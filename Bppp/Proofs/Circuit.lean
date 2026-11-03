import Bppp.Proofs.CircuitPoly
import Bppp.Proofs.NormLinear
import Bppp.Spec.Commitment

/-!
# Completeness of `circuit.rs`
-/

open Finset

namespace Bppp

variable {F E : Type} [Field F] [DecidableEq F] [AddCommGroup E] [Module F E] [DecidableEq E]

set_option linter.unusedSectionVars false

namespace Circuit

/-- `Generators::commit`, for vectors of the generators' lengths. -/
theorem gens_commit_eq (gens : Generators E) (sigma : F) (l n : List F)
    (hl : l.length = gens.h_vec.length) (hn : n.length = gens.g_vec.length) :
    gens.commit sigma l n = .ok (sigma • gens.g + (List.zipWith (· • ·) l gens.h_vec).sum +
      (List.zipWith (· • ·) n gens.g_vec).sum) := by
  simp only [Generators.commit, Generators.msm, mixed_multi_scalar_mul]
  rw [if_neg (by simp [hl, hn])]
  simp only [List.cons_append, List.zipWith_cons_cons, List.zipWith_append hl, List.sum_cons,
    List.sum_append, List.zipWith_nil_left, List.sum_nil, add_zero, add_assoc]

/-- An MSM over a list, as `Spec.NormLinear.msm` over its entries. -/
theorem sum_zipWith_msm (a : List F) (P : List E) {L : ℕ} (ha : a.length = L) (hP : P.length = L) :
    (List.zipWith (· • ·) a P).sum =
      Spec.NormLinear.msm L (fun k => a.getD k 0) (fun k => P.getD k 0) := by
  rw [sum_zipWith _ _ _ 0 0, ha, hP, min_self]; rfl

theorem input_commitments_eq (params : CircuitParams) (rng : Randomness F) (values : List ℕ)
    (blindings : List F) (G H : E) (gens : Generators E) :
    (Witness.new params rng values blindings : Witness F).input_commitments G H gens =
      .ok ((List.zip (to_scalars values : List F) blindings).map fun (v, s) =>
        PedersenCommitment.new G H v s) := by
  simp only [Witness.input_commitments, Witness.new]
  generalize List.zip (to_scalars values : List F) blindings = L
  suffices ∀ k, (L.zipIdx k).mapM (fun x => (match ([] : List (List F × F))[x.2]? with
      | some (n, l) => do
        let p ← multi_scalar_mul (n ++ [l]) (gens.g_vec ++ [gens.h_vec.getD (H_LEN - 1) 0])
        pure (⟨(PedersenCommitment.new G H x.1.1 x.1.2).point + p⟩ : PedersenCommitment E)
      | none => pure (PedersenCommitment.new G H x.1.1 x.1.2) : Result (PedersenCommitment E))) =
      .ok (L.map fun (v, s) => PedersenCommitment.new G H v s) from this 0
  intro k
  induction L generalizing k with
  | nil => rfl
  | cons x L ih =>
    rw [List.zipIdx_cons, List.mapM_cons, ih]
    simp [pure, Except.pure, bind, Except.bind]

variable (params : CircuitParams) (hv : params.Valid) (rng : Randomness F) (values : List ℕ)
  (blindings : List F)

theorem dig_lt (k : ℕ) : (specHonest rng values blindings).dig (params.toSpec hv) k < 16 :=
  Spec.dig_lt (P := params.toSpec hv) (h := specHonest rng values blindings)
    (digits_lt params rng values blindings) k

/-- `reciprocals` inverts `α + d_k`. -/
theorem reciprocals_eq (hlen : values.length = params.m) (alpha : F)
    (halpha : ∀ j : ℕ, j < 16 → alpha + j ≠ 0) (rho lambda beta delta : F) (r : ℕ → F) :
    ∃ n_r, reciprocals params (Witness.new params rng values blindings : Witness F).n_l alpha =
      .ok n_r ∧ n_r.length = params.nm ∧ ∀ k, n_r.getD k 0 =
        (specOpening params hv rng values blindings alpha rho lambda beta delta r).nR k := by
  set W : Witness F := Witness.new params rng values blindings
  have hnl : W.n_l.length = params.nm := by simp [W, Witness.new, length_pad_to]
  have hden : ∀ x ∈ (W.n_l.take params.n_d).map (alpha + ·), x ≠ 0 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    rw [List.getElem_take, getElem_eq_getD' _ _ 0, getD_n_l params hv rng values blindings hlen]
    exact halpha _ (dig_lt params hv rng values blindings k)
  refine ⟨pad_to (((W.n_l.take params.n_d).map (alpha + ·)).map (·⁻¹)) params.nm,
    by simp only [reciprocals, batch_invert_eq _ hden, bind, Except.bind, pure, Except.pure],
    length_pad_to _ _, fun k => ?_⟩
  rw [getD_pad_to]
  simp only [specOpening, Spec.Honest.opening, specCh, CircuitParams.Nd_toSpec]
  have hnd := hv.le
  split_ifs with h1 h2 h2
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map, List.getElem?_take,
      if_pos h2, List.getElem?_eq_getElem (by omega)]
    simp only [Option.map_some, Option.getD_some]
    rw [getElem_eq_getD' _ _ 0, getD_n_l params hv rng values blindings hlen k]
  · rw [getD_eq_zero_of_le (by simp; omega)]
  · omega
  · rfl

open BpppTranscript NormLinear

theorem spec_commit_congr (P : Spec.Params) (g : E) (H G : ℕ → E) (σ : F) {ℓ ℓ' n n' : ℕ → F}
    (hℓ : ∀ s < 8, ℓ s = ℓ' s) (hn : ∀ k < P.nm, n k = n' k) :
    Spec.commit P g H G σ ℓ n = Spec.commit P g H G σ ℓ' n' := by
  simp only [Spec.commit, Spec.NormLinear.msm]
  have h1 : ∑ s ∈ range 8, ℓ s • H s = ∑ s ∈ range 8, ℓ' s • H s :=
    sum_congr rfl fun s hs => by rw [hℓ s (mem_range.1 hs)]
  have h2 : ∑ k ∈ range P.nm, n k • G k = ∑ k ∈ range P.nm, n' k • G k :=
    sum_congr rfl fun k hk => by rw [hn k (mem_range.1 hk)]
  rw [h1, h2]

theorem sum_zipIdx_map {α : Type} (L : List α) (d : α) (f : ℕ → F) (q : α → E) :
    ((L.zipIdx.map fun (v, i) => (f i, q v)).map fun (s, p) => s • p).sum =
      ∑ i ∈ range L.length, f i • q (L.getD i d) := by
  suffices h : ∀ k, (((L.zipIdx k).map fun (v, i) => (f i, q v)).map fun (s, p) => s • p).sum =
      ∑ i ∈ range L.length, f (k + i) • q (L.getD i d) by simpa using h 0
  induction L with
  | nil => simp
  | cons x L ih =>
    intro k
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, List.sum_cons, ih, List.length_cons,
      sum_range_succ']
    simp only [add_zero, List.getD_cons_zero, List.getD_cons_succ]
    rw [add_comm]
    congr 1
    exact sum_congr rfl fun i _ => by rw [show k + 1 + i = k + (i + 1) by ring]

/-- The verifier's `p_s(τ)`, from `p_n(τ)`, is `p_s` of `Spec` at `τ`. -/
theorem ps_eq (alpha rho lambda beta delta : F) (C : Constraints F)
    (hC : Constraints.Correct params alpha (rho * rho) lambda C hv) (τ : Fˣ) :
    weighted_norm ((List.range params.nm).map fun k => evalAt τ ((C.p_n delta⁻¹).toPolys k))
        (rho * rho) + C.p_s_constant * ((τ : F) * τ * τ) =
      evalAt τ (Spec.ps (params.toSpec hv) (specCh alpha rho lambda beta delta)) := by
  rw [weighted_norm_eq, List.length_map, List.length_range]
  simp only [Spec.ps, Spec.normμ, map_add, map_sum, map_mul, evalAt_mono, Constraints.p_s_constant,
    hC.lambda_al, hC.mu_am, CircuitParams.nm_toSpec, zpow_ofNat]
  have h : ∀ k ∈ range params.nm, ((List.range params.nm).map fun k =>
      evalAt τ ((C.p_n delta⁻¹).toPolys k)).getD k 0 =
      evalAt τ (Spec.pn (params.toSpec hv) (specCh alpha rho lambda beta delta) k) := fun k hk => by
    rw [getD_map_range _ (mem_range.1 hk),
      toPolys_p_n params hv alpha rho lambda beta delta C hC k (mem_range.1 hk)]
  rw [sum_congr rfl fun k hk => by rw [h k hk]]
  have hlam : Spec.lamAl (params.toSpec hv) (Constraints.challenges alpha (rho * rho) lambda 0 0) =
      Spec.lamAl (params.toSpec hv) (specCh alpha rho lambda beta delta) := rfl
  have hmu : Spec.muAm (params.toSpec hv) (Constraints.challenges alpha (rho * rho) lambda 0 0) =
      Spec.muAm (params.toSpec hv) (specCh alpha rho lambda beta delta) := rfl
  rw [hlam, hmu]
  simp only [specCh, pow_zero, mul_one]
  congr 1
  · exact sum_congr rfl fun k _ => by ring
  · ring

/-- `<p_n(τ), G_vec>`. -/
theorem pn_msm_eq (gens : Generators E) (hg : gens.g_vec.length = params.nm)
    (alpha rho lambda beta delta : F) (C : Constraints F)
    (hC : Constraints.Correct params alpha (rho * rho) lambda C hv) (τ : Fˣ) :
    (List.zipWith (· • ·) ((List.range params.nm).map fun k => evalAt τ ((C.p_n delta⁻¹).toPolys k))
        gens.g_vec).sum =
      Spec.NormLinear.msm params.nm
        (fun k => evalAt τ (Spec.pn (params.toSpec hv) (specCh alpha rho lambda beta delta) k))
        (fun k => gens.g_vec.getD k 0) := by
  rw [sum_zipWith_msm _ gens.g_vec (by simp) hg]
  exact sum_congr rfl fun k hk => by
    simp only []
    rw [getD_map_range _ (mem_range.1 hk),
      toPolys_p_n params hv alpha rho lambda beta delta C hC k (mem_range.1 hk)]

/-- The verifier's decomposed `C(τ)` (25). -/
theorem combined_assembly (P : Spec.Params) (g : E) (G : ℕ → E) (ch : Spec.Challenges F) (τ : Fˣ)
    (cS cO cL cR : E) (V : ℕ → E) :
    evalAt τ (Spec.ps P ch) • g + Spec.NormLinear.msm P.nm (fun k => evalAt τ (Spec.pn P ch k)) G +
      ((τ : F)⁻¹ • cS + ch.δ • cO + (τ : F) • cL + ((τ : F) * τ) • cR +
        ∑ i ∈ range P.M, (2 * ((τ : F) * τ * τ) * ch.lam ^ i) • V i) =
    Spec.combined P g G ch τ cS cO cL cR (Spec.vHat P ch V) := by
  simp only [Spec.combined, Spec.vHat, smul_sum, smul_smul, zpow_neg_one]
  rw [sum_congr rfl fun i _ => by
    rw [show 2 * ((τ : F) * τ * τ) * ch.lam ^ i = (τ : F) ^ 3 * (2 * ch.lam ^ i) by ring], sq]
  abel

/-- A circuit commitment as `Spec.commit`. -/
theorem commit_spec (gens : Generators E) (hh : gens.h_vec.length = H_LEN)
    (hg : gens.g_vec.length = params.nm) (sigma : F) (l n : List F) (hl : l.length = H_LEN)
    (hn : n.length = params.nm) :
    sigma • gens.g + (List.zipWith (· • ·) l gens.h_vec).sum + (List.zipWith (· • ·) n gens.g_vec).sum =
      Spec.commit (params.toSpec hv) gens.g (fun k => gens.h_vec.getD k 0)
        (fun k => gens.g_vec.getD k 0) sigma (fun k => l.getD k 0) (fun k => n.getD k 0) := by
  rw [sum_zipWith_msm l gens.h_vec hl hh, sum_zipWith_msm n gens.g_vec hn hg]; rfl

include hv in
set_option maxHeartbeats 1000000 in
/-- **Completeness of the range circuit.** For honest inputs in range, generators of the right
shape whose `G` and `H_0` are the Pedersen bases, and a transcript whose challenges are never
`-j` for `j < 16`, `verify` accepts what `prove` outputs. -/
theorem completeness (Gp Hp : E) (gens : Generators E) (t : BpppTranscript F E)
    (hh : gens.h_vec.length = H_LEN) (hg : gens.g_vec.length = params.nm)
    (hgH : gens.g = Hp) (hhG : gens.h_vec.getD 0 0 = Gp)
    (hlen : values.length = params.m) (hb : blindings.length = params.m)
    (hrange : ∀ v ∈ values, params.range.is_in_range v) (hd : ∀ v ∈ values, v < 16 ^ params.d)
    (horacle : ∀ log, ∀ j : ℕ, j < 16 → t.oracle log + j ≠ 0) :
    ∃ proof t', (prove Gp Hp gens params rng values blindings).run t =
        .ok ((proof, (List.zip (to_scalars values : List F) blindings).map fun (v, s) =>
          PedersenCommitment.new Gp Hp v s), t') ∧
      (verify gens params proof ((List.zip (to_scalars values : List F) blindings).map fun (v, s) =>
          PedersenCommitment.new Gp Hp v s)).run t = .ok ((), t') := by
  have hprove : ¬(values.length ≠ params.m ∨ blindings.length ≠ params.m ∨
      gens.g_vec.length ≠ params.nm ∨ values.any (fun v => !params.range.is_in_range v)) := by
    simp [hlen, hb, hg]
    intro v hv; simpa using hrange v hv
  simp only [prove, hprove, if_false, prove_witness, StateT.run_bind]
  rw [input_commitments_eq]
  set vcs := (List.zip (to_scalars values : List F) blindings).map fun (v, s) =>
    PedersenCommitment.new Gp Hp v s with hvcs
  set W : Witness F := Witness.new params rng values blindings with hW
  have hrl : W.r_l.length = H_LEN := length_blinding_vector _ _
  have hro : W.r_o.length = H_LEN := length_blinding_vector _ _
  have hrr : W.r_r.length = H_LEN := length_blinding_vector _ _
  have hnl : W.n_l.length = params.nm := length_pad_to _ _
  have hno : W.n_o.length = params.nm := length_pad_to _ _
  have hns : W.n_s.length = params.nm := by simp [W, Witness.new]
  obtain ⟨c_l, hcl⟩ : ∃ c_l, commit gens W.r_l W.n_l = .ok c_l :=
    ⟨_, gens_commit_eq gens _ _ _ (by rw [length_h_coordinates hrl, hh]) (by rw [hnl, hg])⟩
  obtain ⟨c_o, hco⟩ : ∃ c_o, commit gens W.r_o W.n_o = .ok c_o :=
    ⟨_, gens_commit_eq gens _ _ _ (by rw [length_h_coordinates hro, hh]) (by rw [hno, hg])⟩
  simp only [StateT.run_pure, pure_bind, run_liftM_ok, ok_bind,
    run_domain_sep, run_append_commits, hcl, hco, run_append_point, run_challenge_scalar,
    extend_extend, extend_oracle, extend_log]
  generalize hα : t.oracle (t.log ++ [Entry.message "dom-sep" (List.map Char.toNat "bppp_circuit".toList)] ++
    List.map (fun c => Entry.point "V" c.point) vcs ++ [Entry.point "C_L" c_l] ++
    [Entry.point "C_O" c_o] ++ [Entry.challenge "alpha"]) = alpha
  have halpha : ∀ j : ℕ, j < 16 → alpha + j ≠ 0 := fun j hj => hα ▸ horacle _ j hj
  obtain ⟨n_r, hnr_eq, hnr_len, hnr⟩ := reciprocals_eq params hv rng values blindings hlen alpha
    halpha 0 0 0 0 0
  rw [← hW] at hnr_eq
  obtain ⟨c_r, hcr⟩ : ∃ c_r, commit gens W.r_r n_r = .ok c_r :=
    ⟨_, gens_commit_eq gens _ _ _ (by rw [length_h_coordinates hrr, hh]) (by rw [hnr_len, hg])⟩
  simp only [hnr_eq, hcr, run_liftM_ok, ok_bind, extend_oracle, extend_log]
  set L1 : List (Entry F E) := [Entry.message "dom-sep" (List.map Char.toNat "bppp_circuit".toList)] ++
    (List.map (fun c => Entry.point "V" c.point) vcs ++
      ([Entry.point "C_L" c_l] ++ ([Entry.point "C_O" c_o] ++ [Entry.challenge "alpha"]))) with hL1
  generalize hrho : t.oracle (t.log ++ L1 ++ [Entry.point "C_R" c_r] ++ [Entry.challenge "rho"]) = rho
  generalize hlam : t.oracle (t.log ++ L1 ++ [Entry.point "C_R" c_r] ++ [Entry.challenge "rho"] ++
    [Entry.challenge "lambda"]) = lambda
  generalize hbeta : t.oracle (t.log ++ L1 ++ [Entry.point "C_R" c_r] ++ [Entry.challenge "rho"] ++
    [Entry.challenge "lambda"] ++ [Entry.challenge "beta"]) = beta
  generalize hdelta : t.oracle (t.log ++ L1 ++ [Entry.point "C_R" c_r] ++ [Entry.challenge "rho"] ++
    [Entry.challenge "lambda"] ++ [Entry.challenge "beta"] ++ [Entry.challenge "delta"]) = delta
  have hne : ∀ (l : List (Entry F E)) (x : F), t.oracle l = x → x ≠ 0 := fun l x h => by
    have := horacle l 0 (by norm_num); rw [h] at this; simpa using this
  have hrho0 : rho ≠ 0 := hne _ _ hrho
  have hbeta0 : beta ≠ 0 := hne _ _ hbeta
  have hdelta0 : delta ≠ 0 := hne _ _ hdelta
  have hdinv : inverse delta = .ok delta⁻¹ := by simp [inverse, hdelta0]
  obtain ⟨C, hCnew, hC⟩ := Constraints.new_correct params alpha (rho * rho) lambda hv
    (mul_ne_zero hrho0 hrho0) halpha
  simp only [hdinv, hCnew, run_liftM_ok, ok_bind]
  have hrest := rest_eq params hv rng values blindings alpha rho lambda beta delta C hC n_r hlen hb hd
    hnr_len (fun k => hnr k)
  obtain ⟨g_s, h_s, hsolve, hhs_len, hhs7, hrS⟩ := solve_r_s_eq params hv rng values blindings alpha
    rho lambda beta delta C hC _ hbeta0 hrest
  rw [← hW] at hsolve
  obtain ⟨c_s, hcs⟩ : ∃ c_s, gens.commit g_s h_s W.n_s = .ok c_s :=
    ⟨_, gens_commit_eq gens _ _ _ (by rw [hhs_len, hh]) (by rw [hns, hg])⟩
  rw [show W.l_s = rng.l_s from rfl]
  simp only [hsolve, hcs, run_liftM_ok, ok_bind, extend_oracle, extend_log]
  set L2 : List (Entry F E) := [Entry.point "C_R" c_r] ++ ([Entry.challenge "rho"] ++
    ([Entry.challenge "lambda"] ++ ([Entry.challenge "beta"] ++ [Entry.challenge "delta"])))
    with hL2
  generalize htau : t.oracle (t.log ++ L1 ++ L2 ++ [Entry.point "C_S" c_s] ++
    [Entry.challenge "tau"]) = tau
  have htau0 : tau ≠ 0 := hne _ _ htau
  set τu : Fˣ := Units.mk0 tau htau0
  set T : BpppTranscript F E := ((t.extend L1).extend L2).extend
    ([Entry.point "C_S" c_s] ++ [Entry.challenge "tau"]) with hT
  -- The evaluations.
  obtain ⟨hcu, hcp⟩ := c_spec params hv alpha rho lambda beta delta C hC
  obtain ⟨hlu, hlp⟩ := l_base params hv rng values blindings alpha rho lambda beta delta C hC
    (rSOf g_s h_s) n_r hb
  obtain ⟨hnu, hnp⟩ := n_spec params hv rng values blindings alpha rho lambda beta delta C hC
    (rSOf g_s h_s) n_r hlen hnr_len (fun k => hnr k)
  rw [← hW] at hlu hlp hnu hnp
  have hlu' := Laurent.uniform_add hlu (Laurent.uniform_monomial (-1) hhs_len)
  have hev : ∀ {L : ℕ} {P : Laurent (List F)}, Laurent.Uniform L P →
      P.eval tau = .ok ((List.range L).map fun k => evalAt τu (P.toPolys k)) :=
    fun hP => Laurent.eval_eq hP τu
  simp only [hev hcu, hev hlu', hev hnu, run_liftM_ok, ok_bind]
  have hpnu := uniform_p_n params hv alpha rho lambda delta C hC
  set c_tau := (List.range H_LEN).map fun k => evalAt τu ((Circuit.c C beta).toPolys k)
  set l_tau := (List.range H_LEN).map fun k =>
    evalAt τu (((coordinates_without_c_s params C W n_r delta delta⁻¹).2.1 +
      Laurent.monomial (-1) h_s).toPolys k)
  set n_tau := (List.range params.nm).map fun k =>
    evalAt τu ((coordinates_without_c_s params C W n_r delta delta⁻¹).2.2.toPolys k)
  set pn_tau := (List.range params.nm).map fun k => evalAt τu ((C.p_n delta⁻¹).toPolys k)
  set ps_tau := weighted_norm pn_tau (rho * rho) + C.p_s_constant * (tau * tau * tau)
  set extra := [(tau⁻¹, c_s), (delta, c_o), (tau, c_l), (tau * tau, c_r)] ++
    vcs.zipIdx.map fun (v_i, i) => (2 * (tau * tau * tau) * C.input_weights.getD i 0, v_i.point)
  have hident : ps_tau • gens.g + (List.zipWith (· • ·) pn_tau gens.g_vec).sum +
      (extra.map fun (s, p) => s • p).sum =
      (inner_product c_tau l_tau + weighted_norm n_tau (rho * rho)) • gens.g +
        (List.zipWith (· • ·) l_tau gens.h_vec).sum + (List.zipWith (· • ·) n_tau gens.g_vec).sum := by
    set w := specOpening params hv rng values blindings alpha rho lambda beta delta (rSOf g_s h_s)
      with hw
    set Hf : ℕ → E := fun k => gens.h_vec.getD k 0 with hHf
    set Gf : ℕ → E := fun k => gens.g_vec.getD k 0 with hGf
    -- The four messages are the commitments of `Spec`.
    have ecl : c_l = Spec.cL (params.toSpec hv) gens.g Hf Gf w := by
      have e := Except.ok.inj ((gens_commit_eq gens _ _ _ (by rw [length_h_coordinates hrl, hh])
        (by rw [hnl, hg])).symm.trans hcl)
      rw [← e, commit_spec params hv gens hh hg _ _ _ (length_h_coordinates hrl) hnl, headD_eq_getD]
      exact spec_commit_congr _ _ _ _ _ (fun s _ => getD_h_coordinates hrl s)
        (fun k _ => getD_n_l params hv rng values blindings hlen k)
    have eco : c_o = Spec.cO (params.toSpec hv) gens.g Hf Gf w := by
      have e := Except.ok.inj ((gens_commit_eq gens _ _ _ (by rw [length_h_coordinates hro, hh])
        (by rw [hno, hg])).symm.trans hco)
      rw [← e, commit_spec params hv gens hh hg _ _ _ (length_h_coordinates hro) hno, headD_eq_getD]
      exact spec_commit_congr _ _ _ _ _ (fun s _ => getD_h_coordinates hro s)
        (fun k _ => getD_n_o params hv rng values blindings hlen k)
    have ecr : c_r = Spec.cR (params.toSpec hv) gens.g Hf Gf w := by
      have e := Except.ok.inj ((gens_commit_eq gens _ _ _ (by rw [length_h_coordinates hrr, hh])
        (by rw [hnr_len, hg])).symm.trans hcr)
      rw [← e, commit_spec params hv gens hh hg _ _ _ (length_h_coordinates hrr) hnr_len,
        headD_eq_getD]
      exact spec_commit_congr _ _ _ _ _ (fun s _ => getD_h_coordinates hrr s) (fun k _ => hnr k)
    have ecs : c_s = Spec.cS (params.toSpec hv) gens.g Hf Gf w := by
      have e := Except.ok.inj ((gens_commit_eq gens _ _ _ (by rw [hhs_len, hh])
        (by rw [hns, hg])).symm.trans hcs)
      rw [← e, commit_spec params hv gens hh hg _ _ _ hhs_len hns]
      refine spec_commit_congr _ _ _ _ _ (fun s hs => ?_) (fun k hk => ?_)
      · simp only [w, Spec.Honest.opening, Spec.lin, rSOf, specHonest]
        rcases (show s < 7 ∨ s = 7 by omega) with h7 | rfl
        · rw [if_pos h7, if_neg (by omega), Nat.add_sub_cancel]
        · rw [if_neg (by omega), hhs7]
      · simp only [w, Spec.Honest.opening, specHonest, W, Witness.new]
        exact getD_map_range _ (by simpa using hk)
    -- The inputs.
    have hvcs_len : vcs.length = params.m := by simp [vcs, length_to_scalars, hlen, hb]
    have evcs : ∀ i < params.m, (vcs.getD i ⟨0⟩).point =
        Spec.Honest.inputs (P := params.toSpec hv) gens.g Hf (specHonest rng values blindings) i := by
      intro i hi
      have hi1 : i < (List.zip (to_scalars values : List F) blindings).length := by
        simp [length_to_scalars, hlen, hb, hi]
      rw [← getElem_eq_getD' vcs (by rw [hvcs_len]; exact hi), List.getElem_map, List.getElem_zip]
      simp only [PedersenCommitment.new, Spec.Honest.inputs, hHf, hgH, hhG]
      rw [getElem_eq_getD' _ _ 0, getD_to_scalars,
        value_eq params hv rng values blindings hd i (by rw [hlen]; exact hi),
        getElem_eq_getD' _ _ 0]
      rfl
    have hiw : ∀ i < params.m, C.input_weights.getD i 0 = lambda ^ i := fun i hi => by
      rw [input_weights_eq params hv alpha rho lambda C hC, getD_map_range _ hi]
    have hextra : (extra.map fun (s, p) => s • p).sum = tau⁻¹ • c_s + delta • c_o + tau • c_l +
        (tau * tau) • c_r + ∑ i ∈ range params.m, (2 * (tau * tau * tau) * lambda ^ i) •
          Spec.Honest.inputs (P := params.toSpec hv) gens.g Hf (specHonest rng values blindings) i := by
      simp only [extra, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      have hz := sum_zipIdx_map vcs ⟨0⟩ (fun i => 2 * (tau * tau * tau) * C.input_weights.getD i 0)
        (fun v => v.point)
      simp only at hz
      rw [hz, hvcs_len]
      rw [sum_congr rfl fun i hi => by rw [hiw i (mem_range.1 hi), evcs i (mem_range.1 hi)]]
      abel
    have hLHS : ps_tau • gens.g + (List.zipWith (· • ·) pn_tau gens.g_vec).sum +
        (extra.map fun (s, p) => s • p).sum = Spec.combined (params.toSpec hv) gens.g Gf
          (specCh alpha rho lambda beta delta) τu (Spec.cS (params.toSpec hv) gens.g Hf Gf w)
          (Spec.cO (params.toSpec hv) gens.g Hf Gf w) (Spec.cL (params.toSpec hv) gens.g Hf Gf w)
          (Spec.cR (params.toSpec hv) gens.g Hf Gf w) (Spec.vHat (params.toSpec hv)
            (specCh alpha rho lambda beta delta)
            (Spec.Honest.inputs (P := params.toSpec hv) gens.g Hf (specHonest rng values blindings))) := by
      have hA := combined_assembly (params.toSpec hv) gens.g Gf (specCh alpha rho lambda beta delta) τu
        c_s c_o c_l c_r
        (Spec.Honest.inputs (P := params.toSpec hv) gens.g Hf (specHonest rng values blindings))
      have e1 : ps_tau = evalAt τu (Spec.ps (params.toSpec hv) (specCh alpha rho lambda beta delta)) :=
        ps_eq params hv alpha rho lambda beta delta C hC τu
      have e2 : (List.zipWith (· • ·) pn_tau gens.g_vec).sum = Spec.NormLinear.msm
          (params.toSpec hv).nm
          (fun k => evalAt τu (Spec.pn (params.toSpec hv) (specCh alpha rho lambda beta delta) k)) Gf :=
        pn_msm_eq params hv gens hg alpha rho lambda beta delta C hC τu
      rw [← ecs, ← eco, ← ecl, ← ecr, ← hA, hextra, e1, e2]
      rfl
    -- The evaluated opening.
    have hl_getD : ∀ s < H_LEN, l_tau.getD s 0 =
        evalAt τu (Spec.ℓ (specCh alpha rho lambda beta delta) w s) := fun s hs => by
      rw [getD_map_range _ hs, Laurent.toPolys_add hlu (Laurent.uniform_monomial (-1) hhs_len),
        Laurent.toPolys_monomial, hlp s hs]
      have key : (if s < 7 then rSOf g_s h_s (s + 1) else rng.l_s) = h_s.getD s 0 := by
        simp only [H_LEN] at hs
        rcases (show s < 7 ∨ s = 7 by omega) with h7 | rfl
        · rw [if_pos h7]; simp only [rSOf, if_neg (by omega : s + 1 ≠ 0), Nat.add_sub_cancel]
        · rw [if_neg (by omega), hhs7]
      rw [key, sub_add_cancel]
    have hn_getD : ∀ k < params.nm, n_tau.getD k 0 =
        evalAt τu (Spec.n (params.toSpec hv) (specCh alpha rho lambda beta delta) w k) :=
      fun k hk => by rw [getD_map_range _ hk, hnp k hk]
    have hc_getD : ∀ s < H_LEN, c_tau.getD s 0 =
        evalAt τu (Spec.c (params.toSpec hv) (specCh alpha rho lambda beta delta) s) :=
      fun s hs => by rw [getD_map_range _ hs, hcp s hs]
    have hrel := relation_of_f_zero (params.toSpec hv) (specCh alpha rho lambda beta delta) w
      (f_zero params hv rng values blindings alpha rho lambda beta delta halpha hbeta0 hdelta0 hrho0
        g_s h_s hrS) τu
    have hσ : inner_product c_tau l_tau + weighted_norm n_tau (rho * rho) =
        evalAt τu (Spec.σ (params.toSpec hv) (specCh alpha rho lambda beta delta) w) := by
      rw [hrel, inner_product_eq, weighted_norm_eq]
      have hcl8 : c_tau.length = 8 := by simp [c_tau, H_LEN]
      have hll8 : l_tau.length = 8 := by simp [l_tau, H_LEN]
      have hnl : n_tau.length = params.nm := by simp [n_tau]
      rw [hcl8, hll8, hnl, min_self, CircuitParams.nm_toSpec]
      have s1 : ∑ s ∈ range 8, c_tau.getD s 0 * l_tau.getD s 0 = ∑ s ∈ range 8,
          evalAt τu (Spec.c (params.toSpec hv) (specCh alpha rho lambda beta delta) s) *
            evalAt τu (Spec.ℓ (specCh alpha rho lambda beta delta) w s) :=
        sum_congr rfl fun s hs => by
          rw [hc_getD s (by simpa [H_LEN] using hs), hl_getD s (by simpa [H_LEN] using hs)]
      have s2 : ∑ k ∈ range params.nm, n_tau.getD k 0 * n_tau.getD k 0 * (rho * rho) ^ (k + 1) =
          ∑ k ∈ range params.nm, (specCh alpha rho lambda beta delta).μ ^ (k + 1) *
            (evalAt τu (Spec.n (params.toSpec hv) (specCh alpha rho lambda beta delta) w k) *
              evalAt τu (Spec.n (params.toSpec hv) (specCh alpha rho lambda beta delta) w k)) :=
        sum_congr rfl fun k hk => by rw [hn_getD k (mem_range.1 hk)]; simp only [specCh]; ring
      rw [s1, s2]
    rw [hLHS, Spec.vHat_honest (params.toSpec hv) gens.g Hf Gf (specCh alpha rho lambda beta delta)
      (specHonest rng values blindings) (rSOf g_s h_s)]
    rw [show Spec.Honest.opening (params.toSpec hv) (specCh alpha rho lambda beta delta)
      (specHonest rng values blindings) (rSOf g_s h_s) = w from rfl, Spec.combined_eq,
      commit_spec params hv gens hh hg _ _ _ (by simp [l_tau]) (by simp [n_tau]), hσ]
    exact spec_commit_congr _ _ _ _ _ (fun s hs => (hl_getD s (by simpa [H_LEN] using hs)).symm)
      (fun k hk => (hn_getD k hk).symm)
  obtain ⟨nl, t', hnlp, hnlv⟩ := NormLinear.completeness gens T c_tau rho l_tau n_tau ps_tau pn_tau
    extra (by simp [c_tau, hh]) (by simp [l_tau, hh]) (by simp [n_tau, hg]) (by simp [pn_tau, hg])
    (by rw [hh]; decide) hrho0 hident
  refine ⟨⟨c_l, c_o, c_r, c_s, nl⟩, t', ?_, ?_⟩
  · rw [hnlp]; rfl
  · have hvcs_len : vcs.length = params.m := by simp [vcs, length_to_scalars, hlen, hb]
    have hver : ¬(vcs.length ≠ params.m ∨ gens.g_vec.length ≠ params.nm) := by simp [hvcs_len, hg]
    have htinv : inverse tau = .ok tau⁻¹ := by simp [inverse, htau0]
    simp only [verify, hver, if_false, StateT.run_bind, pure_bind, run_domain_sep,
      ok_bind, run_append_commits, run_append_point, run_challenge_scalar, extend_extend,
      extend_oracle, extend_log]
    rw [hL2, hL1] at htau hT
    rw [hL1] at hrho hlam hbeta hdelta
    simp only [List.append_assoc, List.cons_append, List.nil_append,
      extend_extend] at hα hrho hlam hbeta hdelta htau hT ⊢
    rw [hα, hrho, hlam, hbeta, hdelta, hdinv]
    simp only [run_liftM_ok, ok_bind, extend_extend, extend_oracle, extend_log,
      List.append_assoc, List.cons_append, List.nil_append]
    rw [htau, htinv, hCnew]
    simp only [run_liftM_ok, ok_bind, hev hpnu, hev hcu]
    rw [← hT]
    exact hnlv

end Circuit

end Bppp
