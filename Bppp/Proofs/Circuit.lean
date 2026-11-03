import Bppp.Proofs.CircuitPoly
import Bppp.Proofs.NormLinear

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

include hv in
/-- **Completeness of the range circuit.** For honest inputs in range, generators of the right
shape whose `G` and `H_0` are the Pedersen bases, and a transcript whose challenges are never
`-j` for `j < 16`, `verify` accepts what `prove` outputs. -/
theorem completeness (Gp Hp : E) (gens : Generators E) (t : BpppTranscript F E)
    (hh : gens.h_vec.length = H_LEN) (hg : gens.g_vec.length = params.nm)
    (hgH : gens.g = Hp) (hhG : gens.h_vec.getD 0 0 = Gp)
    (hlen : values.length = params.m) (hb : blindings.length = params.m)
    (hrange : ∀ v ∈ values, params.range.is_in_range v) (hd : ∀ v ∈ values, v < 16 ^ params.d)
    (horacle : ∀ log, ∀ j : ℕ, j < 16 → t.oracle log + j ≠ 0) :
    ∃ proof vcs t', (prove Gp Hp gens params rng values blindings).run t = .ok ((proof, vcs), t') ∧
      (verify gens params proof vcs).run t = .ok ((), t') := by
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
  simp only [hsolve, hcs, run_liftM_ok, ok_bind, extend_oracle, extend_log, run_append_point]
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
    sorry
  obtain ⟨nl, t', hnlp, hnlv⟩ := NormLinear.completeness gens T c_tau rho l_tau n_tau ps_tau pn_tau
    extra (by simp [c_tau, hh]) (by simp [l_tau, hh]) (by simp [n_tau, hg]) (by simp [pn_tau, hg])
    (by rw [hh]; decide) hrho0 hident
  refine ⟨⟨c_l, c_o, c_r, c_s, nl⟩, vcs, t', ?_, ?_⟩
  · rw [hnlp]; rfl
  · have hvcs_len : vcs.length = params.m := by simp [vcs, length_to_scalars, hlen, hb]
    have hver : ¬(vcs.length ≠ params.m ∨ gens.g_vec.length ≠ params.nm) := by simp [hvcs_len, hg]
    have htinv : inverse tau = .ok tau⁻¹ := by simp [inverse, htau0]
    simp only [verify, hver, if_false, StateT.run_bind, StateT.run_pure, pure_bind, run_domain_sep,
      ok_bind, run_append_commits, run_append_point, run_challenge_scalar, extend_extend,
      extend_oracle, extend_log, run_liftM_ok]
    rw [hL2, hL1] at htau hT
    rw [hL1] at hrho hlam hbeta hdelta
    simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append,
      extend_extend] at hα hrho hlam hbeta hdelta htau hT ⊢
    rw [hα, hrho, hlam, hbeta, hdelta, hdinv]
    simp only [run_liftM_ok, ok_bind, extend_extend, extend_oracle, extend_log,
      List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
    rw [htau, htinv, hCnew]
    simp only [run_liftM_ok, ok_bind, hev hpnu, hev hcu]
    rw [← hT]
    exact hnlv

end Circuit

end Bppp
