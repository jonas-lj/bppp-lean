import Bppp.Proofs.LazyBases
import Bppp.Proofs.Transcript

/-!
# Completeness of `norm_linear.rs`

A prover state `(bases, c, rho, l, n)` stands for an instance and witness of `Spec.NormLinear`
(`toInst`, `toWit`). Each round of `prove_rec` sends `Spec.NormLinear.msgX` and `msgR` and folds
as `Spec.NormLinear.foldInst`, so the relation (19) carries over (`Spec.NormLinear.fold_rel`), and
`norm_linear::verify`, which tracks the folds as weights on the original generators, accepts.
-/

open Finset

namespace Bppp

variable {F E : Type} [Field F] [DecidableEq F] [AddCommGroup E] [Module F E] [DecidableEq E]

set_option linter.unusedSectionVars false

namespace NormLinear

open Spec.NormLinear (Rel ip wip half pad ev od)

/-- The instance of `Spec.NormLinear` a prover state stands for, with commitment `C`. -/
def toInst (C : E) (lb : LazyBases F E) (c : List F) (rho : F) (l n : List F) :
    Spec.NormLinear.Instance F E where
  C := C
  c k := c.getD k 0
  H k := lb.cur_h.getD k 0
  G k := lb.cur_g.getD k 0
  Lℓ := l.length
  Ln := n.length
  ρ := rho
  μ := rho * rho

/-- The witness of `Spec.NormLinear` the vectors `l`, `n` stand for. -/
def toWit (l n : List F) : Spec.NormLinear.Witness F := ⟨fun k => l.getD k 0, fun k => n.getD k 0⟩

/-! ## Vectors as functions -/

theorem pad_getD {α : Type} [Zero α] (v : List α) (k : ℕ) :
    pad v.length (fun k => v.getD k 0) k = v.getD k 0 := by
  unfold pad; split_ifs with h
  · rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

theorem ev_getD (v : List F) (j : ℕ) : ev v.length (fun k => v.getD k 0) j = (halves v).1.getD j 0 := by
  rw [ev, pad_getD, (getD_halves v j).1]

theorem od_getD (v : List F) (j : ℕ) : od v.length (fun k => v.getD k 0) j = (halves v).2.getD j 0 := by
  rw [od, pad_getD, (getD_halves v j).2]

theorem ev_getD_pts {Q : List E} {L : ℕ} (h : Q.length = L) (j : ℕ) :
    ev L (fun k => Q.getD k 0) j = Q.getD (2 * j) 0 := by
  rw [ev, ← h, pad_getD]

theorem od_getD_pts {Q : List E} {L : ℕ} (h : Q.length = L) (j : ℕ) :
    od L (fun k => Q.getD k 0) j = Q.getD (2 * j + 1) 0 := by
  rw [od, ← h, pad_getD]

theorem ev_fun {v : List F} {L : ℕ} (h : v.length = L) :
    ev L (fun k => v.getD k 0) = fun j => (halves v).1.getD j 0 := by
  subst h; funext j; exact ev_getD v j

theorem od_fun {v : List F} {L : ℕ} (h : v.length = L) :
    od L (fun k => v.getD k 0) = fun j => (halves v).2.getD j 0 := by
  subst h; funext j; exact od_getD v j

theorem length_halves_fst (v : List F) : (halves v).1.length = half v.length :=
  (halves_length v).1

theorem length_halves_snd (v : List F) : (halves v).2.length = half v.length :=
  (halves_length v).2

theorem inner_product_ip {u v : List F} {N : ℕ} (h : min u.length v.length = N) :
    inner_product u v = ip N (fun k => u.getD k 0) (fun k => v.getD k 0) := by
  rw [inner_product_eq, h, ip]

theorem weighted_inner_product_wip {u v : List F} {N : ℕ} (h : min u.length v.length = N) (mu : F) :
    weighted_inner_product u v mu = wip N mu (fun k => u.getD k 0) (fun k => v.getD k 0) := by
  rw [weighted_inner_product_eq, h, wip]
  exact sum_congr rfl fun k _ => by ring

/-- An MSM over `Q` with coefficients `from_halves a b`, as a sum over the halves. -/
theorem sum_from_halves (a b : List F) (h : a.length = b.length) (Q : List E) :
    ∑ i ∈ range (from_halves a b).length, (from_halves a b).getD i 0 • Q.getD i 0 =
      ∑ j ∈ range a.length, (a.getD j 0 • Q.getD (2 * j) 0 + b.getD j 0 • Q.getD (2 * j + 1) 0) := by
  rw [length_from_halves, h, min_self, ← h, Spec.NormLinear.sum_range_two_mul]
  refine sum_congr rfl fun j _ => ?_
  rw [(getD_from_halves a b h j).1, (getD_from_halves a b h j).2]

/-! ## One round -/

section Round

variable (C : E) (lb : LazyBases F E) (c : List F) (rho : F) (l n : List F)

theorem msm_halves_eq {a b : List F} (hab : a.length = b.length) {v : List F}
    (ha : a.length = half v.length) {Q : List E} (hQ : Q.length = v.length) :
    ∑ i ∈ range (from_halves a b).length, (from_halves a b).getD i 0 • Q.getD i 0 =
      Spec.NormLinear.msm (half v.length) (fun j => a.getD j 0) (ev v.length fun k => Q.getD k 0) +
      Spec.NormLinear.msm (half v.length) (fun j => b.getD j 0) (od v.length fun k => Q.getD k 0) := by
  rw [sum_from_halves a b hab, Spec.NormLinear.msm, Spec.NormLinear.msm, ← sum_add_distrib, ha]
  refine sum_congr rfl fun j _ => ?_
  rw [ev_getD_pts hQ, od_getD_pts hQ]

/-- `prove_rec`'s first message is `Spec.NormLinear.msgX`. -/
theorem x_point_eq (hc : c.length = l.length) (hh : lb.cur_h.length = l.length)
    (hg : lb.cur_g.length = n.length) :
    (2 * rho⁻¹ * weighted_inner_product (halves n).1 (halves n).2 (rho * rho * (rho * rho)) +
        inner_product (halves c).1 (halves l).2 + inner_product (halves c).2 (halves l).1) • lb.g0 +
      ∑ i ∈ range (from_halves (halves l).2 (halves l).1).length,
        (from_halves (halves l).2 (halves l).1).getD i 0 • lb.cur_h.getD i 0 +
      ∑ i ∈ range (from_halves (vec_scalar_mul rho (halves n).2)
          (vec_scalar_mul rho⁻¹ (halves n).1)).length,
        (from_halves (vec_scalar_mul rho (halves n).2) (vec_scalar_mul rho⁻¹ (halves n).1)).getD i 0 •
          lb.cur_g.getD i 0 =
    Spec.NormLinear.msgX lb.g0 (toInst C lb c rho l n) (toWit l n) := by
  have hl1 := length_halves_fst l
  have hl2 := length_halves_snd l
  have hn1 := length_halves_fst n
  have hn2 := length_halves_snd n
  have hc1 := length_halves_fst c
  have hc2 := length_halves_snd c
  rw [msm_halves_eq (by rw [hl1, hl2]) hl2 hh,
    msm_halves_eq (by simp [length_vec_scalar_mul, hn1, hn2])
      (by rw [length_vec_scalar_mul, hn2]) hg]
  rw [weighted_inner_product_wip (by rw [hn1, hn2, min_self]),
    inner_product_ip (by rw [hc1, hl2, hc, min_self]),
    inner_product_ip (by rw [hc2, hl1, hc, min_self]),
    show rho * rho * (rho * rho) = (rho * rho) ^ 2 by ring]
  simp only [Spec.NormLinear.msgX, toInst, toWit, ev_fun hc, od_fun hc, ev_fun rfl, od_fun rfl,
    od_getD, ev_getD, getD_vec_scalar_mul, add_assoc]

/-- `prove_rec`'s second message is `Spec.NormLinear.msgR`. -/
theorem r_point_eq (hc : c.length = l.length) (hh : lb.cur_h.length = l.length)
    (hg : lb.cur_g.length = n.length) :
    (weighted_norm (halves n).2 (rho * rho * (rho * rho)) +
        inner_product (halves c).2 (halves l).2) • lb.g0 +
      ∑ i ∈ range (from_odd_half (halves l).2).length,
        (from_odd_half (halves l).2).getD i 0 • lb.cur_h.getD i 0 +
      ∑ i ∈ range (from_odd_half (halves n).2).length,
        (from_odd_half (halves n).2).getD i 0 • lb.cur_g.getD i 0 =
    Spec.NormLinear.msgR lb.g0 (toInst C lb c rho l n) (toWit l n) := by
  have hl2 := length_halves_snd l
  have hn2 := length_halves_snd n
  have hc2 := length_halves_snd c
  rw [from_odd_half_eq, from_odd_half_eq,
    msm_halves_eq (by simp) (by rw [List.length_replicate, hl2]) hh,
    msm_halves_eq (by simp) (by rw [List.length_replicate, hn2]) hg]
  rw [weighted_norm, weighted_inner_product_wip (by rw [hn2, min_self]),
    inner_product_ip (by rw [hc2, hl2, hc, min_self]),
    show rho * rho * (rho * rho) = (rho * rho) ^ 2 by ring]
  have hz : ∀ (L L' : ℕ) (G : ℕ → E),
      Spec.NormLinear.msm L (fun j => (List.replicate L' (0 : F)).getD j 0) G = 0 := by
    intro L L' G
    refine sum_eq_zero fun j _ => ?_
    show (List.replicate L' (0 : F)).getD j 0 • G j = 0
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> simp
  simp only [Spec.NormLinear.msgR, toInst, toWit, od_fun hc, od_fun rfl, hz, zero_add,
    add_assoc]

theorem getD_fold_vec (a : List F) (gamma : F) (s : F) (j : ℕ) :
    (vec_add (vec_scalar_mul s (halves a).1) (vec_scalar_mul gamma (halves a).2)).getD j 0 =
      s * ev a.length (fun k => a.getD k 0) j + gamma * od a.length (fun k => a.getD k 0) j := by
  rw [getD_vec_add (by simp [length_vec_scalar_mul, length_halves_fst, length_halves_snd]),
    getD_vec_scalar_mul, getD_vec_scalar_mul, ev_getD, od_getD]

theorem vec_scalar_mul_one (a : List F) : vec_scalar_mul 1 a = a := by
  simp [vec_scalar_mul]

theorem length_fold_vec (a : List F) (gamma s : F) :
    (vec_add (vec_scalar_mul s (halves a).1) (vec_scalar_mul gamma (halves a).2)).length =
      half a.length := by
  simp [length_vec_add, length_vec_scalar_mul, length_halves_fst, length_halves_snd]

theorem getD_foldPts_pts (f0 f1 : F) {Q : List E} {L : ℕ} (h : Q.length = L) (i : ℕ) :
    (foldPts f0 f1 Q).getD i 0 =
      f0 • ev L (fun k => Q.getD k 0) i + f1 • od L (fun k => Q.getD k 0) i := by
  rw [getD_foldPts, ev_getD_pts h, od_getD_pts h]
  split_ifs with hi
  · rfl
  · rw [getD_eq_zero_of_le (by omega), getD_eq_zero_of_le (by omega), smul_zero, smul_zero,
      add_zero]

/-- The state after a round stands for `Spec.NormLinear.foldInst` and `foldWit`. -/
theorem fold_toInst (X R : E) (gamma : F) (lb' : LazyBases F E) (hp : lb'.Pos)
    (hc : c.length = l.length) (hh : lb.cur_h.length = l.length) (hg : lb.cur_g.length = n.length)
    (hh' : lb'.cur_h = lb.cur_h) (hg' : lb'.cur_g = lb.cur_g) :
    toInst (C + gamma • X + (gamma ^ 2 - 1) • R) (lb'.fold rho gamma)
        (vec_add (halves c).1 (vec_scalar_mul gamma (halves c).2)) (rho * rho)
        (vec_add (halves l).1 (vec_scalar_mul gamma (halves l).2))
        (vec_add (vec_scalar_mul rho⁻¹ (halves n).1) (vec_scalar_mul gamma (halves n).2)) =
      Spec.NormLinear.foldInst (toInst C lb c rho l n) X R gamma ∧
    toWit (vec_add (halves l).1 (vec_scalar_mul gamma (halves l).2))
        (vec_add (vec_scalar_mul rho⁻¹ (halves n).1) (vec_scalar_mul gamma (halves n).2)) =
      Spec.NormLinear.foldWit (toInst C lb c rho l n) (toWit l n) gamma := by
  have e1 : ∀ a : List F, vec_add (halves a).1 (vec_scalar_mul gamma (halves a).2) =
      vec_add (vec_scalar_mul 1 (halves a).1) (vec_scalar_mul gamma (halves a).2) := fun a => by
    rw [vec_scalar_mul_one]
  rw [e1 c, e1 l]
  constructor
  · simp only [toInst, Spec.NormLinear.foldInst, LazyBases.cur_h_fold _ hp, LazyBases.cur_g_fold _ hp,
      hh', hg', length_fold_vec, Spec.NormLinear.Instance.mk.injEq, true_and]
    refine ⟨funext fun j => ?_, funext fun j => ?_, funext fun j => ?_, by ring⟩
    · rw [getD_fold_vec, one_mul, hc]
    · rw [getD_foldPts_pts _ _ hh, one, one_smul]
    · rw [getD_foldPts_pts _ _ hg]
  · simp only [toWit, Spec.NormLinear.foldWit, toInst, Spec.NormLinear.Witness.mk.injEq]
    exact ⟨funext fun j => by rw [getD_fold_vec, one_mul],
      funext fun j => by rw [getD_fold_vec]⟩

end Round

/-! ## All rounds -/

open BpppTranscript

theorem run_liftM_ok {σ ε α : Type} (a : α) (t : σ) :
    (liftM (Except.ok a : Except ε α) : StateT σ (Except ε) α).run t = .ok (a, t) := rfl

@[simp] theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

/-- The transcript entries of the final opening. -/
def finalEntries (proof : NormLinearProof F E) : List (Entry F E) :=
  .scalar "l_final" proof.l_final :: proof.n_final.map (.scalar "n_final")

theorem proof_shape_step {a b : ℕ} (h : ¬ is_base_case a b) :
    proof_shape a b = ((proof_shape ((a + 1) / 2) ((b + 1) / 2)).1 + 1,
      (proof_shape ((a + 1) / 2) ((b + 1) / 2)).2) := by
  rw [proof_shape, dif_neg h]

/-- `prove_rec` and the round loop of `norm_linear::verify` agree, and the final opening satisfies
the relation on the commitment folded by the rounds, over the bases the verifier's weights give. -/
theorem prove_rec_spec (gens : Generators E) :
    ∀ (N : ℕ) (lb : LazyBases F E) (c : List F) (rho : F) (l n : List F) (C : E)
      (t : BpppTranscript F E) (W_h W_g : Weights F) (gammas : List F),
    l.length + n.length = N → lb.Pos → 0 < W_h.w.length → 0 < W_g.w.length →
    lb.cur_h = contract' W_h.w gens.h_vec → lb.cur_g = contract' W_g.w gens.g_vec →
    lb.g0 = gens.g → c.length = l.length → lb.cur_h.length = l.length →
    lb.cur_g.length = n.length → 0 < l.length → rho ≠ 0 →
    Rel gens.g (toInst C lb c rho l n) (toWit l n) →
    ∃ (proof : NormLinearProof F E) (t' : BpppTranscript F E) (cf : List F) (rhof muf : F)
      (gs : List F) (Wh' Wg' : Weights F),
      (prove_rec lb c rho l n).run t = .ok (proof, t'.extend (finalEntries proof)) ∧
      proof.rounds.length = (proof_shape l.length n.length).1 ∧
      proof.n_final.length = (proof_shape l.length n.length).2 ∧
      (proof.rounds.foldlM verify_round (c, rho, rho * rho, gammas, W_h, W_g)).run t =
        .ok ((cf, rhof, muf, gammas ++ gs, Wh', Wg'), t') ∧
      gs.length = proof.rounds.length ∧ cf.length = 1 ∧ 0 < Wh'.w.length ∧ 0 < Wg'.w.length ∧
      (contract' Wh'.w gens.h_vec).length = 1 ∧
      (contract' Wg'.w gens.g_vec).length = proof.n_final.length ∧
      C + ((List.zip proof.rounds gs).map fun ((X, R), γ) => γ • X + (γ ^ 2 - 1) • R).sum =
        (cf.headD 0 * proof.l_final + weighted_norm proof.n_final muf) • gens.g +
          proof.l_final • (contract' Wh'.w gens.h_vec).getD 0 0 +
          ∑ k ∈ range proof.n_final.length,
            proof.n_final.getD k 0 • (contract' Wg'.w gens.g_vec).getD k 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro lb c rho l n C t W_h W_g gammas hN hp hWh hWg hcur_h hcur_g hg0 hc hh hg hl hrho hrel
  rw [prove_rec]
  by_cases hb : is_base_case l.length n.length
  · -- The opening is sent in the clear.
    have hl1 : l.length = 1 := by
      simp only [is_base_case, Bool.and_eq_true, decide_eq_true_eq] at hb; omega
    obtain ⟨l0, rfl⟩ : ∃ l0, l = [l0] := by
      match l, hl1 with
      | [l0], _ => exact ⟨l0, rfl⟩
    refine ⟨⟨[], l0, n⟩, t, c, rho, rho * rho, [], W_h, W_g, ?_, ?_, ?_, ?_, rfl, ?_, hWh, hWg,
      ?_, ?_, ?_⟩
    · simp only [dif_pos hb, StateT.run_bind, run_append_scalars, ok_bind, StateT.run_pure]
      simp [finalEntries, extend, pure, Except.pure]
    · rw [proof_shape, dif_pos hb]; rfl
    · rw [proof_shape, dif_pos hb]
    · rw [List.append_nil]; rfl
    · rw [hc]; rfl
    · rw [← hcur_h, hh]; rfl
    · rw [← hcur_g, hg]
    · simp only [Spec.NormLinear.Rel, toInst, toWit] at hrel
      rw [List.zip_nil_left, List.map_nil, List.sum_nil, add_zero, hrel, ← hcur_h, ← hcur_g]
      simp only [List.length_singleton, ip, wip, Spec.NormLinear.msm, range_one,
        sum_singleton, List.getD_cons_zero, weighted_norm_eq]
      congr 3
      have hc0 : c.getD 0 0 = c.headD 0 := by cases c <;> rfl
      rw [hc0]
      exact congrArg _ (sum_congr rfl fun k _ => by ring)
  · -- One round.
    have hlen := halves_length l
    have hnlen := halves_length n
    have hclen := halves_length c
    have hrinv : inverse rho = .ok rho⁻¹ := by simp [inverse, hrho]
    obtain ⟨lb1, hX, hp1, hh1, hg1, hg01⟩ := LazyBases.msm_eq lb hp
      (2 * rho⁻¹ * weighted_inner_product (halves n).1 (halves n).2 (rho * rho * (rho * rho)) +
        inner_product (halves c).1 (halves l).2 + inner_product (halves c).2 (halves l).1)
      (from_halves (halves l).2 (halves l).1)
      (from_halves (vec_scalar_mul rho (halves n).2) (vec_scalar_mul rho⁻¹ (halves n).1))
      (by rw [length_from_halves, hh]; omega)
      (by rw [length_from_halves, length_vec_scalar_mul, length_vec_scalar_mul, hg]; omega)
    obtain ⟨lb2, hR, hp2, hh2, hg2, hg02⟩ := LazyBases.msm_eq lb1 hp1
      (weighted_norm (halves n).2 (rho * rho * (rho * rho)) + inner_product (halves c).2 (halves l).2)
      (from_odd_half (halves l).2) (from_odd_half (halves n).2)
      (by rw [from_odd_half_eq, length_from_halves, hh1, hh]; simp; omega)
      (by rw [from_odd_half_eq, length_from_halves, hg1, hg]; simp; omega)
    rw [hh1, hg1, hg01] at hR
    rw [x_point_eq C lb c rho l n hc hh hg, hg0] at hX
    rw [r_point_eq C lb c rho l n hc hh hg, hg0] at hR
    set x := toInst C lb c rho l n
    set w := toWit l n
    set X := Spec.NormLinear.msgX gens.g x w
    set R := Spec.NormLinear.msgR gens.g x w
    set gamma := t.oracle (t.log ++ [.point "X" X, .point "R" R, .challenge "gamma"])
    have hfold := fold_toInst C lb c rho l n X R gamma lb2 hp2 hc hh hg (hh2.trans hh1)
      (hg2.trans hg1)
    have hrel' := Spec.NormLinear.fold_rel gens.g x w hrho (by simp only [x, toInst]; ring) gamma
      hrel
    rw [← hfold.1, ← hfold.2] at hrel'
    simp only [is_base_case, FOLD_THRESHOLD, Bool.and_eq_true, decide_eq_true_eq, not_and,
      not_lt] at hb
    obtain ⟨proof', t', cf, rhof, muf, gs, Wh', Wg', hrun, hr1, hn1, hv, hgs, hcf, hWh', hWg', hch,
      hcg, hfin⟩ := ih _ (by
        simp only [length_vec_add, length_vec_scalar_mul, length_halves_fst,
          length_halves_snd, half] at *
        omega)
      (lb2.fold rho gamma) (vec_add (halves c).1 (vec_scalar_mul gamma (halves c).2)) (rho * rho)
      (vec_add (halves l).1 (vec_scalar_mul gamma (halves l).2))
      (vec_add (vec_scalar_mul rho⁻¹ (halves n).1) (vec_scalar_mul gamma (halves n).2))
      (C + gamma • X + (gamma ^ 2 - 1) • R)
      (t.extend [.point "X" X, .point "R" R, .challenge "gamma"])
      (W_h.tensor_pair one gamma) (W_g.tensor_pair rho gamma) (gammas ++ [gamma]) rfl
      (LazyBases.pos_fold hp2 _ _) (by rw [length_tensor_pair]; omega)
      (by rw [length_tensor_pair]; omega)
      (by rw [LazyBases.cur_h_fold _ hp2, hh2, hh1, hcur_h, contract'_tensor_pair hWh])
      (by rw [LazyBases.cur_g_fold _ hp2, hg2, hg1, hcur_g, contract'_tensor_pair hWg])
      (by rw [LazyBases.g0_fold, hg02, hg01, hg0])
      (by simp [length_vec_add, length_vec_scalar_mul, hlen, hclen, hc])
      (by rw [LazyBases.cur_h_fold _ hp2, length_foldPts, hh2, hh1, hh]
          simp [length_vec_add, length_vec_scalar_mul, hlen])
      (by rw [LazyBases.cur_g_fold _ hp2, length_foldPts, hg2, hg1, hg]
          simp [length_vec_add, length_vec_scalar_mul, hnlen])
      (by simp [length_vec_add, length_vec_scalar_mul, hlen]; omega)
      (mul_ne_zero hrho hrho) hrel'
    refine ⟨{ proof' with rounds := (X, R) :: proof'.rounds }, t', cf, rhof, muf, gamma :: gs, Wh',
      Wg', ?_, ?_, hn1.trans ?_, ?_, by simp [hgs], hcf, hWh', hWg', hch, hcg, ?_⟩
    · simp only [dif_neg (by simp [is_base_case, FOLD_THRESHOLD]; omega : ¬ is_base_case l.length n.length),
        StateT.run_bind]
      rw [hrinv, run_liftM_ok, ok_bind]
      simp only
      rw [hX, run_liftM_ok, ok_bind]
      simp only
      rw [hR, run_liftM_ok, ok_bind]
      simp only [run_append_point, ok_bind, run_challenge_scalar, extend_extend, extend_log,
        extend_oracle, List.append_assoc, List.cons_append, List.nil_append]
      rw [hrun]
      rfl
    · have hb' : ¬ is_base_case l.length n.length := by simp [is_base_case, FOLD_THRESHOLD]; omega
      rw [List.length_cons, hr1, proof_shape_step hb']
      simp [length_vec_add, length_vec_scalar_mul, hlen, hnlen]
    · have hb' : ¬ is_base_case l.length n.length := by simp [is_base_case, FOLD_THRESHOLD]; omega
      rw [proof_shape_step hb']
      simp [length_vec_add, length_vec_scalar_mul, hlen, hnlen]
    · rw [List.foldlM_cons, StateT.run_bind]
      simp only [verify_round, StateT.run_bind, run_append_point, ok_bind, run_challenge_scalar,
        extend_extend, extend_log, extend_oracle, List.append_assoc, List.cons_append,
        List.nil_append, StateT.run_pure]
      rw [pure_bind]
      refine hv.trans ?_
      simp
    · simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, ← add_assoc]
      exact hfin

end NormLinear

end Bppp
