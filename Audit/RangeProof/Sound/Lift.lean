import Audit.RangeProof.Sound.Extractor
import Audit.RangeProof.Sound.Runs

/-!
# The lifted commitments map to the real commitments

This file proves that the coordinates that `rangeExtract` computes are coordinates of the real
commitments, if no NLA extractor gives a link.

Why it exists:
- `range_sound` (`Audit/RangeProof/Sound/Proofs.lean`) needs two facts. Each check of
  `leafChk` maps to the zero point. With all checks 0, Jonas's lemma applies in the coordinate
  space.

How it works:
1. `leaf_facts`: `leafVals_spec` at one leaf, with the inputs from `leafInputs_eq` and the
   relation from `path_rel`.
2. `extra_sum`: the extra points of `norm_linear::verify` add up to
   `τ⁻¹ C_S + δ C_O + τ C_L + τ² C_R + Σ_i 2 τ³ λ_i V_i`.
3. `nodeZ_spec`: if the leaves of a node give no link, `combMap` of `nodeZ` gives `C_S`,
   `δ C_O`, `C_L`, `C_R` and `V̂`. This is `interp` with `lagInv`.
4. `lift_spec`: `combMap` of each lifted commitment is the real commitment.
5. `chk_spec`: `combMap` of each check is 0.

Assumptions:
- Every path of the fork tree is accepted.
-/

namespace Audit.RangeProof.Sound

open Finset Bppp BpppTranscript Circuit Audit.TreeSoundness

variable {F E : Type} [Field F] [DecidableEq F] [AddCommGroup E] [Module F E] [DecidableEq E]

set_option linter.unusedSectionVars false

/-! ## The extra points -/

omit [DecidableEq E] in
/-- The sum of the extra points of `norm_linear::verify`, in any module. -/
theorem extra_sum {M : Type} [AddCommGroup M] [Module F M] [DecidableEq M] (C : Constraints F)
    (delta : F)
    (τ : Fˣ) (vcs : List (PedersenCommitment M)) (cS cO cL cR : M) :
    ((extraOf C delta τ vcs cS cO cL cR).map fun (s, p) => s • p).sum =
      (τ : F)⁻¹ • cS + delta • cO + (τ : F) • cL + ((τ : F) * τ) • cR +
        ∑ i ∈ range vcs.length, (2 * ((τ : F) * τ * τ) * C.lambdas.getD i 0) •
          (vcs.getD i ⟨0⟩).point := by
  simp only [extraOf, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  have hz := sum_zipIdx_map vcs ⟨0⟩
    (fun i => 2 * ((τ : F) * τ * τ) * C.lambdas.getD i 0) (fun v => v.point)
  simp only at hz
  rw [hz]
  abel

/-! ## One leaf -/

section Leaf

variable {P : CircuitParams} (x : RangeStatement F E P) (t : RangeForkTree F E P)

/-- The unit of `τ` at a leaf. -/
abbrev tτu (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) (b : Fin 2)
    (l : Fin (P.m * (P.nm + 8) + 1)) (i : Fin 13) : Fˣ :=
  Units.mk0 _ (tτ t a r b l i).property

/-- **One leaf of the tree.** If every path is accepted, `leafVals_spec` holds at each leaf. -/
theorem leaf_facts (hv : P.Valid) (hacc : t.AllPaths ((rangeSystem F E P).Verify x))
    (hrounds : NLA.numRounds H_LEN P.nm = numNlaRounds P) (heven : NLA.EvenNorms H_LEN P.nm)
    (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) (b : Fin 2) (l : Fin (P.m * (P.nm + 8) + 1))
    (i : Fin 13) (C : Constraints F)
    (hCnew : Constraints.new P (tα t a).val ((tρ t a r).val * (tρ t a r).val) (tLam t a r b l) =
      .ok C)
    (hC : Constraints.Correct P (tα t a).val ((tρ t a r).val * (tρ t a r).val) (tLam t a r b l)
      C hv) :
    combMap P x.gens (leafV P x t a r b l i).1 = 0 ∧
      ((leafV P x t a r b l i).1 = 0 →
        combMap P x.gens (leafV P x t a r b l i).2 =
          ((extraOf C (tδ t a r).val (tτu t a r b l i) x.commitments (tCS t a r b l) (tCO t)
            (tCL t) (tCR t a)).map fun (s, p) => s • p).sum ∧
        ∃ w : NLA.Witness F H_LEN P.nm,
          NLA.Rel (leafInst P x.gens x.commitments (tCS t a r b l) (tCO t) (tCL t) (tCR t a)
            (cTau C (tβ t a r b).val (tτu t a r b l i))
            (psTau P C (tρ t a r).val (tδ t a r).val (tτu t a r b l i))
            (pnTau P C (tδ t a r).val (tτu t a r b l i)) C (tδ t a r).val (tρ t a r).val
            (tτu t a r b l i) (tρ t a r).property) w ∧
          (leafV P x t a r b l i).2 =
            toComb P ((leafInst P x.gens x.commitments (tCS t a r b l) (tCO t) (tCL t) (tCR t a)
              (cTau C (tβ t a r b).val (tτu t a r b l i))
              (psTau P C (tρ t a r).val (tδ t a r).val (tτu t a r b l i))
              (pnTau P C (tδ t a r).val (tτu t a r b l i)) C (tδ t a r).val (tρ t a r).val
              (tτu t a r b l i) (tρ t a r).property).opening w) -
              pubPart P (psTau P C (tρ t a r).val (tδ t a r).val (tτu t a r b l i))
                (pnTau P C (tδ t a r).val (tτu t a r b l i)) ∧
          leafWit P x.gens x.commitments (tCS t a r b l) (tCO t) (tCL t) (tCR t a)
            (tα t a).val (tρ t a r) (tLam t a r b l) (tβ t a r b).val (tδ t a r).val
            (tτ t a r b l i) (tNla t a r b l i) = NLA.Bridge.ofWit w) := by
  have hdata := leafInputs_eq P hv (tα t a).val (tρ t a r).val (tLam t a r b l) (tβ t a r b).val
    (tδ t a r).val (tτu t a r b l i) C (tδ t a r).property hCnew hC
  have hpath : (tNla t a r b l i).AllPaths _ :=
    RoundTypes.ForkTree.AllPaths.mono (fun tr z h => path_rel x hv (tCL t) (tCO t) (tCR t a)
      (tCS t a r b l) (tα t a) (tρ t a r) (tδ t a r) (tβ t a r b) (tLam t a r b l) (tτ t a r b l i)
      tr z C hCnew hC h) (hacc a r (0 : Fin 1) b l i)
  exact leafVals_spec P x.gens x.commitments (tCS t a r b l) (tCO t) (tCL t) (tCR t a)
    x.setup.hGLen hrounds heven (tα t a).val (tρ t a r) (tLam t a r b l) (tβ t a r b).val
    (tδ t a r).val (tτ t a r b l i) (tNla t a r b l i) _ _ _ C hdata
    (by simp [cTau, H_LEN]) hpath

omit [DecidableEq F] [DecidableEq E] in
/-- `τ Y(τ)` is a polynomial of degree 4 in `τ`. -/
theorem tau_poly {M : Type} [AddCommGroup M] [Module F M] (τ : F) (hτ : τ ≠ 0) (δ : F)
    (cS cO cL cR : M) (n : ℕ) (c : ℕ → F) (V : ℕ → M) :
    τ • (τ⁻¹ • cS + δ • cO + τ • cL + (τ * τ) • cR + ∑ i ∈ range n, (2 * (τ * τ * τ) * c i) • V i) =
      ∑ j : Fin 5, τ ^ (j : ℕ) • ![cS, δ • cO, cL, cR, ∑ i ∈ range n, (2 * c i) • V i] j := by
  have hs : τ • ∑ i ∈ range n, (2 * (τ * τ * τ) * c i) • V i =
      τ ^ 4 • ∑ i ∈ range n, (2 * c i) • V i := by
    rw [smul_sum, smul_sum]
    exact sum_congr rfl fun i _ => by rw [smul_smul, smul_smul]; ring_nf
  rw [smul_add, hs, Fin.sum_univ_five]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Fin.val_zero, Fin.val_one,
    Fin.val_two, pow_zero, one_smul, pow_one]
  have e3 : ((3 : Fin 5) : ℕ) = 3 := rfl
  have e4 : ((4 : Fin 5) : ℕ) = 4 := rfl
  rw [e3, e4, smul_add, smul_add, smul_add, smul_smul, mul_inv_cancel₀ hτ, one_smul]
  simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  module

/-- The `τ` of a node are distinct. -/
theorem tauPts_inj {P : CircuitParams} (t : RangeForkTree F E P) (a : Fin (Nd P + 16))
    (r : Fin (P.nm + 1)) (b : Fin 2) (l : Fin (P.m * (P.nm + 8) + 1)) :
    Function.Injective (tauPts P t a r b l) := by
  intro k k' e
  by_contra hne
  have hne' : tauFirst k ≠ tauFirst k' := fun h => hne (Fin.castLE_injective _ h)
  exact (((((t.children a).children r).children 0).children b).children l).challenges.property
    _ _ hne' (Subtype.ext e)

/-- **One node.** If no leaf of the node `(a, r, b, l)` gives a link, then `combMap` of `nodeZ`
gives `C_S`, `δ C_O`, `C_L`, `C_R` and `V̂ = Σ_i 2 λ^i V_i`. -/
theorem nodeZ_spec (hv : P.Valid) (hacc : t.AllPaths ((rangeSystem F E P).Verify x))
    (hrounds : NLA.numRounds H_LEN P.nm = numNlaRounds P) (heven : NLA.EvenNorms H_LEN P.nm)
    (hpm : x.commitments.length = P.m)
    (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) (b : Fin 2) (l : Fin (P.m * (P.nm + 8) + 1))
    (C : Constraints F)
    (hCnew : Constraints.new P (tα t a).val ((tρ t a r).val * (tρ t a r).val) (tLam t a r b l) =
      .ok C)
    (hC : Constraints.Correct P (tα t a).val ((tρ t a r).val * (tρ t a r).val) (tLam t a r b l)
      C hv)
    (h0 : ∀ i, (leafV P x t a r b l i).1 = 0) (j : Fin 5) :
    combMap P x.gens (nodeZ P x t a r b l j) =
      ![tCS t a r b l, (tδ t a r).val • tCO t, tCL t, tCR t a,
        ∑ i ∈ range P.m, (2 * tLam t a r b l ^ i) • (x.commitments.getD i ⟨0⟩).point] j := by
  apply interp (combMap P x.gens) (tauPts P t a r b l) (tauPts_inj t a r b l)
  intro k
  set i := tauFirst k
  obtain ⟨hY, -⟩ := (leaf_facts x t hv hacc hrounds heven a r b l i C hCnew hC).2 (h0 i)
  rw [map_smul, hY, extra_sum, hpm]
  have hl : ∀ q ∈ range P.m, (2 * ((tτu t a r b l i : F) * tτu t a r b l i * tτu t a r b l i) *
      C.lambdas.getD q 0) • (x.commitments.getD q ⟨0⟩).point =
      (2 * ((tτu t a r b l i : F) * tτu t a r b l i * tτu t a r b l i) * tLam t a r b l ^ q) •
        (x.commitments.getD q ⟨0⟩).point := fun q hq => by
    rw [getD_lambdas P hv _ _ _ C hC q (mem_range.1 hq)]
  rw [sum_congr rfl hl]
  exact tau_poly _ (tτ t a r b l i).property _ _ _ _ _ _ (fun q => tLam t a r b l ^ q) _

omit [DecidableEq E] in
theorem liftVcs_length (P : CircuitParams) (x : RangeStatement F E P) (t : RangeForkTree F E P) :
    (liftVcs P x t).length = P.m := by
  simp [liftVcs]

omit [DecidableEq E] in
theorem liftVcs_getD (P : CircuitParams) (x : RangeStatement F E P) (t : RangeForkTree F E P)
    (q : ℕ) (hq : q < P.m) : ((liftVcs P x t).getD q ⟨0⟩).point = liftV P x t q := by
  simp [liftVcs, List.getD_eq_getElem?_getD, hq]

/-- The first `m` values of `λ` are distinct. -/
theorem lamPts_inj {P : CircuitParams} (t : RangeForkTree F E P) :
    Function.Injective (lamPts P t) := by
  intro k k' e
  by_contra hne
  have hne' : lamIdx P k ≠ lamIdx P k' := fun h => hne (Fin.castLE_injective _ h)
  exact ((((t.children 0).children 0).children 0).children 0).challenges.property _ _ hne' e

/-- The facts of `lift_spec`: the hypotheses of `nodeZ_spec` at every node. -/
structure LiftHyp (P : CircuitParams) (x : RangeStatement F E P) (t : RangeForkTree F E P)
    (hv : P.Valid) (C : Fin (Nd P + 16) → Fin (P.nm + 1) → Fin 2 → Fin (P.m * (P.nm + 8) + 1) →
      Constraints F) : Prop where
  hacc : t.AllPaths ((rangeSystem F E P).Verify x)
  hrounds : NLA.numRounds H_LEN P.nm = numNlaRounds P
  heven : NLA.EvenNorms H_LEN P.nm
  hpm : x.commitments.length = P.m
  h2 : (2 : F) ≠ 0
  hCnew : ∀ a r b l, Constraints.new P (tα t a).val ((tρ t a r).val * (tρ t a r).val)
    (tLam t a r b l) = .ok (C a r b l)
  hC : ∀ a r b l, Constraints.Correct P (tα t a).val ((tρ t a r).val * (tρ t a r).val)
    (tLam t a r b l) (C a r b l) hv
  hall : ∀ a r b l i, (leafV P x t a r b l i).1 = 0

variable {x t} {hv : P.Valid}
  {C : Fin (Nd P + 16) → Fin (P.nm + 1) → Fin 2 → Fin (P.m * (P.nm + 8) + 1) → Constraints F}

theorem LiftHyp.node (H : LiftHyp P x t hv C) (a r b l) (j : Fin 5) :
    combMap P x.gens (nodeZ P x t a r b l j) =
      ![tCS t a r b l, (tδ t a r).val • tCO t, tCL t, tCR t a,
        ∑ i ∈ range P.m, (2 * tLam t a r b l ^ i) • (x.commitments.getD i ⟨0⟩).point] j :=
  nodeZ_spec x t hv H.hacc H.hrounds H.heven H.hpm a r b l (C a r b l) (H.hCnew a r b l)
    (H.hC a r b l) (H.hall a r b l) j

/-- **The lifted commitments.** `combMap` maps each lifted commitment to the real one. -/
theorem LiftHyp.lift (H : LiftHyp P x t hv C) :
    (∀ a r b l, combMap P x.gens (liftCS P x t a r b l) = tCS t a r b l) ∧
      combMap P x.gens (liftCO P x t) = tCO t ∧ combMap P x.gens (liftCL P x t) = tCL t ∧
      (∀ a, combMap P x.gens (liftCR P x t a) = tCR t a) ∧
      ∀ q < P.m, combMap P x.gens (liftV P x t q) = (x.commitments.getD q ⟨0⟩).point := by
  refine ⟨fun a r b l => H.node a r b l 0, ?_, H.node 0 0 0 0 2, fun a => H.node a 0 0 0 3, ?_⟩
  · rw [liftCO, map_smul, H.node 0 0 0 0 1]
    simp [smul_smul, inv_mul_cancel₀ (tδ t 0 0).property]
  · intro q hq
    rw [liftV, dite_cond_eq_true (eq_true hq), map_smul]
    have hi := interp (combMap P x.gens) (lamPts P t) (lamPts_inj t)
      (fun l => nodeZ P x t 0 0 0 (lamIdx P l) 4)
      (fun q : Fin P.m => (2 : F) • (x.commitments.getD q ⟨0⟩).point) (fun l => by
        rw [H.node 0 0 0 (lamIdx P l) 4]
        show ∑ i ∈ range P.m, (2 * tLam t 0 0 0 (lamIdx P l) ^ i) •
          (x.commitments.getD i ⟨0⟩).point = _
        rw [← Fin.sum_univ_eq_sum_range (fun i => (2 * tLam t 0 0 0 (lamIdx P l) ^ i) •
          (x.commitments.getD i ⟨0⟩).point)]
        exact sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]; rfl) ⟨q, hq⟩
    rw [hi, smul_smul, inv_mul_cancel₀ H.h2, one_smul]

/-- **The checks.** `combMap` maps each check to 0. -/
theorem LiftHyp.chk (H : LiftHyp P x t hv C) (a r b l i) :
    combMap P x.gens (leafChk P x t a r b l i) = 0 := by
  obtain ⟨hS, hO, hL, hR, hV⟩ := H.lift
  have hdata := leafInputs_eq P hv (tα t a).val (tρ t a r).val (tLam t a r b l) (tβ t a r b).val
    (tδ t a r).val (tτu t a r b l i) (C a r b l) (tδ t a r).property (H.hCnew a r b l)
    (H.hC a r b l)
  simp only [tτu, Units.val_mk0] at hdata
  obtain ⟨hY, -⟩ := (leaf_facts x t hv H.hacc H.hrounds H.heven a r b l i (C a r b l)
    (H.hCnew a r b l) (H.hC a r b l)).2 (H.hall a r b l i)
  simp only [leafChk, hdata]
  rw [map_sub, hY, extra_sum, extra_sum, liftVcs_length, H.hpm]
  simp only [map_add, map_sum, map_smul, hS, hO, hL, hR]
  rw [sub_eq_zero]
  congr 1
  exact sum_congr rfl fun q hq => by
    rw [liftVcs_getD P x t q (mem_range.1 hq), hV q (mem_range.1 hq)]

end Leaf

end Audit.RangeProof.Sound
