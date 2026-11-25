import Audit.RangeProof.Statement
import Audit.RangeProof.Sound.Lagrange
import Bppp.Soundness

/-!
# The coordinate space of the range extractor

This file sets up `Combination F P` as a space of points with independent generators.

Why it exists:
- Jonas's `circuit_extract` (`Bppp/Spec/CircuitExtract.lean`) ends in "a witness, or a relation
  among the generators". It proves this by contradiction, so it does not compute anything.
- In `Combination F P`, the generators are the unit vectors. They have no relation. So Jonas's
  lemma gives a witness there, and the witness can be read off the coordinates.
- The extractor computes the coordinates of every commitment. If a coordinate equation fails,
  the difference is a link between the real generators.

How it works:
1. `combMap gens` maps a combination to its point over the real generators. It is linear.
2. `unitGens` are the unit vectors. `combMap` maps them to the real generators
   (`combMap_eH`, `combMap_eG`).
3. With `unitGens`, Jonas's `commit` is the vector of its coordinates (`commit_unit`). So the
   unit generators have no relation (`not_relation_unit`).
4. `interp`: interpolation with `lagInv` commutes with a linear map.
5. `firstNZ`: the first nonzero candidate of a list, or 0.

Assumptions:
- `gens` has 8 points in `h_vec` and `nm` points in `g_vec`, as `Setup` says.
-/

namespace Audit.RangeProof.Sound

open Finset Bppp

variable {F E : Type} [Field F] [DecidableEq F] [AddCommGroup E] [Module F E]

set_option linter.unusedSectionVars false

/-! ## The map to the real points -/

/-- The point of a combination over the real generators. -/
def combMap (P : CircuitParams) (gens : Generators E) : Combination F P →ₗ[F] E where
  toFun o := o.1 • gens.g + ∑ i, o.2.1 i • gens.h_vec.getD i 0 + ∑ j, o.2.2 j • gens.g_vec.getD j 0
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, sum_add_distrib]
    abel
  map_smul' c a := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
      RingHom.id_apply, smul_add, smul_sum]

/-- A link between the generators is a nonzero combination that `combMap` maps to 0. -/
theorem isGeneratorLink_iff {P : CircuitParams} (x : RangeStatement F E P)
    (o : Combination F P) : IsGeneratorLink x o ↔ o ≠ 0 ∧ combMap P x.gens o = 0 := by
  rw [isGeneratorLink_iff_gens]
  rfl

/-! ## The unit generators -/

variable (P : CircuitParams)

/-- The unit vector of `g`. -/
def eg : Combination F P := (1, 0, 0)

/-- The unit vector of `h_vec[i]`, or 0 if `8 ≤ i`. -/
def eH (i : ℕ) : Combination F P :=
  if h : i < H_LEN then (0, Pi.single ⟨i, h⟩ 1, 0) else 0

/-- The unit vector of `g_vec[j]`, or 0 if `nm ≤ j`. -/
def eG (j : ℕ) : Combination F P :=
  if h : j < P.nm then (0, 0, Pi.single ⟨j, h⟩ 1) else 0

/-- The unit generators: `g`, then 8 points `h_vec`, then `nm` points `g_vec`. -/
def unitGens : Generators (Combination F P) :=
  ⟨eg P, (List.range H_LEN).map (eH P), (List.range P.nm).map (eG P)⟩

theorem unitGens_h (i : ℕ) : (unitGens (F := F) P).h_vec.getD i 0 = eH P i := by
  by_cases hi : i < H_LEN
  · simp [unitGens, List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by simp [unitGens]; omega)]
    simp [eH, hi]

theorem unitGens_g (j : ℕ) : (unitGens (F := F) P).g_vec.getD j 0 = eG P j := by
  by_cases hj : j < P.nm
  · simp [unitGens, List.getD_eq_getElem?_getD, hj]
  · rw [List.getD_eq_default _ _ (by simp [unitGens]; omega)]
    simp [eG, hj]

variable {P}

theorem combMap_eg (gens : Generators E) : combMap P gens (eg (F := F) P) = gens.g := by
  simp [combMap, eg]

theorem combMap_eH (gens : Generators E) (hh : gens.h_vec.length = H_LEN) (i : ℕ) :
    combMap (F := F) P gens (eH P i) = gens.h_vec.getD i 0 := by
  by_cases hi : i < H_LEN
  · simp [combMap, eH, hi, Pi.single_apply]
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [eH, hi]

theorem combMap_eG (gens : Generators E) (hg : gens.g_vec.length = P.nm) (j : ℕ) :
    combMap (F := F) P gens (eG P j) = gens.g_vec.getD j 0 := by
  by_cases hj : j < P.nm
  · simp [combMap, eG, hj, Pi.single_apply]
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [eG, hj]

/-! ## Jonas's `commit` over the unit generators -/

variable (hv : P.Valid)

omit [DecidableEq F] in
@[simp] theorem eg_coords : (eg (F := F) P).1 = 1 ∧ (eg (F := F) P).2.1 = 0 ∧
    (eg (F := F) P).2.2 = 0 := ⟨rfl, rfl, rfl⟩

omit [DecidableEq F] in
theorem eH_coords (k : ℕ) : (eH (F := F) P k).1 = 0 ∧
    (∀ i : Fin H_LEN, (eH (F := F) P k).2.1 i = if k = i then 1 else 0) ∧
    (eH (F := F) P k).2.2 = 0 := by
  unfold eH
  split_ifs with hk
  · refine ⟨rfl, fun i => ?_, rfl⟩
    simp only [Pi.single_apply, Fin.ext_iff]
    by_cases e : k = i <;> simp [e, eq_comm]
  · refine ⟨rfl, fun i => ?_, rfl⟩
    have : k ≠ i := fun e => hk (e ▸ i.isLt)
    simp [this]

omit [DecidableEq F] in
theorem eG_coords (k : ℕ) : (eG (F := F) P k).1 = 0 ∧ (eG (F := F) P k).2.1 = 0 ∧
    (∀ j : Fin P.nm, (eG (F := F) P k).2.2 j = if k = j then 1 else 0) := by
  unfold eG
  split_ifs with hk
  · refine ⟨rfl, rfl, fun i => ?_⟩
    simp only [Pi.single_apply, Fin.ext_iff]
    by_cases e : k = i <;> simp [e, eq_comm]
  · refine ⟨rfl, rfl, fun i => ?_⟩
    have : k ≠ i := fun e => hk (e ▸ i.isLt)
    simp [this]

omit [DecidableEq F] in
@[simp] theorem eH_fst (k : ℕ) : (eH (F := F) P k).1 = 0 := (eH_coords (P := P) k).1
omit [DecidableEq F] in
@[simp] theorem eH_h (k : ℕ) (i : Fin H_LEN) :
    (eH (F := F) P k).2.1 i = if k = i then 1 else 0 := (eH_coords (P := P) k).2.1 i
omit [DecidableEq F] in
@[simp] theorem eH_n (k : ℕ) : (eH (F := F) P k).2.2 = 0 := (eH_coords (P := P) k).2.2
omit [DecidableEq F] in
@[simp] theorem eG_fst (k : ℕ) : (eG (F := F) P k).1 = 0 := (eG_coords (P := P) k).1
omit [DecidableEq F] in
@[simp] theorem eG_h (k : ℕ) : (eG (F := F) P k).2.1 = 0 := (eG_coords (P := P) k).2.1
omit [DecidableEq F] in
@[simp] theorem eG_n (k : ℕ) (j : Fin P.nm) :
    (eG (F := F) P k).2.2 j = if k = j then 1 else 0 := (eG_coords (P := P) k).2.2 j

omit [DecidableEq F] in
/-- Over the unit generators, `commit` is the vector of its coordinates. -/
theorem commit_unit (s : F) (h n : ℕ → F) :
    Spec.commit (P.toSpec hv) (eg P) (eH P) (eG P) s h n =
      ((s, fun i => h i, fun j => n j) : Combination F P) := by
  simp only [Spec.commit, Spec.NormLinear.msm, CircuitParams.nm_toSpec]
  ext i
  · simp [Prod.fst_sum]
  · have hi : (i : ℕ) < 8 := i.isLt
    simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, hi]
  · simp [Prod.snd_sum, Finset.sum_apply, i.isLt]

/-- The unit generators have no relation. -/
theorem not_relation_unit :
    ¬ Spec.Relation F (P.toSpec hv) (eg (F := F) P) (eH P) (eG P) := by
  rintro ⟨s, h, n, hne, h0⟩
  rw [commit_unit] at h0
  simp only [Prod.mk_eq_zero, funext_iff, Pi.zero_apply] at h0
  obtain ⟨hs, hh, hn⟩ := h0
  rcases hne with h1 | ⟨j, hj, hj'⟩ | ⟨j, hj, hj'⟩
  · exact h1 hs
  · exact hj' (hh ⟨j, hj⟩)
  · exact hj' (hn ⟨j, by simpa using hj⟩)

/-- `combMap` maps `commit` over the unit generators to `commit` over the real generators. -/
theorem combMap_commit (gens : Generators E) (hh : gens.h_vec.length = H_LEN)
    (hg : gens.g_vec.length = P.nm) (s : F) (h n : ℕ → F) :
    combMap P gens (Spec.commit (P.toSpec hv) (eg (F := F) P) (eH P) (eG P) s h n) =
      Spec.commit (P.toSpec hv) gens.g (fun k => gens.h_vec.getD k 0)
        (fun k => gens.g_vec.getD k 0) s h n := by
  simp only [Spec.commit, Spec.NormLinear.msm, map_add, map_sum, map_smul, combMap_eg,
    combMap_eH gens hh, combMap_eG gens hg]

/-! ## Interpolation -/

omit [DecidableEq F] in
/-- Interpolation commutes with a linear map: if `φ (Y k)` is the polynomial with coefficients
`Z` at `t k`, then `φ` of the interpolated coefficient `b` is `Z b`. -/
theorem interp {E' : Type} [AddCommGroup E'] [Module F E'] (φ : E' →ₗ[F] E) {n : ℕ}
    (t : Fin n → F) (ht : Function.Injective t) (Y : Fin n → E') (Z : Fin n → E)
    (h : ∀ k, φ (Y k) = ∑ j : Fin n, t k ^ (j : ℕ) • Z j) (b : Fin n) :
    φ (∑ k, lagInv t b k • Y k) = Z b := by
  simp only [map_sum, map_smul, h, smul_sum, smul_smul]
  rw [sum_comm]
  simp only [← sum_smul, lagInv_spec t ht, ite_smul, one_smul, zero_smul, sum_ite_eq,
    mem_univ, ite_true]

/-! ## The first nonzero candidate -/

/-- The first nonzero entry of `l`, or 0. -/
def firstNZ {α : Type} [Zero α] [DecidableEq α] (l : List α) : α :=
  (l.find? (· ≠ 0)).getD 0

theorem firstNZ_cons {α : Type} [Zero α] [DecidableEq α] (a : α) (l : List α) :
    firstNZ (a :: l) = if a = 0 then firstNZ l else a := by
  by_cases h : a = 0 <;> simp [firstNZ, List.find?_cons, h]

theorem firstNZ_eq_zero {α : Type} [Zero α] [DecidableEq α] (l : List α) :
    firstNZ l = 0 ↔ ∀ o ∈ l, o = 0 := by
  induction l with
  | nil => simp [firstNZ]
  | cons a l ih => by_cases h : a = 0 <;> simp [firstNZ_cons, h, ih]

theorem firstNZ_mem {α : Type} [Zero α] [DecidableEq α] (l : List α) (h : firstNZ l ≠ 0) :
    firstNZ l ∈ l := by
  induction l with
  | nil => simp [firstNZ] at h
  | cons a l ih => by_cases ha : a = 0 <;> simp_all [firstNZ_cons]

end Audit.RangeProof.Sound
