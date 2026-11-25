import Audit.«02-RangeProof»

/-!
# The range statement in the Rust form

This file gives the facts about `RangeStatement` (`Audit/02-RangeProof.lean`) in the form of the
Rust inputs.

Why it exists:
- The statement holds the generators and the commitments as vectors. The proofs work with the
  Rust inputs `x.gens`, `x.generators` and `x.commitments`.

How it works:
- `LargeChar.cast_ne_zero`: no integer from 1 to `Nd + 16` is 0 in `F`.
- `RangeStatement.setup`: the Rust setup facts (`Setup`) hold for every statement.
- `opensInRange_iff` and `isGeneratorLink_iff_gens`: `OpensInRange` and `IsGeneratorLink` with
  the Rust lists.

Assumptions:
- None.
-/

namespace Audit.RangeProof

open Bppp

variable {F E : Type} [Field F] [DecidableEq F] [AddCommGroup E] [Module F E] [DecidableEq E]

set_option linter.unusedSectionVars false

/-- No integer from 1 to `Nd + 16` is 0 in `F`. -/
theorem LargeChar.cast_ne_zero {P : CircuitParams} (h : LargeChar F P) (k : ℕ) (hk : 0 < k)
    (hle : k ≤ Nd P + 16) : (k : F) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff F (ringChar F)]
  rcases h with h | h
  · rw [h, zero_dvd_iff]
    omega
  · exact fun hd => absurd (Nat.le_of_dvd hk hd) (by omega)

/-- The setup that Rust computes before it reads a proof (`range_proof.rs`, `crs.rs:61`). -/
structure Setup (generators : ℕ → Result (Generators E))
    (commitments : List (PedersenCommitment E)) (range : Range) (params : CircuitParams)
    (gens : Generators E) (G H : E) : Prop where
  hParams : CircuitParams.new range commitments.length = .ok params
  hGens : generators params.nm = .ok gens
  hHLen : gens.h_vec.length = H_LEN
  hGLen : gens.g_vec.length = params.nm
  hValueBase : gens.g = H
  hBlindingBase : gens.h_vec.getD 0 0 = G

omit [DecidableEq E] in
/-- Entry `i` of a list of `n` points, for `i < n`. -/
theorem getD_ofFn {n : ℕ} (f : Fin n → E) (i : Fin n) : (List.ofFn f).getD i 0 = f i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

namespace RangeStatement

variable {P : CircuitParams} (x : RangeStatement F E P)

omit [DecidableEq E] in
theorem length_commitments : x.commitments.length = P.m := by
  simp [commitments]

omit [DecidableEq E] in
/-- The Rust setup facts hold for every statement. -/
theorem setup : Setup x.generators x.commitments x.range P x.gens x.G x.H where
  hParams := by rw [length_commitments]; exact x.hParams
  hGens := rfl
  hHLen := by simp [gens]
  hGLen := by simp [gens]
  hValueBase := rfl
  hBlindingBase := getD_ofFn x.hVec ⟨0, by decide⟩

end RangeStatement

omit [DecidableEq E] in
/-- `OpensInRange` with the Rust list of commitments. -/
theorem opensInRange_iff {P : CircuitParams} (x : RangeStatement F E P) (v : ℕ → ℕ)
    (s : ℕ → F) : OpensInRange x v s ↔ ∀ i (hi : i < x.commitments.length),
      v i < 2 ^ x.range.bits ∧ x.commitments[i].point = (v i : F) • x.H + s i • x.G := by
  constructor
  · intro h i hi
    have hi' : i < P.m := by rwa [x.length_commitments] at hi
    simpa [RangeStatement.commitments] using h ⟨i, hi'⟩
  · intro h i
    simpa [RangeStatement.commitments] using h i (by simp [x.length_commitments])

omit [DecidableEq F] [DecidableEq E] in
/-- `IsGeneratorLink` with the Rust generators. -/
theorem isGeneratorLink_iff_gens {P : CircuitParams} (x : RangeStatement F E P)
    (o : Combination F P) : IsGeneratorLink x o ↔ o ≠ 0 ∧ o.1 • x.gens.g +
      ∑ i, o.2.1 i • x.gens.h_vec.getD i 0 + ∑ j, o.2.2 j • x.gens.g_vec.getD j 0 = 0 := by
  obtain ⟨s, h, n⟩ := o
  simp only [IsGeneratorLink, RangeStatement.gens, getD_ofFn]

end Audit.RangeProof
