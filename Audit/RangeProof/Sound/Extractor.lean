import Audit.RangeProof.Sound.Leaf

/-!
# The range extractor

This file defines `rangeExtract`, the extractor of `RangeSoundness` (`Audit/02-RangeProof.lean`).

Why it exists:
- `RangeSoundness` is a statement about a named extractor. `range_sound`
  (`Audit/RangeProof/Sound/Proofs.lean`) proves it for `rangeExtract`.

How it works:
1. At each `τ` leaf, `leafV` runs the extractor of the full NLA. It gives a candidate link, and the
   coordinates of `Y(τ) = τ⁻¹ C_S + δ C_O + τ C_L + τ² C_R + τ³ V̂`. A coordinate vector is a
   `Combination`: a scalar for `g`, for each `h_vec[i]`, and for each `g_vec[j]`.
2. `nodeZ`: at each `λ` node, interpolation at the first 5 `τ` gives the coordinates of `C_S`,
   `δ C_O`, `C_L`, `C_R` and `V̂`.
3. `liftCO`, `liftCL`, `liftCR`, `liftCS` read the commitments off `nodeZ`. `liftV`: at the first
   node, interpolation at the first `m` values of `λ` gives the coordinates of each `V_i`, from
   `V̂ = 2 Σ_i λ^i V_i`.
4. `leafChk`: at each leaf, the coordinates of `Y(τ)` minus the value that the lifted
   commitments give. In the real group, each check is the zero point.
5. `rangeLink`: the first nonzero NLA link. If there is none, the first nonzero check.
6. The value of input `i` comes from the digits in the `g_vec` coordinates of `C_L`. The
   blinding is the `h_vec[0]` coordinate of `V_i`.

Assumptions:
- None for the definition. Every step is computable and takes polynomial time in the size of
  the tree: `lagInv` (`Audit/RangeProof/Sound/Lagrange.lean`) is `O(n⁴)`, and `digitOf` tries
  16 values.
-/

namespace Audit.RangeProof.Sound

open Finset Bppp Audit.TreeSoundness

variable {F E : Type} [Field F] [DecidableEq F] [AddCommGroup E] [Module F E] [DecidableEq E]

/-! ## The parts of the fork tree -/

section Tree

variable {P : CircuitParams} (t : RangeForkTree F E P)

/-- `C_L`, the first message. -/
def tCL : E := t.commitment.1

/-- `C_O`, the first message. -/
def tCO : E := t.commitment.2

/-- `α` of the branch `a`. -/
def tα (a : Fin (Nd P + 16)) : {α : F // ∀ j : ℕ, j < 16 → α + j ≠ 0} := t.challenges.val a

/-- `C_R` of the branch `a`. -/
def tCR (a : Fin (Nd P + 16)) : E := (t.children a).commitment

/-- `ρ` of the branch `(a, r)`. -/
def tρ (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) : {ρ : F // ρ ≠ 0} :=
  (t.children a).challenges.val r

/-- `δ` of the branch `(a, r)`. It is not forked. -/
def tδ (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) : {δ : F // δ ≠ 0} :=
  ((t.children a).children r).challenges.val 0

/-- `β` of the branch `(a, r, b)`. -/
def tβ (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) (b : Fin 2) : {β : F // β ≠ 0} :=
  (((t.children a).children r).children 0).challenges.val b

/-- `λ` of the branch `(a, r, b, l)`. -/
def tLam (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) (b : Fin 2)
    (l : Fin (P.m * (P.nm + 8) + 1)) : F :=
  ((((t.children a).children r).children 0).children b).challenges.val l

/-- `C_S` of the branch `(a, r, b, l)`. -/
def tCS (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) (b : Fin 2)
    (l : Fin (P.m * (P.nm + 8) + 1)) : E :=
  (((((t.children a).children r).children 0).children b).children l).commitment

/-- `τ` of the branch `(a, r, b, l, i)`. -/
def tτ (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) (b : Fin 2)
    (l : Fin (P.m * (P.nm + 8) + 1)) (i : Fin 13) : {τ : F // τ ≠ 0} :=
  (((((t.children a).children r).children 0).children b).children l).challenges.val i

/-- The NLA subtree of the branch `(a, r, b, l, i)`. -/
def tNla (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) (b : Fin 2)
    (l : Fin (P.m * (P.nm + 8) + 1)) (i : Fin 13) :
    (nlaRounds F E (numNlaRounds P)).ForkTree (nlaForks F E (numNlaRounds P)) (F × List F) :=
  ((((((t.children a).children r).children 0).children b).children l).children i)

end Tree

/-! ## The extractor -/

section Extract

variable (P : CircuitParams) (x : RangeStatement F E P) (t : RangeForkTree F E P)

/-- The values of the leaf `(a, r, b, l, i)`: a candidate link, and the coordinates of `Y(τ)`. -/
def leafV (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) (b : Fin 2)
    (l : Fin (P.m * (P.nm + 8) + 1)) (i : Fin 13) : Combination F P × Combination F P :=
  leafVals P x.gens x.commitments (tCS t a r b l) (tCO t) (tCL t) (tCR t a) (tα t a).val
    (tρ t a r) (tLam t a r b l) (tβ t a r b).val (tδ t a r).val (tτ t a r b l i) (tNla t a r b l i)

/-- The indices of the first five `τ`. -/
def tauFirst : Fin 5 → Fin 13 := Fin.castLE (by norm_num)

/-- The first five `τ` of the node `(a, r, b, l)`. -/
def tauPts (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) (b : Fin 2)
    (l : Fin (P.m * (P.nm + 8) + 1)) : Fin 5 → F :=
  fun k => (tτ t a r b l (tauFirst k)).val

/-- The coordinates of coefficient `j` of `τ Y(τ)` at the node `(a, r, b, l)`. The coefficients
are `C_S`, `δ C_O`, `C_L`, `C_R` and `V̂`. -/
def nodeZ (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) (b : Fin 2)
    (l : Fin (P.m * (P.nm + 8) + 1)) (j : Fin 5) : Combination F P :=
  ∑ k, lagInv (tauPts P t a r b l) j k •
    (tauPts P t a r b l k • (leafV P x t a r b l (tauFirst k)).2)

/-- The coordinates of `C_S` at the node `(a, r, b, l)`. -/
def liftCS (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) (b : Fin 2)
    (l : Fin (P.m * (P.nm + 8) + 1)) : Combination F P :=
  nodeZ P x t a r b l 0

/-- The coordinates of `C_O`, from the first node. -/
def liftCO : Combination F P := (tδ t 0 0).val⁻¹ • nodeZ P x t 0 0 0 0 1

/-- The coordinates of `C_L`, from the first node. -/
def liftCL : Combination F P := nodeZ P x t 0 0 0 0 2

/-- The coordinates of `C_R` of the branch `a`, from its first node. -/
def liftCR (a : Fin (Nd P + 16)) : Combination F P := nodeZ P x t a 0 0 0 3

/-- The indices of the first `m` values of `λ`. -/
def lamIdx : Fin P.m → Fin (P.m * (P.nm + 8) + 1) :=
  Fin.castLE (Nat.le_succ_of_le (Nat.le_mul_of_pos_right _ (by omega)))

/-- The first `m` values of `λ` at the first node. -/
def lamPts : Fin P.m → F := fun l => tLam t 0 0 0 (lamIdx P l)

/-- The coordinates of the input `V_i`: interpolation of `V̂ = Σ_i λ^i (2 V_i)` at the first `m`
values of `λ`. -/
def liftV (i : ℕ) : Combination F P :=
  if h : i < P.m then
    (2 : F)⁻¹ • ∑ l, lagInv (lamPts P t) ⟨i, h⟩ l • nodeZ P x t 0 0 0 (lamIdx P l) 4
  else 0

/-- The inputs with the lifted coordinates. -/
def liftVcs : List (PedersenCommitment (Combination F P)) :=
  (List.range P.m).map fun i => ⟨liftV P x t i⟩

/-- The check of the leaf `(a, r, b, l, i)`: the coordinates of `Y(τ)` minus the value that the
lifted commitments give. -/
def leafChk (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) (b : Fin 2)
    (l : Fin (P.m * (P.nm + 8) + 1)) (i : Fin 13) : Combination F P :=
  match leafInputs P (tα t a).val (tρ t a r).val (tLam t a r b l) (tβ t a r b).val (tδ t a r).val
      (tτ t a r b l i).val with
  | .error _ => 0
  | .ok (_, _, _, C) =>
    (leafV P x t a r b l i).2 - ((Circuit.extraOf C (tδ t a r).val
      (Units.mk0 _ (tτ t a r b l i).property) (liftVcs P x t) (liftCS P x t a r b l)
      (liftCO P x t) (liftCL P x t) (liftCR P x t a)).map fun (s, p) => s • p).sum

/-- All leaves `(a, r, b, l, i)`. -/
def allIdx : List (Fin (Nd P + 16) × Fin (P.nm + 1) × Fin 2 × Fin (P.m * (P.nm + 8) + 1) ×
    Fin 13) :=
  (List.finRange _).flatMap fun a => (List.finRange _).flatMap fun r =>
    (List.finRange 2).flatMap fun b => (List.finRange _).flatMap fun l =>
      (List.finRange 13).map fun i => (a, r, b, l, i)

/-- The NLA links of all leaves. -/
def nlaLinks : List (Combination F P) :=
  (allIdx P).map fun (a, r, b, l, i) => (leafV P x t a r b l i).1

/-- The checks of all leaves. -/
def leafChks : List (Combination F P) :=
  (allIdx P).map fun (a, r, b, l, i) => leafChk P x t a r b l i

/-- The link: the first nonzero NLA link. If there is none, the first nonzero check. -/
def rangeLink : Combination F P :=
  if firstNZ (nlaLinks P x t) ≠ 0 then firstNZ (nlaLinks P x t) else firstNZ (leafChks P x t)

/-- The digit `j < 16` with `(j : F) = c`, or 0. -/
def digitOf (c : F) : ℕ := ((List.range 16).find? fun j : ℕ => ((j : ℕ) : F) = c).getD 0

/-- The `g_vec[k]` coordinate of `C_L`, or 0 if `nm ≤ k`. -/
def liftN (k : ℕ) : F := if h : k < P.nm then (liftCL P x t).2.2 ⟨k, h⟩ else 0

/-- **The range extractor.** The value of input `i` has the digits of its slots in `C_L`. The
blinding is the `h_vec[0]` coordinate of `V_i`. -/
def rangeExtract : RangeWitness F P where
  value i := ∑ s ∈ range P.d, 16 ^ s * digitOf (liftN P x t (i * P.d + s))
  blinding i := (liftV P x t i).2.1 ⟨0, by decide⟩
  link := rangeLink P x t

end Extract

end Audit.RangeProof.Sound
