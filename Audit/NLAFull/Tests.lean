import Audit.NLAFull

/-!
# Tests of the NLA extractors

This file runs the extractors of `Audit/NLA.lean` and `Audit/NLAFull.lean` on small examples.

Why it exists:
- A `#guard` runs compiled code. So a passing test shows that Lean has code for the extractors.
  A `noncomputable` extractor cannot run.
- The tests also check the outputs. This is not a proof, but it catches a wrong formula early.

How it works:
1. Honest round: the honest prover answers 4 challenges. `extractWitness` gives back the
   witness, and `extractGeneratorLink` gives 0.
2. Cheating round: the points are in `ℚ`, so the generators have links. The prover changes the
   4th response, and the verifier still accepts it. `extractGeneratorLink` gives a nonzero
   opening of the zero point.
3. Honest tree: 2 rounds. `treeExtractWitness` gives back the witness, and
   `treeExtractGeneratorLink` gives 0.

Assumptions:
- Scalars and points are both `ℚ`. A real group is different, but the extractors do not read
  the points, so the test is still valid for them.
-/

namespace Audit.NLA.Tests

open Audit.NLA

/-- Over `ℚ`, the verifier's check `Rel` is an equality of numbers, so a test can run it. -/
instance {m k : ℕ} (x : Instance ℚ ℚ m k) (w : Witness ℚ m k) : Decidable (Rel x w) :=
  inferInstanceAs (Decidable (x.C = _))

/-! ## One round -/

/-- The witness of the round tests. -/
def w₁ : Witness ℚ 2 2 := ⟨![1, 2], ![3, 4]⟩

/-- The generators of the round tests, with `C = 0`. -/
def x₀ : Instance ℚ ℚ 2 2 where
  C := 0
  g := 1
  c := ![1, 2]
  H := ![2, 3]
  G := ![5, 7]
  ρ := 2
  hρ := by norm_num

/-- The round instance: `C` is the honest commitment to `w₁`. -/
def x₁ : Instance ℚ ℚ 2 2 := { x₀ with C := x₀.point (x₀.opening w₁) }

/-- The 4 challenges. -/
def γ₁ : Fin 4 → ℚ := ![1, 2, 3, 4]

/-- The honest messages `X`, `R` and the honest responses. -/
def X₁ : ℚ := msgX x₁ w₁
def R₁ : ℚ := msgR x₁ w₁
def ws₁ (i : Fin 4) : Witness ℚ (half 2) (half 2) := foldWit x₁ (γ₁ i) w₁

-- The verifier accepts the 4 honest responses.
#guard (List.finRange 4).all fun i => decide (Rel (foldInst x₁ X₁ R₁ (γ₁ i)) (ws₁ i))
-- `extractWitness` gives back `w₁`.
#guard List.ofFn (extractWitness x₁ γ₁ ws₁).ℓ == [1, 2]
#guard List.ofFn (extractWitness x₁ γ₁ ws₁).n == [3, 4]
-- `extractGeneratorLink` gives 0.
#guard decide (extractGeneratorLink x₁ γ₁ ws₁ = 0)

/-! ## A cheating round -/

/-- The only slot after one fold of length 2. -/
def s₀ : Fin (half 2) := ⟨0, by decide⟩

/-- The folded instance at the 4th challenge. -/
def x₃ : Instance ℚ ℚ (half 2) (half 2) := foldInst x₁ X₁ R₁ (γ₁ 3)

/-- The 4th response with its norm part changed by 1. -/
def wu : Witness ℚ (half 2) (half 2) := ⟨(ws₁ 3).ℓ, fun _ => (ws₁ 3).n s₀ + 1⟩

/-- The change of the linear part that keeps the point of the 4th response. -/
def t₃ : ℚ :=
  (x₃.point (x₃.opening (ws₁ 3)) - x₃.point (x₃.opening wu)) / (x₃.c s₀ * x₃.g + x₃.H s₀)

/-- The cheating 4th response. It is not the honest fold. -/
def wc : Witness ℚ (half 2) (half 2) := ⟨fun _ => (ws₁ 3).ℓ s₀ + t₃, wu.n⟩

/-- The responses: honest at `γ 0`, `γ 1`, `γ 2`, cheating at `γ 3`. -/
def wsc (i : Fin 4) : Witness ℚ (half 2) (half 2) := if i = 3 then wc else ws₁ i

-- The division in `t₃` is by a nonzero number.
#guard decide (x₃.c s₀ * x₃.g + x₃.H s₀ ≠ 0)
-- The verifier accepts all 4 responses.
#guard (List.finRange 4).all fun i => decide (Rel (foldInst x₁ X₁ R₁ (γ₁ i)) (wsc i))
-- `extractGeneratorLink` gives a link: a nonzero opening of the zero point.
#guard decide (extractGeneratorLink x₁ γ₁ wsc ≠ 0)
#guard decide (x₁.point (extractGeneratorLink x₁ γ₁ wsc) = 0)

/-! ## A tree of 2 rounds -/

/-- The 4 challenges are distinct. -/
theorem γ₁_distinct : ∀ i j, i ≠ j → γ₁ i ≠ γ₁ j := by decide

/-- The honest tree: each node forks at `γ₁`, and each response is the honest fold. -/
def honestTree {m k : ℕ} (x : Instance ℚ ℚ m k) (w : Witness ℚ m k) : ForkTree ℚ ℚ m k :=
  if hBase : IsBase m k then
    .leaf w
  else
    .node ⟨msgX x w, msgR x w, γ₁, γ₁_distinct⟩ fun i =>
      honestTree (foldInst x (msgX x w) (msgR x w) (γ₁ i)) (foldWit x (γ₁ i) w)
termination_by m + k
decreasing_by simp only [IsBase, half] at *; omega

/-- The witness of the tree test. The lengths fold `(4, 4) → (2, 2) → (1, 1)`. -/
def w₂ : Witness ℚ 4 4 := ⟨![1, 2, 3, 4], ![5, 6, 7, 8]⟩

/-- The generators of the tree test, with `C = 0`. -/
def y₀ : Instance ℚ ℚ 4 4 where
  C := 0
  g := 1
  c := ![1, 2, 3, 4]
  H := ![2, 3, 5, 7]
  G := ![11, 13, 17, 19]
  ρ := 3
  hρ := by norm_num

/-- The tree instance: `C` is the honest commitment to `w₂`. -/
def y₁ : Instance ℚ ℚ 4 4 := { y₀ with C := y₀.point (y₀.opening w₂) }

-- The tree has 16 transcripts, one for each pair of challenges.
#guard (honestTree y₁ w₂).transcripts.length == 16
-- `treeExtractWitness` gives back `w₂`.
#guard List.ofFn (treeExtractWitness y₁ (honestTree y₁ w₂)).ℓ == [1, 2, 3, 4]
#guard List.ofFn (treeExtractWitness y₁ (honestTree y₁ w₂)).n == [5, 6, 7, 8]
-- `treeExtractGeneratorLink` gives 0.
#guard decide (treeExtractGeneratorLink y₁ (honestTree y₁ w₂) = 0)

end Audit.NLA.Tests
