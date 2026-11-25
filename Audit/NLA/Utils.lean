import Mathlib

/-!
# Utilities for the audit

This file defines the vector operations of `Audit/NLA/Round.lean`.

Why it exists:
- `Rel`, `msgX`, `msgR` and the fold use these operations.
- A separate file keeps `Audit/NLA/Round.lean` short.
- The spec `Audit/02-RangeProof.lean` does not use this file. Only the proof of `range_sound`
  uses it. You do not need to review it.

Assumptions:
- A vector of length `m` is a function `Fin m → F`.
- Slots count from 0. Slot `i` of a weighted inner product has the weight `μ^(i+1)`.
-/

namespace Audit.NLA

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-! ## Vectors -/

section Vectors

variable {m : ℕ}

/-- The inner product `⟨a, b⟩ = Σᵢ aᵢ bᵢ`. -/
def ip (a b : Fin m → F) : F := ∑ i, a i * b i

/-- The weighted inner product `⟨a, b⟩_μ = Σᵢ μ^(i+1) aᵢ bᵢ`. -/
def wip (μ : F) (a b : Fin m → F) : F := ∑ i : Fin m, μ ^ (i.val + 1) * (a i * b i)

/-- The multi-scalar multiplication `⟨a, G⟩ = Σᵢ aᵢ • Gᵢ`. -/
def msm (a : Fin m → F) (G : Fin m → E) : E := ∑ i, a i • G i

/-! Notation, as in the paper. Write `⟪a, b⟫` for `⟨a, b⟩`, because Lean uses `⟨a, b⟩` to build
structures. The notation is scoped: it works in the namespace `Audit.NLA` and after
`open Audit.NLA`. -/

/-- `⟪a, b⟫` is the inner product `ip a b`. -/
scoped notation "⟪" a ", " b "⟫" => ip a b

/-- `⟪a, b⟫_μ` is the weighted inner product `wip μ a b`. -/
scoped notation "⟪" a ", " b "⟫_" μ:max => wip μ a b

/-- `‖a‖²_μ` is the weighted norm `wip μ a a`. -/
scoped notation "‖" a "‖²_" μ:max => wip μ a a

/-- `x²` is `x ^ 2`. -/
scoped notation:max x:max "²" => x ^ 2

/-- `x³` is `x ^ 3`. -/
scoped notation:max x:max "³" => x ^ 3

/-- `⌈m/2⌉`, the length of each half of a vector of length `m`. -/
def half (m : ℕ) : ℕ := (m + 1) / 2

/-! Tests: `half` rounds up. -/
example : half 0 = 0 := rfl
example : half 1 = 1 := rfl
example : half 2 = 1 := rfl
example : half 3 = 2 := rfl
example : half 8 = 4 := rfl
example : half 9 = 5 := rfl

/-- The even slots `v₀, v₂, v₄, …` of `v`. -/
def evens {α : Type} (v : Fin m → α) : Fin (half m) → α :=
  fun i => v ⟨2 * i.val, by have := i.isLt; unfold half at this; omega⟩

/-- The odd slots `v₁, v₃, v₅, …` of `v`. If `m` is odd, the last slot is 0, as in the Rust
`halves`. For points, 0 is the identity. -/
def odds {α : Type} [Zero α] (v : Fin m → α) : Fin (half m) → α :=
  fun i => if h : 2 * i.val + 1 < m then v ⟨2 * i.val + 1, h⟩ else 0

/-! Tests: `evens` and `odds` on an even length, an odd length, and length 1. -/
example : evens (![1, 2, 3, 4] : Fin 4 → ℕ) = ![1, 3] := by ext i; fin_cases i <;> rfl
example : odds (![1, 2, 3, 4] : Fin 4 → ℕ) = ![2, 4] := by ext i; fin_cases i <;> rfl
example : evens (![1, 2, 3, 4, 5] : Fin 5 → ℕ) = ![1, 3, 5] := by ext i; fin_cases i <;> rfl
example : odds (![1, 2, 3, 4, 5] : Fin 5 → ℕ) = ![2, 4, 0] := by ext i; fin_cases i <;> rfl
example : evens (![7] : Fin 1 → ℕ) = ![7] := by ext i; fin_cases i; rfl
example : odds (![7] : Fin 1 → ℕ) = ![0] := by ext i; fin_cases i; rfl

end Vectors

end Audit.NLA
