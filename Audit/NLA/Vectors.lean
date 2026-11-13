import Mathlib

/-!
# Vectors for the NLA audit

This file defines the vector operations that `Audit/NLA.lean` uses.

Why it exists:
- `Rel`, `msgX` and `msgR` use these operations, so they are part of the specification.
- A separate file keeps `Audit/NLA.lean` short.

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

/-- The even slots `v₀, v₂, v₄, …` of a vector of length `2m`. -/
def evens {α : Type} (v : Fin (2 * m) → α) : Fin m → α :=
  fun i => v ⟨2 * i.val, by have := i.isLt; omega⟩

/-- The odd slots `v₁, v₃, v₅, …` of a vector of length `2m`. -/
def odds {α : Type} (v : Fin (2 * m) → α) : Fin m → α :=
  fun i => v ⟨2 * i.val + 1, by have := i.isLt; omega⟩

end Vectors

end Audit.NLA
