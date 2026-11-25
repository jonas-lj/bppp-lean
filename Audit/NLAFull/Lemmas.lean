import Audit.NLA.Proofs

/-!
# Round lemmas for the full NLA

This file proves the facts about one round that the full NLA chains together.

Why it exists:
- The proofs in `Audit/NLAFull/Proofs.lean` and `Audit/NLAFull/LegacyProofs.lean` use these
  lemmas.
- Only proofs live here. The statements that we audit stay in `Audit/NLAFull/Full.lean`.

How it works:
1. `point_liftLink` and `eq_zero_of_liftLink_eq_zero`: a link on the folded generators lifts to
   a link on the generators before the fold.
2. `even_of_two_pow_dvd`: if `2^(r+1)` divides `k`, then `k` is even and `2^r` divides `half k`.

Assumptions:
- `ρ ≠ 0`, as each `Instance` carries.
-/

namespace Audit.NLA

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-- A link on the folded generators, as a link on the generators before the fold. -/
def liftLink {m k : ℕ} (ρ γ : F) (o : Opening F (half m) (half k)) : Opening F m k :=
  ⟨o.σ, expand 1 γ o.ℓ, expand ρ γ o.n⟩

/-- The lift opens the same point. -/
theorem point_liftLink {m k : ℕ} (x : Instance F E m k) (X R : E) (γ : F)
    (o : Opening F (half m) (half k)) :
    x.point (liftLink x.ρ γ o) = (foldInst x X R γ).point o := by
  have hH : evens x.H + γ • odds x.H = (1 : F) • evens x.H + γ • odds x.H := by rw [one_smul]
  simp only [Instance.point, foldInst, liftLink]
  rw [hH, msm_expand, msm_expand]

/-- The lift of a nonzero link is nonzero. -/
theorem eq_zero_of_liftLink_eq_zero {m k : ℕ} {ρ : F} (hρ : ρ ≠ 0) (γ : F)
    (o : Opening F (half m) (half k)) (h : liftLink ρ γ o = 0) : o = 0 := by
  simp only [liftLink, Opening.ext_iff] at h
  obtain ⟨hσ, hℓ, hn⟩ := h
  ext i
  · exact hσ
  · have hi : 2 * i.val < m := by have := i.isLt; unfold half at this; omega
    have := congrFun hℓ ⟨2 * i.val, hi⟩
    rw [expand_even _ _ _ _ hi, one_mul] at this
    exact this
  · have hi : 2 * i.val < k := by have := i.isLt; unfold half at this; omega
    have := congrFun hn ⟨2 * i.val, hi⟩
    rw [expand_even _ _ _ _ hi] at this
    exact (mul_eq_zero.mp this).resolve_left hρ

/-- If `2^(r+1)` divides `k`, then `k` is even, and `2^r` divides `half k`. -/
theorem even_of_two_pow_dvd {k r : ℕ} (h : 2 ^ (r + 1) ∣ k) : k % 2 = 0 ∧ 2 ^ r ∣ half k := by
  obtain ⟨q, rfl⟩ := h
  refine ⟨by rw [pow_succ]; simp [Nat.mul_mod, Nat.mul_assoc], ⟨q, ?_⟩⟩
  unfold half
  rw [show 2 ^ (r + 1) * q = 2 * (2 ^ r * q) by ring]
  omega

/-- Openings with scalars in `F` have decidable equality. -/
instance Opening.decEq [DecidableEq F] {m k : ℕ} : DecidableEq (Opening F m k) := fun _ _ =>
  decidable_of_iff _ Opening.ext_iff.symm

end Audit.NLA
