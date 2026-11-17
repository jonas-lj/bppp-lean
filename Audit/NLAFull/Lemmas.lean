import Audit.NLA.Proofs

/-!
# Round lemmas for the full NLA

This file proves the facts about one round that the full NLA chains together.

Why it exists:
- `nla_complete` and `nla_sound` in `Audit/NLAFull.lean` use these lemmas.
- Only proofs live here. The statements that we audit stay in `Audit/NLAFull.lean`.

How it works:
1. `independent_fold`: if the generators are independent, then the folded generators are
   independent.
2. `even_of_two_pow_dvd`: if `2^(r+1)` divides `k`, then `k` is even and `2^r` divides `half k`.

Assumptions:
- `ρ ≠ 0`, as each `Instance` carries.
-/

namespace Audit.NLA

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-- If the generators of `x` are independent, then the folded generators are independent. -/
theorem independent_fold {m k : ℕ} (x : Instance F E m k) (hind : x.Independent) (X R : E)
    (γ : F) : (foldInst x X R γ).Independent := by
  intro o h0
  have h1 : x.point ⟨o.σ, expand 1 γ o.ℓ, expand x.ρ γ o.n⟩ = 0 := by
    have hH : evens x.H + γ • odds x.H = (1 : F) • evens x.H + γ • odds x.H := by rw [one_smul]
    simp only [Instance.point, foldInst] at h0
    rw [hH, msm_expand, msm_expand] at h0
    exact h0
  have ho := hind _ h1
  simp only [Opening.ext_iff] at ho
  obtain ⟨hσ, hℓ, hn⟩ := ho
  ext i
  · exact hσ
  · have hi : 2 * i.val < m := by have := i.isLt; unfold half at this; omega
    have := congrFun hℓ ⟨2 * i.val, hi⟩
    rw [expand_even _ _ _ _ hi, one_mul] at this
    exact this
  · have hi : 2 * i.val < k := by have := i.isLt; unfold half at this; omega
    have := congrFun hn ⟨2 * i.val, hi⟩
    rw [expand_even _ _ _ _ hi] at this
    exact (mul_eq_zero.mp this).resolve_left x.hρ

/-- If `2^(r+1)` divides `k`, then `k` is even, and `2^r` divides `half k`. -/
theorem even_of_two_pow_dvd {k r : ℕ} (h : 2 ^ (r + 1) ∣ k) : k % 2 = 0 ∧ 2 ^ r ∣ half k := by
  obtain ⟨q, rfl⟩ := h
  refine ⟨by rw [pow_succ]; simp [Nat.mul_mod, Nat.mul_assoc], ⟨q, ?_⟩⟩
  unfold half
  rw [show 2 ^ (r + 1) * q = 2 * (2 ^ r * q) by ring]
  omega

end Audit.NLA
