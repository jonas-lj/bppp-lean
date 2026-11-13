import Audit.NLA.Vectors

/-!
# Fold lemmas for the NLA audit

This file proves how each term of `Rel` changes under one fold.

Why it exists:
- The proof of `roundProtocol_complete` in `Audit/NLA.lean` uses these lemmas.
- Only proofs live here. The statements that we audit stay in `Audit/NLA.lean`.

How it works:
1. `sum_split` writes a sum over length `2m` as even and odd slots over length `m`.
2. Each fold lemma writes one folded term as a quadratic in `γ`. The `γ⁰` coefficient is the
   old term. The `γ¹` and `γ²` coefficients are the parts of `X` and `R`.

Assumptions:
- `ρ ≠ 0`, because the fold of the norm part uses `ρ⁻¹`.
-/

namespace Audit.NLA

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-- Part 1a: a sum over length `2m` is a sum of even and odd slots over length `m`. -/
theorem sum_split {M : Type} [AddCommMonoid M] {m : ℕ} (f : Fin (2 * m) → M) :
    ∑ j, f j = ∑ i : Fin m,
      (f ⟨2 * i.val, by have := i.isLt; omega⟩ + f ⟨2 * i.val + 1, by have := i.isLt; omega⟩) := by
  rw [← (finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  congr 2 <;> ext <;> simp [finProdFinEquiv]
  omega

/-- Part 1b: the fold of the linear term, as a quadratic in `γ`. -/
theorem ip_fold {m : ℕ} (c ℓ : Fin (2 * m) → F) (γ : F) :
    ip (evens c + γ • odds c) (evens ℓ + γ • odds ℓ)
      = ip c ℓ + γ * (ip (evens c) (odds ℓ) + ip (odds c) (evens ℓ))
        + (γ ^ 2 - 1) * ip (odds c) (odds ℓ) := by
  simp only [ip, sum_split (fun j => c j * ℓ j), evens, odds, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Part 1c: the fold of the weighted norm. The weight `ρ⁻¹` on the even half makes it work. -/
theorem wip_fold {k : ℕ} (ρ γ : F) (hρ : ρ ≠ 0) (n : Fin (2 * k) → F) :
    wip ((ρ ^ 2) ^ 2) (ρ⁻¹ • evens n + γ • odds n) (ρ⁻¹ • evens n + γ • odds n)
      = wip (ρ ^ 2) n n + γ * (2 * ρ⁻¹ * wip ((ρ ^ 2) ^ 2) (evens n) (odds n))
        + (γ ^ 2 - 1) * wip ((ρ ^ 2) ^ 2) (odds n) (odds n) := by
  simp only [wip, sum_split (fun j : Fin (2 * k) => (ρ ^ 2) ^ (j.val + 1) * (n j * n j)),
    evens, odds, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring

/-- Part 1d: the fold of the linear generators `H`. -/
theorem msm_fold_H {m : ℕ} (ℓ : Fin (2 * m) → F) (H : Fin (2 * m) → E) (γ : F) :
    msm (evens ℓ + γ • odds ℓ) (evens H + γ • odds H)
      = msm ℓ H + γ • (msm (odds ℓ) (evens H) + msm (evens ℓ) (odds H))
        + (γ ^ 2 - 1) • msm (odds ℓ) (odds H) := by
  simp only [msm, sum_split (fun j => ℓ j • H j), evens, odds, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.smul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by module

/-- Part 1e: the fold of the norm generators `G`. The `ρ` and `ρ⁻¹` cancel. -/
theorem msm_fold_G {k : ℕ} (ρ γ : F) (hρ : ρ ≠ 0) (n : Fin (2 * k) → F) (G : Fin (2 * k) → E) :
    msm (ρ⁻¹ • evens n + γ • odds n) (ρ • evens G + γ • odds G)
      = msm n G + γ • (msm (ρ • odds n) (evens G) + msm (ρ⁻¹ • evens n) (odds G))
        + (γ ^ 2 - 1) • msm (odds n) (odds G) := by
  simp only [msm, sum_split (fun j => n j • G j), evens, odds, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  match_scalars <;> field_simp
  ring

end Audit.NLA
