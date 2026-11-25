import Audit.NLA.Utils

/-!
# Fold lemmas for the NLA audit

This file proves how each term of `Rel` changes under one fold.

Why it exists:
- The proof of `roundProtocol_complete` in `Audit/NLA/Proofs.lean` uses these lemmas.
- Only proofs and the helper `pad` live here. The statements that we audit stay in
  `Audit/NLA/Round.lean`.

How it works:
1. `sum_split` writes a sum over length `2m` as even and odd slots over length `m`.
2. `pad` makes a length even. It does not change a sum, so `sum_split` applies to any length.
3. Each fold lemma writes one folded term as a quadratic in `γ`. The `γ⁰` coefficient is the
   old term. The `γ¹` and `γ²` coefficients are the parts of `X` and `R`.

Assumptions:
- `ρ ≠ 0`, because the fold of the norm part uses `ρ⁻¹`.
-/

namespace Audit.NLA

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-- `v` with a 0 at the end if `m` is odd. The proofs use it. -/
def pad {α : Type} [Zero α] {m : ℕ} (v : Fin m → α) : Fin (2 * half m) → α :=
  fun j => if h : j.val < m then v ⟨j.val, h⟩ else 0

/-- Part 1a: a sum over length `2m` is a sum of even and odd slots over length `m`. -/
theorem sum_split {M : Type} [AddCommMonoid M] {m : ℕ} (f : Fin (2 * m) → M) :
    ∑ j, f j = ∑ i : Fin m,
      (f ⟨2 * i.val, by have := i.isLt; omega⟩ + f ⟨2 * i.val + 1, by have := i.isLt; omega⟩) := by
  rw [← (finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  congr 2 <;> ext <;> simp [finProdFinEquiv]
  omega

/-- Part 1a': padding with zeros does not change a sum. -/
theorem sum_pad {M : Type} [AddCommMonoid M] {m N : ℕ} (hmN : m ≤ N) (f : Fin m → M) :
    ∑ j : Fin N, (if h : j.val < m then f ⟨j.val, h⟩ else 0) = ∑ i, f i := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if h : j < m then f ⟨j, h⟩ else 0) N,
    ← Finset.sum_subset (Finset.range_mono hmN) fun j _ hj => by
      rw [Finset.mem_range] at hj; simp [hj],
    ← Fin.sum_univ_eq_sum_range (fun j => if h : j < m then f ⟨j, h⟩ else 0) m]
  simp

/-- Part 1a'': `pad` does not change an inner product. -/
theorem ip_pad {m : ℕ} (c ℓ : Fin m → F) : ip (pad c) (pad ℓ) = ip c ℓ := by
  rw [ip, ip, ← sum_pad (N := 2 * half m) (by unfold half; omega) (fun i => c i * ℓ i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [pad]
  split_ifs <;> simp

/-- Part 1a''': `pad` does not change a multi-scalar multiplication. -/
theorem msm_pad {m : ℕ} (ℓ : Fin m → F) (H : Fin m → E) : msm (pad ℓ) (pad H) = msm ℓ H := by
  rw [msm, msm, ← sum_pad (N := 2 * half m) (by unfold half; omega) (fun i => ℓ i • H i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [pad]
  split_ifs <;> simp

/-- `pad` does not change a weighted inner product, because it keeps each index. -/
theorem wip_pad {k : ℕ} (μ : F) (a b : Fin k → F) : wip μ (pad a) (pad b) = wip μ a b := by
  rw [wip, wip, ← sum_pad (N := 2 * half k) (by unfold half; omega)
    (fun i : Fin k => μ ^ (i.val + 1) * (a i * b i))]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [pad]
  split_ifs <;> simp

/-- `evens` reads the even slots of `pad v`. -/
theorem evens_eq {α : Type} [Zero α] {m : ℕ} (v : Fin m → α) (i : Fin (half m)) :
    evens v i = pad v ⟨2 * i.val, by have := i.isLt; omega⟩ := by
  have := i.isLt
  simp [evens, pad, show 2 * i.val < m by unfold half at this; omega]

/-- `odds` reads the odd slots of `pad v`. -/
theorem odds_eq {α : Type} [Zero α] {m : ℕ} (v : Fin m → α) (i : Fin (half m)) :
    odds v i = pad v ⟨2 * i.val + 1, by have := i.isLt; omega⟩ := rfl

/-- Part 1b: the fold of the linear term, as a quadratic in `γ`. -/
theorem ip_fold {m : ℕ} (c ℓ : Fin m → F) (γ : F) :
    ip (evens c + γ • odds c) (evens ℓ + γ • odds ℓ)
      = ip c ℓ + γ * (ip (evens c) (odds ℓ) + ip (odds c) (evens ℓ))
        + (γ ^ 2 - 1) * ip (odds c) (odds ℓ) := by
  rw [← ip_pad c ℓ]
  simp only [ip, sum_split (fun j => pad c j * pad ℓ j), evens_eq, odds_eq, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Part 1c: the fold of the weighted norm. The weight `ρ⁻¹` on the even half makes it work. -/
theorem wip_fold {k : ℕ} (ρ γ : F) (hρ : ρ ≠ 0) (n : Fin k → F) :
    wip ((ρ ^ 2) ^ 2) (ρ⁻¹ • evens n + γ • odds n) (ρ⁻¹ • evens n + γ • odds n)
      = wip (ρ ^ 2) n n + γ * (2 * ρ⁻¹ * wip ((ρ ^ 2) ^ 2) (evens n) (odds n))
        + (γ ^ 2 - 1) * wip ((ρ ^ 2) ^ 2) (odds n) (odds n) := by
  rw [← wip_pad (ρ ^ 2) n n]
  simp only [wip, sum_split (fun j : Fin (2 * half k) => (ρ ^ 2) ^ (j.val + 1) * (pad n j * pad n j)),
    evens_eq, odds_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring

/-- Part 1d: the fold of the linear generators `H`. -/
theorem msm_fold_H {m : ℕ} (ℓ : Fin m → F) (H : Fin m → E) (γ : F) :
    msm (evens ℓ + γ • odds ℓ) (evens H + γ • odds H)
      = msm ℓ H + γ • (msm (odds ℓ) (evens H) + msm (evens ℓ) (odds H))
        + (γ ^ 2 - 1) • msm (odds ℓ) (odds H) := by
  rw [← msm_pad ℓ H]
  simp only [msm, sum_split (fun j => pad ℓ j • pad H j), evens_eq, odds_eq, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Finset.smul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by module

/-- Part 1e: the fold of the norm generators `G`. The `ρ` and `ρ⁻¹` cancel. -/
theorem msm_fold_G {k : ℕ} (ρ γ : F) (hρ : ρ ≠ 0) (n : Fin k → F) (G : Fin k → E) :
    msm (ρ⁻¹ • evens n + γ • odds n) (ρ • evens G + γ • odds G)
      = msm n G + γ • (msm (ρ • odds n) (evens G) + msm (ρ⁻¹ • evens n) (odds G))
        + (γ ^ 2 - 1) • msm (odds n) (odds G) := by
  rw [← msm_pad n G]
  simp only [msm, sum_split (fun j => pad n j • pad G j), evens_eq, odds_eq, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  match_scalars <;> field_simp
  ring

end Audit.NLA
