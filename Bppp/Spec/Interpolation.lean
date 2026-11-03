import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-!
# Interpolation

A polynomial of degree at most `d` that vanishes at `d + 1` distinct points is zero (Lemma 1 of
the paper), for `d = 2, 3`, and the inverse of the `3 × 3` system `(1, γ, γ² - 1)` that the
norm-linear extractor solves.
-/

open Polynomial Finset

namespace Bppp.Spec

variable {F : Type*} [Field F]

/-- A cubic with four distinct roots is zero. -/
theorem cubic_zero (t : Fin 4 → F) (ht : Function.Injective t) (a0 a1 a2 a3 : F)
    (h : ∀ k, a0 + a1 * t k + a2 * t k ^ 2 + a3 * t k ^ 3 = 0) :
    a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 := by
  set p : F[X] := C a0 + C a1 * X + C a2 * X ^ 2 + C a3 * X ^ 3
  have hp : p = 0 := by
    refine eq_zero_of_degree_lt_of_eval_index_eq_zero univ (ht.injOn) ?_ ?_
    · rw [card_univ, Fintype.card_fin]
      refine lt_of_le_of_lt (degree_le_of_natDegree_le (p := p) (n := 3) ?_) (by decide)
      simp only [p]; compute_degree!
    · intro k _
      simp [p, h k]
  have c : ∀ i, p.coeff i = 0 := fun i => by rw [hp, coeff_zero]
  have c0 := c 0; have c1 := c 1; have c2 := c 2; have c3 := c 3
  simp [p, coeff_X, coeff_X_pow] at c0 c1 c2 c3
  exact ⟨c0, c1, c2, c3⟩

/-- A quadratic with three distinct roots is zero. -/
theorem quadratic_zero (t : Fin 3 → F) (ht : Function.Injective t) (a0 a1 a2 : F)
    (h : ∀ k, a0 + a1 * t k + a2 * t k ^ 2 = 0) : a0 = 0 ∧ a1 = 0 ∧ a2 = 0 := by
  set p : F[X] := C a0 + C a1 * X + C a2 * X ^ 2
  have hp : p = 0 := by
    refine eq_zero_of_degree_lt_of_eval_index_eq_zero univ (ht.injOn) ?_ ?_
    · rw [card_univ, Fintype.card_fin]
      refine lt_of_le_of_lt (degree_le_of_natDegree_le (p := p) (n := 2) ?_) (by decide)
      simp only [p]; compute_degree!
    · intro k _
      simp [p, h k]
  have c : ∀ i, p.coeff i = 0 := fun i => by rw [hp, coeff_zero]
  have c0 := c 0; have c1 := c 1; have c2 := c 2
  simp [p, coeff_X, coeff_X_pow] at c0 c1 c2
  exact ⟨c0, c1, c2⟩

/-! ## The `3 × 3` system -/

section System

variable (t0 t1 t2 : F)

/-- The weights that recover `C`, `X` and `R` from `C + γ_k X + (γ_k² - 1) R`, `k = 0, 1, 2`:
`b = 0, 1, 2` selects `C`, `X`, `R`. -/
noncomputable def lam (b : Fin 3) (m : Fin 3) : F :=
  let t := ![t0, t1, t2]
  let i := t (m + 1)
  let j := t (m + 2)
  let d := (t m - i) * (t m - j)
  match b with
  | 0 => (i * j + 1) / d
  | 1 => -(i + j) / d
  | 2 => 1 / d

variable {t0 t1 t2} (h01 : t0 ≠ t1) (h02 : t0 ≠ t2) (h12 : t1 ≠ t2)
include h01 h02 h12

/-- Recombining with the weights recovers each of `C`, `X`, `R`. -/
theorem lam_dual (b : Fin 3) :
    ∑ m, lam t0 t1 t2 b m = (if b = 0 then 1 else 0) ∧
    ∑ m, lam t0 t1 t2 b m * ![t0, t1, t2] m = (if b = 1 then 1 else 0) ∧
    ∑ m, lam t0 t1 t2 b m * (![t0, t1, t2] m ^ 2 - 1) = (if b = 2 then 1 else 0) := by
  have a := sub_ne_zero.2 h01; have b' := sub_ne_zero.2 h02; have c := sub_ne_zero.2 h12
  have a' := sub_ne_zero.2 h01.symm; have b'' := sub_ne_zero.2 h02.symm
  have c' := sub_ne_zero.2 h12.symm
  fin_cases b <;> simp [lam, Fin.sum_univ_three] <;> refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- The weighted combination at `γ_k` is the indicator of `k`. -/
theorem lam_kron (k m : Fin 3) :
    lam t0 t1 t2 0 m + ![t0, t1, t2] k * lam t0 t1 t2 1 m +
      (![t0, t1, t2] k ^ 2 - 1) * lam t0 t1 t2 2 m = if k = m then 1 else 0 := by
  have a := sub_ne_zero.2 h01; have b' := sub_ne_zero.2 h02; have c := sub_ne_zero.2 h12
  have a' := sub_ne_zero.2 h01.symm; have b'' := sub_ne_zero.2 h02.symm
  have c' := sub_ne_zero.2 h12.symm
  fin_cases k <;> fin_cases m <;> simp [lam] <;> field_simp <;> ring

end System

end Bppp.Spec
