import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Tactic

/-!
# Laurent polynomials

Monomials, coefficients and supports of Laurent polynomials `F[T;T⁻¹]`.
-/

open LaurentPolynomial

namespace Bppp

variable {F : Type*} [Field F]

/-- The monomial `x*T^p`. -/
noncomputable def mono (p : ℤ) (x : F) : F[T;T⁻¹] := C x * T p

/-- The coefficient of `T^p`. -/
def coeff (p : ℤ) : F[T;T⁻¹] →+ F := Finsupp.applyAddHom p

theorem coeff_apply (p : ℤ) (f : F[T;T⁻¹]) : coeff p f = f p := rfl

@[simp] theorem coeff_mono (p q : ℤ) (x : F) : coeff q (mono p x) = if p = q then x else 0 := by
  rw [coeff_apply, mono, ← single_eq_C_mul_T, Finsupp.single_apply]

@[simp] theorem mono_zero (p : ℤ) : mono p (0 : F) = 0 := by simp [mono]

theorem mono_mul (p q : ℤ) (x y : F) : mono p x * mono q y = mono (p + q) (x * y) := by
  simp only [mono, map_mul, T_add]; ring

theorem ext_coeff {f g : F[T;T⁻¹]} (h : ∀ p, coeff p f = coeff p g) : f = g :=
  LaurentPolynomial.ext h

/-- Every nonzero coefficient of `f` is at a power in `[a, b]`. -/
def Supp (f : F[T;T⁻¹]) (a b : ℤ) : Prop := ∀ p, coeff p f ≠ 0 → a ≤ p ∧ p ≤ b

namespace Supp

theorem zero (a b : ℤ) : Supp (0 : F[T;T⁻¹]) a b := by intro p h; simp at h

theorem mono {p a b : ℤ} (x : F) (h₁ : a ≤ p) (h₂ : p ≤ b) : Supp (Bppp.mono p x) a b := by
  intro q h
  rw [coeff_mono] at h
  split_ifs at h with hpq
  · omega
  · exact absurd rfl h

theorem add {f g : F[T;T⁻¹]} {a b : ℤ} (hf : Supp f a b) (hg : Supp g a b) :
    Supp (f + g) a b := by
  intro p h
  rw [map_add] at h
  by_cases hfp : coeff p f = 0
  · exact hg p (by simpa [hfp] using h)
  · exact hf p hfp

theorem neg {f : F[T;T⁻¹]} {a b : ℤ} (hf : Supp f a b) : Supp (-f) a b := by
  intro p h; exact hf p (by simpa using h)

theorem sub {f g : F[T;T⁻¹]} {a b : ℤ} (hf : Supp f a b) (hg : Supp g a b) :
    Supp (f - g) a b := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem sum {ι : Type*} (s : Finset ι) {f : ι → F[T;T⁻¹]} {a b : ℤ}
    (h : ∀ i ∈ s, Supp (f i) a b) : Supp (∑ i ∈ s, f i) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero a b
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))

theorem mul {f g : F[T;T⁻¹]} {a b c d : ℤ} (hf : Supp f a b) (hg : Supp g c d) :
    Supp (f * g) (a + c) (b + d) := by
  classical
  intro p h
  have hp : p ∈ (f * g).support := Finsupp.mem_support_iff.mpr h
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (AddMonoidAlgebra.support_mul f g hp)
  have := hf x (Finsupp.mem_support_iff.mp hx)
  have := hg y (Finsupp.mem_support_iff.mp hy)
  omega

theorem widen {f : F[T;T⁻¹]} {a b a' b' : ℤ} (hf : Supp f a b) (ha : a' ≤ a) (hb : b ≤ b') :
    Supp f a' b' := by
  intro p h; have := hf p h; omega

end Supp

end Bppp
