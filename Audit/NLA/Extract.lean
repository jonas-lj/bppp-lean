import Audit.NLA.FoldLemmas

/-!
# The extraction proof for one NLA round

This file proves `extract_core`: 4 accepted responses give a witness, or a relation among the
generators.

Why it exists:
- `round_sound` in `Audit/NLA/Proofs.lean` applies `extract_core`.
- `extractVec` is the extractor's formula. `extractWit` in `Audit/NLA.lean` uses it. It needs
  `expand` and the weights `cWeight`. Reviewers check only that it is efficient.
- Otherwise, only proofs live here. The statements that we audit stay in `Audit/NLA.lean`.

How it works:
1. Each accepted response gives an opening of `C + γX + (γ² - 1)R` (`msm_expand`).
2. The openings at 3 challenges define a curve `A + tB + t²D`. It opens
   `C + tX + (t² - 1)R` at every `t`, so `A + D` opens `C`.
3. If the opening at the 4th challenge is not on the curve, the difference is a relation.
4. Else each pair of slots gives a cubic with 4 roots (`cubic_zero`). So the pairs fold honestly.
5. Then `σ` gives a quadratic with 4 roots, and `A + D` satisfies the relation.

Assumptions:
- `ρ ≠ 0`, and the norm length `k` is even.
- A padded slot of the linear part has no pair. Its entry of `odds c` is 0, so it adds nothing.
-/

namespace Audit.NLA

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-- Spreads `v` over the slots before a fold: slot `2i` gets `a * vᵢ`, and slot `2i + 1` gets
`b * vᵢ`. So `⟨v, a • [H]₀ + b • [H]₁⟩ = ⟨expand a b v, H⟩`. It does not undo `foldWit`. -/
def expand {m : ℕ} (a b : F) (v : Fin (half m) → F) : Fin m → F :=
  fun j => (if j.val % 2 = 0 then a else b) * v ⟨j.val / 2, by have := j.isLt; unfold half; omega⟩

/-! Tests: `expand` on an even length and an odd length. -/
example : expand (m := 4) (1 : ℚ) 5 ![1, 2] = ![1, 5, 2, 10] := by
  ext j; fin_cases j <;> simp [expand, Matrix.cons_val, half]
  norm_num
example : expand (m := 3) (1 : ℚ) 5 ![1, 2] = ![1, 5, 2] := by
  ext j; fin_cases j <;> simp [expand, Matrix.cons_val, half]

/-- The weight of the challenge `γ₀` that picks `C` out of `C + γX + (γ² - 1)R`, from the
challenges `γ₀`, `γ₁` and `γ₂`. -/
def cWeight (γ₀ γ₁ γ₂ : F) : F := (1 + γ₁ * γ₂) / ((γ₀ - γ₁) * (γ₀ - γ₂))

open Polynomial in
/-- A cubic with 4 distinct roots is zero. -/
theorem cubic_zero (t : Fin 4 → F) (ht : Function.Injective t) (a0 a1 a2 a3 : F)
    (h : ∀ i, a0 + a1 * t i + a2 * t i ^ 2 + a3 * t i ^ 3 = 0) :
    a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 := by
  set p : F[X] := C a0 + C a1 * X + C a2 * X ^ 2 + C a3 * X ^ 3
  have hp : p = 0 := by
    refine eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ ht.injOn ?_ ?_
    · rw [Finset.card_univ, Fintype.card_fin]
      refine lt_of_le_of_lt (degree_le_of_natDegree_le (p := p) (n := 3) ?_) (by decide)
      simp only [p]
      compute_degree!
    · intro i _
      simp [p, h i]
  have c : ∀ i, p.coeff i = 0 := fun i => by rw [hp, coeff_zero]
  have c0 := c 0
  have c1 := c 1
  have c2 := c 2
  have c3 := c 3
  simp [p, coeff_X, coeff_X_pow] at c0 c1 c2 c3
  exact ⟨c0, c1, c2, c3⟩

section Unfold

variable {m : ℕ}

theorem expand_even (a b : F) (v : Fin (half m) → F) (i : Fin (half m)) (h : 2 * i.val < m) :
    expand a b v ⟨2 * i.val, h⟩ = a * v i := by
  simp only [expand, show 2 * i.val % 2 = 0 by omega, ite_true]
  congr 2
  ext
  simp

theorem expand_odd (a b : F) (v : Fin (half m) → F) (i : Fin (half m))
    (h : 2 * i.val + 1 < m) : expand a b v ⟨2 * i.val + 1, h⟩ = b * v i := by
  simp only [expand, show (2 * i.val + 1) % 2 ≠ 0 by omega, ite_false]
  congr 2
  ext
  simp only
  omega

theorem pad_lt {α : Type} [Zero α] (v : Fin m → α) (j : Fin (2 * half m)) (h : j.val < m) :
    pad v j = v ⟨j.val, h⟩ := by
  simp [pad, h]

theorem pad_ge {α : Type} [Zero α] (v : Fin m → α) (j : Fin (2 * half m)) (h : ¬ j.val < m) :
    pad v j = 0 := by
  simp [pad, h]

/-- Step 1: a response over the folded generators is an opening over the old generators. -/
theorem msm_expand (a b : F) (v : Fin (half m) → F) (H : Fin m → E) :
    msm v (a • evens H + b • odds H) = msm (expand a b v) H := by
  rw [← msm_pad (expand a b v) H]
  simp only [msm, sum_split (fun j => pad (expand a b v) j • pad H j), evens_eq, odds_eq,
    Pi.add_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  have h0 : 2 * i.val < m := by unfold half at hi; omega
  rw [pad_lt (expand a b v) ⟨2 * i.val, by omega⟩ h0, pad_lt H ⟨2 * i.val, by omega⟩ h0,
    expand_even _ _ _ _ h0]
  by_cases h1 : 2 * i.val + 1 < m
  · rw [pad_lt (expand a b v) ⟨2 * i.val + 1, by omega⟩ h1, pad_lt H ⟨2 * i.val + 1, by omega⟩ h1,
      expand_odd _ _ _ _ h1]
    module
  · rw [pad_ge (expand a b v) ⟨2 * i.val + 1, by omega⟩ h1, pad_ge H ⟨2 * i.val + 1, by omega⟩ h1]
    module

end Unfold

/-- The point with the coordinates `o = (s, a, b)` over the generators `g`, `H` and `G`. -/
def pt {m k : ℕ} (g : E) (H : Fin m → E) (G : Fin k → E) (o : F × (Fin m → F) × (Fin k → F)) :
    E :=
  o.1 • g + msm o.2.1 H + msm o.2.2 G

section Pt

variable {m k : ℕ} (g : E) (H : Fin m → E) (G : Fin k → E)

theorem pt_add (o o' : F × (Fin m → F) × (Fin k → F)) :
    pt g H G (o + o') = pt g H G o + pt g H G o' := by
  simp only [pt, msm, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

theorem pt_smul (t : F) (o : F × (Fin m → F) × (Fin k → F)) :
    pt g H G (t • o) = t • pt g H G o := by
  simp only [pt, msm, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
    smul_add, Finset.smul_sum]

theorem pt_sub (o o' : F × (Fin m → F) × (Fin k → F)) :
    pt g H G (o - o') = pt g H G o - pt g H G o' := by
  simp only [pt, msm, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  abel

end Pt

/-- The extractor's formula. It is the weighted sum of the expanded responses at `γ 0`, `γ 1`
and `γ 2`, with the weights `cWeight`. It uses `O(m)` field operations. -/
def extractVec {m : ℕ} (a : F) (γ : Fin 4 → F) (v : Fin 4 → Fin (half m) → F) : Fin m → F :=
  cWeight (γ 0) (γ 1) (γ 2) • expand a (γ 0) (v 0)
    + cWeight (γ 1) (γ 0) (γ 2) • expand a (γ 1) (v 1)
    + cWeight (γ 2) (γ 0) (γ 1) • expand a (γ 2) (v 2)

/-- The core of `round_sound`, on the components of the instance. `hacc` is the verifier's check
for the response `(ℓ' i, n' i)` at the challenge `γ i`. -/
theorem extract_core {m k : ℕ} (g : E) (c : Fin m → F) (H : Fin m → E) (G : Fin k → E)
    (ρ : F) (hρ : ρ ≠ 0) (hk : k % 2 = 0) (C X R : E) (γ : Fin 4 → F)
    (hγ : Function.Injective γ) (ℓ' : Fin 4 → Fin (half m) → F)
    (n' : Fin 4 → Fin (half k) → F)
    (hacc : ∀ i, C + γ i • X + (γ i ^ 2 - 1) • R =
      (ip (evens c + γ i • odds c) (ℓ' i) + wip ((ρ ^ 2) ^ 2) (n' i) (n' i)) • g
        + msm (ℓ' i) (evens H + γ i • odds H) + msm (n' i) (ρ • evens G + γ i • odds G)) :
    (∃ (s : F) (a : Fin m → F) (b : Fin k → F),
      (s ≠ 0 ∨ a ≠ 0 ∨ b ≠ 0) ∧ s • g + msm a H + msm b G = 0) ∨
    C = (ip c (extractVec 1 γ ℓ') + wip (ρ ^ 2) (extractVec ρ γ n') (extractVec ρ γ n')) • g
      + msm (extractVec 1 γ ℓ') H + msm (extractVec ρ γ n') G := by
  unfold extractVec
  classical
  have hne : ∀ i j : Fin 4, i ≠ j → γ i - γ j ≠ 0 := fun i j hij =>
    sub_ne_zero.mpr fun e => hij (hγ e)
  have s01 := hne 0 1 (by decide)
  have s02 := hne 0 2 (by decide)
  have s12 := hne 1 2 (by decide)
  have s10 := hne 1 0 (by decide)
  have s20 := hne 2 0 (by decide)
  have s21 := hne 2 1 (by decide)
  -- Step 1: the openings of `C + γ i X + (γ i² - 1) R`.
  obtain ⟨o, ho⟩ : ∃ o : Fin 4 → F × (Fin m → F) × (Fin k → F), o = fun i =>
      (ip (evens c + γ i • odds c) (ℓ' i) + wip ((ρ ^ 2) ^ 2) (n' i) (n' i),
        expand 1 (γ i) (ℓ' i), expand ρ (γ i) (n' i)) := ⟨_, rfl⟩
  have ho0 : ∀ i, (o i).1 = ip (evens c + γ i • odds c) (ℓ' i) + wip ((ρ ^ 2) ^ 2) (n' i) (n' i) :=
    fun i => by rw [ho]
  have ho1 : ∀ i, (o i).2.1 = expand 1 (γ i) (ℓ' i) := fun i => by rw [ho]
  have ho2 : ∀ i, (o i).2.2 = expand ρ (γ i) (n' i) := fun i => by rw [ho]
  have hV : ∀ i, pt g H G (o i) = C + γ i • X + (γ i ^ 2 - 1) • R := fun i => by
    rw [hacc i, pt, ho0, ho1, ho2, ← msm_expand, ← msm_expand, one_smul]
  -- Step 2: the curve `A + t B + t² D` through the openings at `γ 0`, `γ 1` and `γ 2`.
  obtain ⟨A, hA⟩ : ∃ A : F × (Fin m → F) × (Fin k → F),
      A = (γ 1 * γ 2 / ((γ 0 - γ 1) * (γ 0 - γ 2))) • o 0
        + (γ 0 * γ 2 / ((γ 1 - γ 0) * (γ 1 - γ 2))) • o 1
        + (γ 0 * γ 1 / ((γ 2 - γ 0) * (γ 2 - γ 1))) • o 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : F × (Fin m → F) × (Fin k → F),
      B = (-(γ 1 + γ 2) / ((γ 0 - γ 1) * (γ 0 - γ 2))) • o 0
        + (-(γ 0 + γ 2) / ((γ 1 - γ 0) * (γ 1 - γ 2))) • o 1
        + (-(γ 0 + γ 1) / ((γ 2 - γ 0) * (γ 2 - γ 1))) • o 2 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : F × (Fin m → F) × (Fin k → F),
      D = (1 / ((γ 0 - γ 1) * (γ 0 - γ 2))) • o 0
        + (1 / ((γ 1 - γ 0) * (γ 1 - γ 2))) • o 1
        + (1 / ((γ 2 - γ 0) * (γ 2 - γ 1))) • o 2 := ⟨_, rfl⟩
  have hP0 : A + γ 0 • B + γ 0 ^ 2 • D = o 0 := by
    rw [hA, hB, hD]; match_scalars <;> field_simp <;> ring
  have hP1 : A + γ 1 • B + γ 1 ^ 2 • D = o 1 := by
    rw [hA, hB, hD]; match_scalars <;> field_simp <;> ring
  have hP2 : A + γ 2 • B + γ 2 ^ 2 • D = o 2 := by
    rw [hA, hB, hD]; match_scalars <;> field_simp <;> ring
  have hptA : pt g H G A = C - R := by
    rw [hA]; simp only [pt_add, pt_smul, hV]; match_scalars <;> field_simp <;> ring
  have hptB : pt g H G B = X := by
    rw [hB]; simp only [pt_add, pt_smul, hV]; match_scalars <;> field_simp <;> ring
  have hptD : pt g H G D = R := by
    rw [hD]; simp only [pt_add, pt_smul, hV]; match_scalars <;> field_simp <;> ring
  -- Step 3: the opening at `γ 3` is on the curve, or the difference is a relation.
  by_cases h3 : o 3 = A + γ 3 • B + γ 3 ^ 2 • D
  swap
  · left
    refine ⟨(A + γ 3 • B + γ 3 ^ 2 • D - o 3).1, (A + γ 3 • B + γ 3 ^ 2 • D - o 3).2.1,
      (A + γ 3 • B + γ 3 ^ 2 • D - o 3).2.2, ?_, ?_⟩
    · by_contra hc
      push Not at hc
      apply h3
      have h0 : A + γ 3 • B + γ 3 ^ 2 • D - o 3 = 0 := Prod.ext hc.1 (Prod.ext hc.2.1 hc.2.2)
      exact (sub_eq_zero.mp h0).symm
    · change pt g H G _ = 0
      rw [pt_sub, pt_add, pt_add, pt_smul, pt_smul, hptA, hptB, hptD, hV]
      module
  right
  have hall : ∀ i, o i = A + γ i • B + γ i ^ 2 • D := by
    intro i
    fin_cases i
    exacts [hP0.symm, hP1.symm, hP2.symm, h3]
  have hl : ∀ i j, expand 1 (γ i) (ℓ' i) j = A.2.1 j + γ i * B.2.1 j + γ i ^ 2 * D.2.1 j :=
    fun i j => by rw [← ho1, hall i]; simp
  have hn : ∀ i j, expand ρ (γ i) (n' i) j = A.2.2 j + γ i * B.2.2 j + γ i ^ 2 * D.2.2 j :=
    fun i j => by rw [← ho2, hall i]; simp
  have hs : ∀ i, ip (evens c + γ i • odds c) (ℓ' i) + wip ((ρ ^ 2) ^ 2) (n' i) (n' i)
      = A.1 + γ i * B.1 + γ i ^ 2 * D.1 :=
    fun i => by rw [← ho0, hall i]; simp
  -- Step 4: each pair of slots folds honestly.
  have lm : ∀ t : Fin (half m), 2 * t.val < m := fun t => by
    have := t.isLt; unfold half at this; omega
  have lk0 : ∀ t : Fin (half k), 2 * t.val < k := fun t => by
    have := t.isLt; unfold half at this; omega
  have lk1 : ∀ t : Fin (half k), 2 * t.val + 1 < k := fun t => by
    have := t.isLt; unfold half at this; omega
  have hH : ∀ (t : Fin (half m)) (h1 : 2 * t.val + 1 < m),
      D.2.1 ⟨2 * t.val, lm t⟩ = 0 ∧ A.2.1 ⟨2 * t.val + 1, h1⟩ = 0 ∧
      D.2.1 ⟨2 * t.val + 1, h1⟩ = B.2.1 ⟨2 * t.val, lm t⟩ := by
    intro t h1
    obtain ⟨a0, -, a2, a3⟩ := cubic_zero γ hγ (-A.2.1 ⟨2 * t.val + 1, h1⟩)
      (A.2.1 ⟨2 * t.val, lm t⟩ - B.2.1 ⟨2 * t.val + 1, h1⟩)
      (B.2.1 ⟨2 * t.val, lm t⟩ - D.2.1 ⟨2 * t.val + 1, h1⟩) (D.2.1 ⟨2 * t.val, lm t⟩) fun i => by
        have e0 := hl i ⟨2 * t.val, lm t⟩
        have e1 := hl i ⟨2 * t.val + 1, h1⟩
        rw [expand_even] at e0
        rw [expand_odd] at e1
        linear_combination e1 - γ i * e0
    exact ⟨a3, by linear_combination -a0, by linear_combination -a2⟩
  have hG : ∀ t : Fin (half k),
      D.2.2 ⟨2 * t.val, lk0 t⟩ = 0 ∧ A.2.2 ⟨2 * t.val + 1, lk1 t⟩ = 0 ∧
      ρ * D.2.2 ⟨2 * t.val + 1, lk1 t⟩ = B.2.2 ⟨2 * t.val, lk0 t⟩ := by
    intro t
    obtain ⟨a0, -, a2, a3⟩ := cubic_zero γ hγ (-ρ * A.2.2 ⟨2 * t.val + 1, lk1 t⟩)
      (A.2.2 ⟨2 * t.val, lk0 t⟩ - ρ * B.2.2 ⟨2 * t.val + 1, lk1 t⟩)
      (B.2.2 ⟨2 * t.val, lk0 t⟩ - ρ * D.2.2 ⟨2 * t.val + 1, lk1 t⟩) (D.2.2 ⟨2 * t.val, lk0 t⟩)
      fun i => by
        have e0 := hn i ⟨2 * t.val, lk0 t⟩
        have e1 := hn i ⟨2 * t.val + 1, lk1 t⟩
        rw [expand_even] at e0
        rw [expand_odd] at e1
        linear_combination ρ * e1 - γ i * e0
    refine ⟨a3, ?_, by linear_combination -a2⟩
    have : ρ * A.2.2 ⟨2 * t.val + 1, lk1 t⟩ = 0 := by linear_combination -a0
    exact (mul_eq_zero.mp this).resolve_left hρ
  -- A padded slot has no pair, but its entry of `odds c` is 0.
  have hpad : ∀ t : Fin (half m), odds c t * D.2.1 ⟨2 * t.val, lm t⟩ = 0 := by
    intro t
    by_cases h1 : 2 * t.val + 1 < m
    · rw [(hH t h1).1, mul_zero]
    · simp [odds, h1]
  -- Step 5: `σ` is a quadratic in `γ` with 4 roots.
  set W : Fin (half k) → F := fun t => ((ρ ^ 2) ^ 2) ^ (t.val + 1) with hW
  set q0 := A.1 - ∑ t, evens c t * A.2.1 ⟨2 * t.val, lm t⟩
    - ∑ t, W t * (A.2.2 ⟨2 * t.val, lk0 t⟩ / ρ) ^ 2 with hq0
  set q1 := B.1 - ∑ t, (evens c t * B.2.1 ⟨2 * t.val, lm t⟩ + odds c t * A.2.1 ⟨2 * t.val, lm t⟩)
    - ∑ t, W t * (2 * A.2.2 ⟨2 * t.val, lk0 t⟩ * B.2.2 ⟨2 * t.val, lk0 t⟩ / ρ ^ 2) with hq1
  set q2 := D.1 - ∑ t, (evens c t * D.2.1 ⟨2 * t.val, lm t⟩ + odds c t * B.2.1 ⟨2 * t.val, lm t⟩)
    - ∑ t, W t * (B.2.2 ⟨2 * t.val, lk0 t⟩ / ρ) ^ 2 with hq2
  have hq : ∀ i, q0 + q1 * γ i + q2 * γ i ^ 2 + 0 * γ i ^ 3 = 0 := by
    intro i
    have hli : ∀ t, ℓ' i t = A.2.1 ⟨2 * t.val, lm t⟩ + γ i * B.2.1 ⟨2 * t.val, lm t⟩
        + γ i ^ 2 * D.2.1 ⟨2 * t.val, lm t⟩ := fun t => by
      have := hl i ⟨2 * t.val, lm t⟩
      rwa [expand_even, one_mul] at this
    have hni : ∀ t, n' i t = (A.2.2 ⟨2 * t.val, lk0 t⟩ + γ i * B.2.2 ⟨2 * t.val, lk0 t⟩) / ρ :=
      fun t => by
        have := hn i ⟨2 * t.val, lk0 t⟩
        rw [expand_even, (hG t).1] at this
        field_simp
        linear_combination this
    have hip : ip (evens c + γ i • odds c) (ℓ' i) = ∑ t, evens c t * A.2.1 ⟨2 * t.val, lm t⟩
        + γ i * ∑ t, (evens c t * B.2.1 ⟨2 * t.val, lm t⟩ + odds c t * A.2.1 ⟨2 * t.val, lm t⟩)
        + γ i ^ 2 * ∑ t, (evens c t * D.2.1 ⟨2 * t.val, lm t⟩
          + odds c t * B.2.1 ⟨2 * t.val, lm t⟩) := by
      simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hli t]
      linear_combination γ i ^ 3 * hpad t
    have hwip : wip ((ρ ^ 2) ^ 2) (n' i) (n' i) = ∑ t, W t * (A.2.2 ⟨2 * t.val, lk0 t⟩ / ρ) ^ 2
        + γ i * ∑ t, W t * (2 * A.2.2 ⟨2 * t.val, lk0 t⟩ * B.2.2 ⟨2 * t.val, lk0 t⟩ / ρ ^ 2)
        + γ i ^ 2 * ∑ t, W t * (B.2.2 ⟨2 * t.val, lk0 t⟩ / ρ) ^ 2 := by
      simp only [wip, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hni t, hW]
      field_simp
      ring
    have := hs i
    rw [hip, hwip] at this
    rw [hq0, hq1, hq2]
    linear_combination -this
  obtain ⟨z0, -, z2, -⟩ := cubic_zero γ hγ q0 q1 q2 0 hq
  -- The extractor is `A + D`, the opening of `C`.
  have hext : cWeight (γ 0) (γ 1) (γ 2) • o 0 + cWeight (γ 1) (γ 0) (γ 2) • o 1
      + cWeight (γ 2) (γ 0) (γ 1) • o 2 = A + D := by
    rw [hA, hD]; simp only [cWeight]; match_scalars <;> field_simp <;> ring
  have hℓC : cWeight (γ 0) (γ 1) (γ 2) • expand 1 (γ 0) (ℓ' 0)
      + cWeight (γ 1) (γ 0) (γ 2) • expand 1 (γ 1) (ℓ' 1)
      + cWeight (γ 2) (γ 0) (γ 1) • expand 1 (γ 2) (ℓ' 2) = (A + D).2.1 := by
    rw [← hext]; simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, ho1]
  have hnC : cWeight (γ 0) (γ 1) (γ 2) • expand ρ (γ 0) (n' 0)
      + cWeight (γ 1) (γ 0) (γ 2) • expand ρ (γ 1) (n' 1)
      + cWeight (γ 2) (γ 0) (γ 1) • expand ρ (γ 2) (n' 2) = (A + D).2.2 := by
    rw [← hext]; simp only [Prod.snd_add, Prod.smul_snd, ho2]
  rw [hℓC, hnC]
  have hC : pt g H G (A + D) = C := by rw [pt_add, hptA, hptD, sub_add_cancel]
  -- `σ` of `A + D` is `⟨c, ℓ⟩ + ‖n‖²_μ`.
  have hipC : ip c (A + D).2.1 = ∑ t, evens c t * A.2.1 ⟨2 * t.val, lm t⟩
      + ∑ t, (evens c t * D.2.1 ⟨2 * t.val, lm t⟩ + odds c t * B.2.1 ⟨2 * t.val, lm t⟩) := by
    rw [← ip_pad, ip, sum_split (fun j => pad c j * pad (A + D).2.1 j), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← evens_eq, ← odds_eq, pad_lt _ _ (lm t)]
    have e0 : (A + D).2.1 ⟨2 * t.val, lm t⟩ = A.2.1 ⟨2 * t.val, lm t⟩ + D.2.1 ⟨2 * t.val, lm t⟩ :=
      rfl
    by_cases h1 : 2 * t.val + 1 < m
    · have e1 : (A + D).2.1 ⟨2 * t.val + 1, h1⟩
          = A.2.1 ⟨2 * t.val + 1, h1⟩ + D.2.1 ⟨2 * t.val + 1, h1⟩ := rfl
      rw [pad_lt _ _ h1, e0, e1, (hH t h1).2.1, (hH t h1).2.2]
      ring
    · rw [pad_ge _ _ h1, e0, show odds c t = 0 by simp [odds, h1]]
      ring
  have hwipC : wip (ρ ^ 2) (A + D).2.2 (A + D).2.2
      = ∑ t, W t * (A.2.2 ⟨2 * t.val, lk0 t⟩ / ρ) ^ 2 + ∑ t, W t * (B.2.2 ⟨2 * t.val, lk0 t⟩ / ρ) ^ 2 := by
    rw [← wip_pad, wip, sum_split (fun j : Fin (2 * half k) =>
      (ρ ^ 2) ^ (j.val + 1) * (pad (A + D).2.2 j * pad (A + D).2.2 j)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pad_lt _ _ (lk0 t), pad_lt _ _ (lk1 t)]
    simp only [Prod.snd_add, Pi.add_apply, (hG t).1, (hG t).2.1, hW]
    have hd := (hG t).2.2
    have hd' : D.2.2 ⟨2 * t.val + 1, lk1 t⟩ = B.2.2 ⟨2 * t.val, lk0 t⟩ / ρ := by
      field_simp; linear_combination hd
    rw [hd']
    field_simp
    ring
  have hσ : (A + D).1 = ip c (A + D).2.1 + wip (ρ ^ 2) (A + D).2.2 (A + D).2.2 := by
    rw [hipC, hwipC, Prod.fst_add]
    linear_combination z0 + z2
  rw [← hσ]
  exact hC.symm

end Audit.NLA
