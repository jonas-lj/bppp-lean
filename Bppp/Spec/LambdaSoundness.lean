import Bppp.Spec.CircuitSoundness

/-!
# The `λ` level of the circuit extractor

For any opening, the `T³` coefficient of `f(T)`, the value row (29), is a polynomial in `λ` whose
coefficients are the rows (35): the degree-0 residue `E_0 + L_0`, the value links `L_i`, set
membership `S` and the shape rows. Forking `λ` forces every row to vanish.
-/

open Finset LaurentPolynomial

namespace Bppp.Spec

variable {F : Type*} [Field F] (P : Params) (ch : Challenges F)

/-- The value row (29) for any opening. -/
theorem coeff3_f (hδ : ch.δ ≠ 0) (w : Opening F) : coeff 3 (f P ch w) =
    2 * (lamAl P ch + muAm P ch) + w.vhat -
    2 * ∑ k ∈ range P.nm, ch.μ ^ (k + 1) * (ch.δ * w.nO k * w.nV k + w.nO k * cnO P ch k +
      cnV P ch k * w.nV k + w.nL k * w.nR k + w.nL k * cnL P ch k + cnR P ch k * w.nR k) -
    ch.β * (ch.δ * w.rO 4 + w.rL 3 + w.rR 2) - ∑ s ∈ range 8, clV P ch s * lin w.rV w.ℓV s := by
  have hcl : coeff 3 (∑ s ∈ range 8, c P ch s * ℓ ch w s) =
      ch.β * (ch.δ * w.rO 4 + w.rL 3 + w.rR 2) + ∑ s ∈ range 8, clV P ch s * lin w.rV w.ℓV s := by
    simp only [sum_range_succ, sum_range_zero, c, ℓ, e, lin]
    norm_num [add_mul, mul_add, mono_mul]
    ring
  simp only [f, σ, ps, map_sub, map_add, hcl, coeff3_normμ, n_eq, pn_eq, coeff3_sq, coeff_mono]
  norm_num
  rw [mul_sum]
  have hsum : ∀ k ∈ range P.nm, ch.μ ^ (k + 1) * (2 * (cnV P ch k * (ch.δ⁻¹ * cnO P ch k) +
      cnR P ch k * cnL P ch k)) - ch.μ ^ (k + 1) * (2 * ((ch.δ * w.nO k + cnV P ch k) *
        (w.nV k + ch.δ⁻¹ * cnO P ch k) + (w.nL k + cnR P ch k) * (w.nR k + cnL P ch k))) =
      -(2 * (ch.μ ^ (k + 1) * (ch.δ * w.nO k * w.nV k + w.nO k * cnO P ch k +
        cnV P ch k * w.nV k + w.nL k * w.nR k + w.nL k * cnL P ch k + cnR P ch k * w.nR k))) :=
    fun k _ => by field_simp; ring
  have key := sum_congr rfl hsum
  rw [sum_sub_distrib, sum_neg_distrib] at key
  linear_combination key

/-! ## The rows (35)

`w` supplies the openings of `C_O`, `C_L`, `C_R`, and `u`, `h`, `n` the coordinates of the inputs
`V_i` on `g`, `H` and `G`. None depends on `λ`. -/

section Rows

variable (w : Opening F) (u : ℕ → F) (h n : ℕ → ℕ → F)

/-- The part of the `λ⁰` coefficient outside the first value link. -/
noncomputable def rowE0 : F :=
  2 * muAm P ch - 2 * ∑ k ∈ range P.nm, ch.μ ^ (k + 1) *
    (w.nL k * w.nR k + if k < P.Nd then ch.α * w.nR k else 0) -
  ch.β * (ch.δ * w.rO 4 + w.rL 3 + w.rR 2)

/-- The value link of input `i`, scaled by `2`. -/
noncomputable def rowL (i : ℕ) : F :=
  2 * u i - 4 * ch.δ * ∑ k ∈ range P.nm, ch.μ ^ (k + 1) * (w.nO k * n i k) -
    2 * ∑ t ∈ range P.D, 16 ^ t * w.nL (i * P.D + t)

/-- Set membership, scaled by `2`. -/
noncomputable def rowS : F :=
  2 * P.Nd / ch.α - 2 * ∑ k ∈ range P.nm,
    ((if k ≤ 14 then w.nO k * (((k : F) + 1) / (ch.α * (ch.α + ((k : F) + 1)))) else 0) +
      if k < P.Nd then w.nR k else 0)

/-- The shape row of coordinate `j` of input `i`: `G_j` for `j < nm`, else `H_{j-nm+1}`. -/
noncomputable def rowR (j i : ℕ) : F := if j < P.nm then -4 * n i j else -2 * h i (j - P.nm + 1)

end Rows

theorem pieceO (hμ : ch.μ ≠ 0) (w : Opening F) :
    ∑ k ∈ range P.nm, ch.μ ^ (k + 1) * (w.nO k * cnO P ch k) = ch.lam ^ P.M * ∑ k ∈ range P.nm,
      (if k ≤ 14 then w.nO k * (((k : F) + 1) / (ch.α * (ch.α + ((k : F) + 1)))) else 0) := by
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have := pow_ne_zero (k + 1) hμ
  simp only [cnO]
  split_ifs
  · field_simp
  · simp

theorem pieceR (hμ : ch.μ ≠ 0) (w : Opening F) :
    ∑ k ∈ range P.nm, ch.μ ^ (k + 1) * (cnR P ch k * w.nR k) =
      ch.lam ^ P.M * ∑ k ∈ range P.nm, (if k < P.Nd then w.nR k else 0) +
        ∑ k ∈ range P.nm, ch.μ ^ (k + 1) * (if k < P.Nd then ch.α * w.nR k else 0) := by
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  have := pow_ne_zero (k + 1) hμ
  simp only [cnR]
  split_ifs
  · field_simp
  · simp

theorem pieceL (hμ : ch.μ ≠ 0) (w : Opening F) :
    ∑ k ∈ range P.nm, ch.μ ^ (k + 1) * (w.nL k * cnL P ch k) =
      ∑ i ∈ range P.M, ch.lam ^ i * ∑ t ∈ range P.D, 16 ^ t * w.nL (i * P.D + t) := by
  rw [sum_range_of_le (m := P.Nd) P.hnm fun k hk => by simp [cnL]; omega]
  rw [sum_congr rfl fun k hk => show ch.μ ^ (k + 1) * (w.nL k * cnL P ch k) =
      ch.lam ^ (k / P.D) * (16 ^ (k % P.D) * w.nL (k / P.D * P.D + k % P.D)) by
    have hk := mem_range.mp hk
    have := pow_ne_zero (k + 1) hμ
    rw [Nat.div_add_mod']
    simp only [cnL, if_pos hk]
    field_simp]
  rw [show P.Nd = P.M * P.D from rfl, sum_range_mul_div_mod P.M P.D fun i t =>
    ch.lam ^ i * (16 ^ t * w.nL (i * P.D + t))]
  simp [mul_sum]

section Inputs

variable (w : Opening F) (u : ℕ → F) (h n : ℕ → ℕ → F)

theorem pieceV (hμ : ch.μ ≠ 0) (hn : ∀ k < P.nm, w.nV k = 2 * ∑ i ∈ range P.M, ch.lam ^ i * n i k) :
    ∑ k ∈ range P.nm, ch.μ ^ (k + 1) * (cnV P ch k * w.nV k) =
      ∑ j ∈ range P.nm, ∑ i ∈ range P.M, ch.lam ^ (P.M * (j + 1) + 1 + i) * (2 * n i j) := by
  refine sum_congr rfl fun k hk => ?_
  have := pow_ne_zero (k + 1) hμ
  rw [hn k (mem_range.mp hk)]
  simp only [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  simp only [cnV, pow_add]
  field_simp

theorem pieceOV (hn : ∀ k < P.nm, w.nV k = 2 * ∑ i ∈ range P.M, ch.lam ^ i * n i k) :
    ∑ k ∈ range P.nm, ch.μ ^ (k + 1) * (ch.δ * w.nO k * w.nV k) = 2 * ch.δ *
      ∑ i ∈ range P.M, ch.lam ^ i * ∑ k ∈ range P.nm, ch.μ ^ (k + 1) * (w.nO k * n i k) := by
  rw [sum_congr rfl fun k hk => by rw [hn k (mem_range.mp hk)]]
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun k _ => sum_congr rfl fun i _ => by ring

theorem pieceH (hl : ∀ s < 8, lin w.rV w.ℓV s = 2 * ∑ i ∈ range P.M, ch.lam ^ i * h i s) :
    ∑ s ∈ range 8, clV P ch s * lin w.rV w.ℓV s =
      ∑ s ∈ range 7, ∑ i ∈ range P.M,
        ch.lam ^ (P.M * (P.nm + s + 1) + 1 + i) * (2 * h i (s + 1)) := by
  rw [sum_range_succ']
  simp only [clV, if_pos, zero_mul, add_zero, Nat.succ_ne_zero, if_false]
  refine sum_congr rfl fun s hs => ?_
  rw [hl (s + 1) (by simp at hs; omega), mul_sum, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  simp only [Params.g, pow_add]
  ring

theorem shape_sum : ∑ j ∈ range (P.nm + 7), ∑ i ∈ range P.M,
    ch.lam ^ (P.M * (j + 1) + 1 + i) * rowR P h n j i =
    -(2 * ∑ j ∈ range P.nm, ∑ i ∈ range P.M, ch.lam ^ (P.M * (j + 1) + 1 + i) * (2 * n i j)) -
      ∑ s ∈ range 7, ∑ i ∈ range P.M,
        ch.lam ^ (P.M * (P.nm + s + 1) + 1 + i) * (2 * h i (s + 1)) := by
  rw [sum_range_add, mul_sum, ← sum_neg_distrib, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  · refine sum_congr rfl fun j hj => ?_
    rw [mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    simp only [rowR, if_pos (mem_range.mp hj)]; ring
  · refine sum_congr rfl fun s _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    simp only [rowR, show ¬ P.nm + s < P.nm by omega, if_false,
      show P.nm + s - P.nm + 1 = s + 1 by omega, show P.nm + s + 1 = P.nm + (s + 1) by omega]
    ring

/-- The value row as a polynomial in `λ` with the rows (35) as coefficients, when `V̂` opens to
the `λ`-combination of the input coordinates. -/
theorem coeff3_rows (hδ : ch.δ ≠ 0) (hμ : ch.μ ≠ 0)
    (hv : w.vhat = 2 * ∑ i ∈ range P.M, ch.lam ^ i * u i)
    (hl : ∀ s < 8, lin w.rV w.ℓV s = 2 * ∑ i ∈ range P.M, ch.lam ^ i * h i s)
    (hn : ∀ k < P.nm, w.nV k = 2 * ∑ i ∈ range P.M, ch.lam ^ i * n i k) :
    coeff 3 (f P ch w) = rowE0 P ch w + ∑ i ∈ range P.M, ch.lam ^ i * rowL P ch w u n i +
      ch.lam ^ P.M * rowS P ch w + ∑ j ∈ range (P.nm + 7), ∑ i ∈ range P.M,
        ch.lam ^ (P.M * (j + 1) + 1 + i) * rowR P h n j i := by
  rw [coeff3_f P ch hδ, shape_sum]
  simp only [mul_add, sum_add_distrib]
  rw [pieceO P ch hμ, pieceR P ch hμ, pieceL P ch hμ, pieceV P ch w n hμ hn, pieceOV P ch w n hn,
    pieceH P ch w h hl, hv]
  have hL : ∑ i ∈ range P.M, ch.lam ^ i * rowL P ch w u n i =
      2 * ∑ i ∈ range P.M, ch.lam ^ i * u i - 4 * ch.δ * ∑ i ∈ range P.M, ch.lam ^ i *
        ∑ k ∈ range P.nm, ch.μ ^ (k + 1) * (w.nO k * n i k) -
      2 * ∑ i ∈ range P.M, ch.lam ^ i * ∑ t ∈ range P.D, 16 ^ t * w.nL (i * P.D + t) := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by simp only [rowL]; ring
  rw [hL]
  simp only [rowE0, rowS, lamAl, mul_add, sum_add_distrib]
  ring_nf
  simp only [mul_comm P.D]
  ring
end Inputs

/-! ## Vanishing of the rows -/

theorem shape_exp_inj {M j j' i i' : ℕ} (hi : i < M) (hi' : i' < M)
    (h : M * (j + 1) + 1 + i = M * (j' + 1) + 1 + i') : j = j' ∧ i = i' := by
  rcases lt_trichotomy j j' with hj | rfl | hj
  · have : M * (j + 2) ≤ M * (j' + 1) := Nat.mul_le_mul_left _ (by omega)
    have : M * (j + 2) = M * (j + 1) + M := by ring
    omega
  · omega
  · have : M * (j' + 2) ≤ M * (j + 1) := Nat.mul_le_mul_left _ (by omega)
    have : M * (j' + 2) = M * (j' + 1) + M := by ring
    omega

open Polynomial in
/-- If the polynomial in `λ` with the rows as coefficients vanishes at `M(nm+8)+1` distinct
points, every row vanishes, the degree-0 one together with the first value link. -/
theorem rows_zero (hM : 0 < P.M) (E0 S : F) (L : ℕ → F) (R : ℕ → ℕ → F)
    (x : Fin (P.M * (P.nm + 8) + 1) → F) (hx : Function.Injective x)
    (h : ∀ r, E0 + ∑ i ∈ range P.M, x r ^ i * L i + x r ^ P.M * S + ∑ j ∈ range (P.nm + 7),
      ∑ i ∈ range P.M, x r ^ (P.M * (j + 1) + 1 + i) * R j i = 0) :
    E0 + L 0 = 0 ∧ (∀ i, 1 ≤ i → i < P.M → L i = 0) ∧ S = 0 ∧
      ∀ j < P.nm + 7, ∀ i < P.M, R j i = 0 := by
  set Q : F[X] := Polynomial.C E0 + ∑ i ∈ range P.M, Polynomial.C (L i) * X ^ i +
    Polynomial.C S * X ^ P.M + ∑ j ∈ range (P.nm + 7), ∑ i ∈ range P.M, Polynomial.C (R j i) * X ^ (P.M * (j + 1) + 1 + i)
  have hMj : ∀ j, P.M ≤ P.M * (j + 1) := fun j => Nat.le_mul_of_pos_right _ (by omega)
  have hco : ∀ d, Q.coeff d = (if d = 0 then E0 else 0) +
      ∑ i ∈ range P.M, (if d = i then L i else 0) + (if d = P.M then S else 0) +
      ∑ j ∈ range (P.nm + 7), ∑ i ∈ range P.M,
        (if d = P.M * (j + 1) + 1 + i then R j i else 0) := fun d => by
    simp only [Q, coeff_add, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_C, mul_ite, mul_one,
      mul_zero]
  have hQ : Q = 0 := by
    refine eq_zero_of_degree_lt_of_eval_index_eq_zero univ hx.injOn ?_ fun r _ => ?_
    · rw [card_univ, Fintype.card_fin, degree_lt_iff_coeff_zero]
      intro d hd
      have hd : P.M * (P.nm + 8) + 1 ≤ d := by exact_mod_cast hd
      have hle : ∀ j < P.nm + 7, P.M * (j + 1) + P.M ≤ P.M * (P.nm + 8) := fun j hj => by
        have : P.M * (j + 2) ≤ P.M * (P.nm + 8) := Nat.mul_le_mul_left _ (by omega)
        have : P.M * (j + 2) = P.M * (j + 1) + P.M := by ring
        omega
      have : P.M ≤ P.M * (P.nm + 8) := Nat.le_mul_of_pos_right _ (by omega)
      rw [hco, if_neg (by omega), if_neg (by omega)]
      rw [sum_eq_zero fun i hi => if_neg (by simp at hi; omega),
        sum_eq_zero fun j hj => sum_eq_zero fun i hi => if_neg (by
          simp at hi hj; have := hle j hj; omega)]
      simp
    · simp only [Q, eval_add, eval_C, eval_finsetSum, eval_mul, eval_pow, eval_X]
      simpa only [mul_comm] using h r
  have c : ∀ d, Q.coeff d = 0 := fun d => by rw [hQ, coeff_zero]
  have hsh : ∀ d < P.M + 1, ∑ j ∈ range (P.nm + 7), ∑ i ∈ range P.M,
      (if d = P.M * (j + 1) + 1 + i then R j i else 0) = 0 := fun d hd =>
    sum_eq_zero fun j _ => sum_eq_zero fun i _ => if_neg (by have := hMj j; omega)
  refine ⟨?_, fun i hi1 hi => ?_, ?_, fun j hj i hi => ?_⟩
  · have := c 0
    rw [hco, hsh 0 (by omega), if_pos rfl, if_neg (by omega), sum_ite_eq] at this
    simpa [hM] using this
  · have := c i
    rw [hco, hsh i (by omega), if_neg (by omega), if_neg (by omega), sum_ite_eq] at this
    simpa [hi] using this
  · have := c P.M
    rw [hco, hsh P.M (by omega), if_neg (by omega), if_pos rfl,
      sum_eq_zero fun i hi => if_neg (by simp at hi; omega)] at this
    simpa using this
  · have hj1 := hMj j
    have := c (P.M * (j + 1) + 1 + i)
    rw [hco, if_neg (by omega), if_neg (by omega),
      sum_eq_zero fun i' hi' => if_neg (by simp at hi'; omega), sum_eq_single j, sum_eq_single i]
      at this
    · simpa using this
    · intro i' hi' hne; exact if_neg fun e => hne (shape_exp_inj hi (by simpa using hi') e).2.symm
    · intro hi'; exact absurd (mem_range.mpr hi) hi'
    · intro j' hj' hne
      exact sum_eq_zero fun i' hi' => if_neg fun e =>
        hne (shape_exp_inj hi (by simpa using hi') e).1.symm
    · intro hj'; exact absurd (mem_range.mpr hj) hj'

/-- The rows depend on the opening only through `n_O`, `n_L`, `n_R` and three blindings. -/
theorem rows_congr {w w' : Opening F} (hO : ∀ k < P.nm, w.nO k = w'.nO k)
    (hL : ∀ k < P.nm, w.nL k = w'.nL k) (hR : ∀ k < P.nm, w.nR k = w'.nR k)
    (hrO : w.rO 4 = w'.rO 4) (hrL : w.rL 3 = w'.rL 3) (hrR : w.rR 2 = w'.rR 2) :
    rowE0 P ch w = rowE0 P ch w' ∧ rowS P ch w = rowS P ch w' ∧
      ∀ (u : ℕ → F) (n : ℕ → ℕ → F), ∀ i < P.M, rowL P ch w u n i = rowL P ch w' u n i := by
  refine ⟨?_, ?_, fun u n i hi => ?_⟩
  · have : ∑ k ∈ range P.nm, ch.μ ^ (k + 1) *
        (w.nL k * w.nR k + if k < P.Nd then ch.α * w.nR k else 0) =
        ∑ k ∈ range P.nm, ch.μ ^ (k + 1) *
        (w'.nL k * w'.nR k + if k < P.Nd then ch.α * w'.nR k else 0) :=
      sum_congr rfl fun k hk => by rw [hL k (mem_range.1 hk), hR k (mem_range.1 hk)]
    simp only [rowE0, this, hrO, hrL, hrR]
  · have : ∑ k ∈ range P.nm,
        ((if k ≤ 14 then w.nO k * (((k : F) + 1) / (ch.α * (ch.α + ((k : F) + 1)))) else 0) +
          if k < P.Nd then w.nR k else 0) = ∑ k ∈ range P.nm,
        ((if k ≤ 14 then w'.nO k * (((k : F) + 1) / (ch.α * (ch.α + ((k : F) + 1)))) else 0) +
          if k < P.Nd then w'.nR k else 0) :=
      sum_congr rfl fun k hk => by rw [hO k (mem_range.1 hk), hR k (mem_range.1 hk)]
    simp only [rowS, this]
  · have h1 : ∑ k ∈ range P.nm, ch.μ ^ (k + 1) * (w.nO k * n i k) =
        ∑ k ∈ range P.nm, ch.μ ^ (k + 1) * (w'.nO k * n i k) :=
      sum_congr rfl fun k hk => by rw [hO k (mem_range.1 hk)]
    have h2 : ∑ t ∈ range P.D, 16 ^ t * w.nL (i * P.D + t) =
        ∑ t ∈ range P.D, 16 ^ t * w'.nL (i * P.D + t) := sum_congr rfl fun t ht => by
      have := Nat.mul_le_mul_right P.D (show i + 1 ≤ P.M by omega)
      have := P.hnm
      have : (i + 1) * P.D = i * P.D + P.D := by ring
      rw [hL _ (by simp at ht; omega)]
    simp only [rowL, h1, h2]

section Extract

variable {E : Type*} [AddCommGroup E] [Module F E] (g : E) (H G : ℕ → E)

variable (F) in
/-- A nontrivial linear relation among `g`, `H_0, ..., H_7` and `G_0, ..., G_{nm-1}`. -/
def Relation : Prop :=
  ∃ (s : F) (h n : ℕ → F), (s ≠ 0 ∨ (∃ j < 8, h j ≠ 0) ∨ (∃ j < P.nm, n j ≠ 0)) ∧
    commit P g H G s h n = 0

/-- The relation the `τ` level returns is one. -/
theorem relation_of_tau {ch : Challenges F} {cS cO cL cR V : E} {rho : F} {τ : Fˣ}
    (h : NormLinear.Relation g (tauInst P ch g H G cS cO cL cR V rho τ)) : Relation F P g H G := by
  obtain ⟨s, h, n, hne, he⟩ := h
  exact ⟨s, h, n, hne, he⟩

/-- Two openings of one element agree, or their difference is a relation. -/
theorem binding {s s' : F} {h h' n n' : ℕ → F}
    (he : commit P g H G s h n = commit P g H G s' h' n') :
    (s = s' ∧ (∀ j < 8, h j = h' j) ∧ ∀ j < P.nm, n j = n' j) ∨ Relation F P g H G := by
  by_cases hc : s = s' ∧ (∀ j < 8, h j = h' j) ∧ ∀ j < P.nm, n j = n' j
  · exact Or.inl hc
  right
  refine ⟨s - s', fun j => h j - h' j, fun j => n j - n' j, ?_, ?_⟩
  · by_contra hn
    push Not at hn
    exact hc ⟨sub_eq_zero.1 hn.1, fun j hj => sub_eq_zero.1 (hn.2.1 j hj),
      fun j hj => sub_eq_zero.1 (hn.2.2 j hj)⟩
  · rw [commit_sub, he, sub_self]

/-- **The `λ` level.** Take `M(nm+8)+1` distinct `λ`, the other challenges fixed, each with an
opening of `C_O`, `C_L`, `C_R` and `V̂ = 2Σ_i λ^i V_i` whose error polynomial vanishes. Either the
inputs open in the `(g, H_0)`-plane, set membership holds, the value links of the inputs `i ≥ 1`
hold and the degree-0 residue vanishes, or the generators satisfy a nontrivial relation. -/
theorem extract_lam (h2 : (2 : F) ≠ 0) (hM : 0 < P.M) (hδ : ch.δ ≠ 0) (hμ : ch.μ ≠ 0)
    (cO cL cR : E) (V : ℕ → E) (lam : Fin (P.M * (P.nm + 8) + 1) → F)
    (hlam : Function.Injective lam) (wo : Fin (P.M * (P.nm + 8) + 1) → Opening F)
    (hf : ∀ r, f P { ch with lam := lam r } (wo r) = 0)
    (hO : ∀ r, cO = Spec.cO P g H G (wo r)) (hL : ∀ r, cL = Spec.cL P g H G (wo r))
    (hR : ∀ r, cR = Spec.cR P g H G (wo r))
    (hV : ∀ r, vHat P { ch with lam := lam r } V =
      commit P g H G (wo r).vhat (lin (wo r).rV (wo r).ℓV) (wo r).nV) :
    (∃ (u : ℕ → F) (h n : ℕ → ℕ → F), (∀ i < P.M, V i = commit P g H G (u i) (h i) (n i)) ∧
      (∀ i < P.M, ∀ k < P.nm, n i k = 0) ∧ (∀ i < P.M, ∀ s, 1 ≤ s → s < 8 → h i s = 0) ∧
      rowS P ch (wo 0) = 0 ∧
      (∀ i, 1 ≤ i → i < P.M → u i = ∑ t ∈ range P.D, 16 ^ t * (wo 0).nL (i * P.D + t)) ∧
      rowE0 P ch (wo 0) + rowL P ch (wo 0) u n 0 = 0) ∨ Relation F P g H G := by
  by_cases hrel : Relation F P g H G
  · exact Or.inr hrel
  left
  -- The openings of `C_O`, `C_L`, `C_R` agree across branches.
  have aO := fun r => (binding P g H G ((hO r).symm.trans (hO 0))).resolve_right hrel
  have aL := fun r => (binding P g H G ((hL r).symm.trans (hL 0))).resolve_right hrel
  have aR := fun r => (binding P g H G ((hR r).symm.trans (hR 0))).resolve_right hrel
  -- Open each `V_i` by inverting the Vandermonde matrix of the first `M` branches.
  have hMN : P.M ≤ P.M * (P.nm + 8) + 1 := by
    have : P.M ≤ P.M * (P.nm + 8) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  set ι : Fin P.M → Fin (P.M * (P.nm + 8) + 1) := Fin.castLE hMN
  set t : Fin P.M → F := fun k => lam (ι k)
  have ht : Function.Injective t := hlam.comp (Fin.castLE_injective _)
  obtain ⟨W, hW1, -⟩ := vandermonde_inv t ht
  have hVF : ∀ b : Fin P.M, V b = commit P g H G (∑ k, W b k / 2 * (wo (ι k)).vhat)
      (fun j => ∑ k, W b k / 2 * lin (wo (ι k)).rV (wo (ι k)).ℓV j)
      (fun j => ∑ k, W b k / 2 * (wo (ι k)).nV j) := fun b => by
    rw [commit_sum]
    have e1 : ∀ k, commit P g H G (wo (ι k)).vhat (lin (wo (ι k)).rV (wo (ι k)).ℓV)
        (wo (ι k)).nV = (2 : F) • ∑ i : Fin P.M, t k ^ (i : ℕ) • V i := fun k => by
      rw [← hV]
      simp only [vHat]
      exact congrArg _ (Fin.sum_univ_eq_sum_range (fun i => lam (ι k) ^ i • V i) P.M).symm
    simp only [e1, smul_sum, smul_smul]
    rw [sum_comm]
    simp only [← sum_smul]
    have : ∀ i : Fin P.M, ∑ k, W b k / 2 * (2 * t k ^ (i : ℕ)) = if b = i then 1 else 0 :=
      fun i => by
        rw [← hW1 b i]
        exact sum_congr rfl fun k _ => by field_simp
    simp only [this, ite_smul, one_smul, zero_smul, sum_ite_eq, mem_univ, if_true]
  set u : ℕ → F := fun i => if hi : i < P.M then ∑ k, W ⟨i, hi⟩ k / 2 * (wo (ι k)).vhat else 0
  set hh : ℕ → ℕ → F := fun i j =>
    if hi : i < P.M then ∑ k, W ⟨i, hi⟩ k / 2 * lin (wo (ι k)).rV (wo (ι k)).ℓV j else 0
  set nn : ℕ → ℕ → F := fun i j =>
    if hi : i < P.M then ∑ k, W ⟨i, hi⟩ k / 2 * (wo (ι k)).nV j else 0
  have hVu : ∀ i < P.M, V i = commit P g H G (u i) (hh i) (nn i) := fun i hi => by
    simp only [u, hh, nn, dif_pos hi]
    exact hVF ⟨i, hi⟩
  -- In every branch `V̂` opens to the `λ`-combination of these.
  have hVr : ∀ r, (wo r).vhat = 2 * ∑ i ∈ range P.M, lam r ^ i * u i ∧
      (∀ s < 8, lin (wo r).rV (wo r).ℓV s = 2 * ∑ i ∈ range P.M, lam r ^ i * hh i s) ∧
      (∀ k < P.nm, (wo r).nV k = 2 * ∑ i ∈ range P.M, lam r ^ i * nn i k) := fun r => by
    have e := (commit_sum P g H G (range P.M) (fun i => 2 * lam r ^ i) u hh nn).trans
      (?_ : _ = commit P g H G (wo r).vhat (lin (wo r).rV (wo r).ℓV) (wo r).nV)
    · obtain ⟨e1, e2, e3⟩ := (binding P g H G e).resolve_right hrel
      refine ⟨?_, fun s hs => ?_, fun k hk => ?_⟩
      · rw [← e1, mul_sum]; exact sum_congr rfl fun i _ => by ring
      · rw [← e2 s hs, mul_sum]; exact sum_congr rfl fun i _ => by ring
      · rw [← e3 k hk, mul_sum]; exact sum_congr rfl fun i _ => by ring
    · rw [← hV r]
      simp only [vHat, smul_sum, smul_smul]
      exact sum_congr rfl fun i hi => by rw [hVu i (mem_range.1 hi)]
  -- The value row vanishes in every branch, as a polynomial in `λ` with fixed coefficients.
  have hrow : ∀ r, rowE0 P ch (wo 0) + ∑ i ∈ range P.M, lam r ^ i * rowL P ch (wo 0) u nn i +
      lam r ^ P.M * rowS P ch (wo 0) + ∑ j ∈ range (P.nm + 7), ∑ i ∈ range P.M,
        lam r ^ (P.M * (j + 1) + 1 + i) * rowR P hh nn j i = 0 := fun r => by
    obtain ⟨hv, hl, hn⟩ := hVr r
    have h3 := coeff3_rows P { ch with lam := lam r } (wo r) u hh nn hδ hμ hv hl hn
    rw [hf r, map_zero] at h3
    obtain ⟨c1, c2, c3⟩ := rows_congr P ch (fun k hk => (aO r).2.2 k hk)
      (fun k hk => (aL r).2.2 k hk) (fun k hk => (aR r).2.2 k hk)
      (by simpa [lin] using (aO r).2.1 3 (by norm_num))
      (by simpa [lin] using (aL r).2.1 2 (by norm_num))
      (by simpa [lin] using (aR r).2.1 1 (by norm_num))
    have hLs : ∑ i ∈ range P.M, lam r ^ i * rowL P ch (wo r) u nn i =
        ∑ i ∈ range P.M, lam r ^ i * rowL P ch (wo 0) u nn i :=
      sum_congr rfl fun i hi => by rw [c3 u nn i (mem_range.1 hi)]
    change 0 = rowE0 P ch (wo r) + ∑ i ∈ range P.M, lam r ^ i * rowL P ch (wo r) u nn i +
      lam r ^ P.M * rowS P ch (wo r) + _ at h3
    rw [c1, c2, hLs] at h3
    exact h3.symm
  obtain ⟨hE, hLi, hS, hRz⟩ := rows_zero P hM _ _ _ _ lam hlam hrow
  -- Read off the rows.
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hn0 : ∀ i < P.M, ∀ k < P.nm, nn i k = 0 := fun i hi k hk => by
    have := hRz k (by omega) i hi
    simp only [rowR, if_pos hk] at this
    exact (mul_eq_zero.1 this).resolve_left (neg_ne_zero.2 h4)
  refine ⟨u, hh, nn, hVu, hn0, fun i hi s hs1 hs8 => ?_, hS, fun i hi1 hi => ?_, hE⟩
  · have := hRz (P.nm + s - 1) (by omega) i hi
    simp only [rowR, show ¬ P.nm + s - 1 < P.nm by omega, if_false,
      show P.nm + s - 1 - P.nm + 1 = s by omega] at this
    exact (mul_eq_zero.1 this).resolve_left (neg_ne_zero.2 h2)
  · have := hLi i hi1 hi
    have hz : ∑ k ∈ range P.nm, ch.μ ^ (k + 1) * ((wo 0).nO k * nn i k) = 0 :=
      sum_eq_zero fun k hk => by rw [hn0 i hi k (mem_range.1 hk)]; ring
    simp only [rowL, hz, mul_zero, sub_zero] at this
    exact mul_left_cancel₀ h2 (by linear_combination this)

end Extract

end Bppp.Spec
