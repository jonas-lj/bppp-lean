import Mathlib

/-!
# A Vandermonde inverse in polynomial time

This file gives `lagInv t`, the inverse of the Vandermonde matrix of distinct points `t`.

Why it exists:
- The range extractor interpolates over the `τ` and the `λ` challenges.
- Mathlib's `Matrix.inv` uses the determinant. Its formula has `n!` terms, so it is too slow for
  `n` commitments.

How it works:
1. `prodLin s` is the list of coefficients of `∏ (X - c)` over `s`, low degree first. Each
   factor costs `O(n)` steps.
2. Column `m` of `lagInv t` holds the coefficients of the Lagrange polynomial `L_m`, with
   `L_m (t k) = 1` if `k = m`, and 0 if not.
3. So `V * lagInv t = 1`, with `V k b = t k ^ b`. For square matrices this gives
   `lagInv t * V = 1` (`lagInv_spec`).

Assumptions:
- The points `t` are distinct.
-/

namespace Audit.RangeProof.Sound

open Finset

variable {F : Type} [Field F]

/-! ## Coefficient lists -/

/-- `a` plus the list `l` of coefficients: `a` goes to the constant term. -/
def addHead (a : F) : List F → List F
  | [] => [a]
  | b :: r => (a + b) :: r

/-- The coefficients of `(X - c) * p`. For `p = a + X q`, this is `-c a + X (a + (X - c) q)`. -/
def mulLin (c : F) : List F → List F
  | [] => []
  | a :: q => (-c * a) :: addHead a (mulLin c q)

/-- The coefficients of `∏ (X - c)` over `c ∈ s`. -/
def prodLin : List F → List F
  | [] => [1]
  | c :: s => mulLin c (prodLin s)

/-- The value of the coefficients `l` at `x` (Horner's rule). -/
def evalList (l : List F) (x : F) : F :=
  l.foldr (fun a acc => a + x * acc) 0

theorem evalList_cons (a : F) (l : List F) (x : F) :
    evalList (a :: l) x = a + x * evalList l x := rfl

theorem evalList_addHead (a : F) (l : List F) (x : F) :
    evalList (addHead a l) x = a + evalList l x := by
  cases l
  · simp [addHead, evalList]
  · simp only [addHead, evalList_cons]
    ring

theorem evalList_mulLin (c : F) (p : List F) (x : F) :
    evalList (mulLin c p) x = (x - c) * evalList p x := by
  induction p with
  | nil => simp [mulLin, evalList]
  | cons a q ih =>
    simp only [mulLin, evalList_cons, evalList_addHead, ih]
    ring

theorem evalList_prodLin (s : List F) (x : F) :
    evalList (prodLin s) x = (s.map (x - ·)).prod := by
  induction s with
  | nil => simp [prodLin, evalList]
  | cons c s ih => simp [prodLin, evalList_mulLin, ih]

theorem length_addHead (a : F) (l : List F) : (addHead a l).length = max 1 l.length := by
  cases l <;> simp [addHead]

theorem length_mulLin (c : F) : ∀ p : List F, p ≠ [] → (mulLin c p).length = p.length + 1
  | [_], _ => by simp [mulLin, addHead]
  | a :: b :: q, _ => by
    have h := length_mulLin c (b :: q) (by simp)
    rw [mulLin, List.length_cons, length_addHead, h]
    simp only [List.length_cons]
    omega

theorem length_prodLin : ∀ s : List F, (prodLin s).length = s.length + 1
  | [] => rfl
  | c :: s => by
    have h := length_prodLin s
    rw [prodLin, length_mulLin c _ (by rw [← List.length_pos_iff]; omega), h]
    rfl

/-- A sum over `Fin n` of the coefficients is the value, if the list has at most `n` entries. -/
theorem sum_getD_eq_evalList (x : F) : ∀ (l : List F) (n : ℕ), l.length ≤ n →
    ∑ b : Fin n, x ^ (b : ℕ) * l.getD b 0 = evalList l x
  | [], n, _ => by simp [evalList]
  | a :: q, 0, h => by simp at h
  | a :: q, n + 1, h => by
    rw [Fin.sum_univ_succ, evalList_cons, ← sum_getD_eq_evalList x q n (by simp at h; omega),
      mul_sum]
    simp [pow_succ]
    exact Finset.sum_congr rfl fun b _ => by ring

/-! ## The inverse -/

/-- The points of `t` other than `t m`. -/
def others {n : ℕ} (t : Fin n → F) (m : Fin n) : List F :=
  ((List.finRange n).filter (· ≠ m)).map t

/-- The inverse of the Vandermonde matrix of `t`: entry `(b, m)` is the coefficient of `X^b` in
the Lagrange polynomial `L_m`. -/
def lagInv {n : ℕ} (t : Fin n → F) (b m : Fin n) : F :=
  (prodLin (others t m)).getD b 0 / ((others t m).map (t m - ·)).prod

omit [Field F] in
theorem length_others_lt {n : ℕ} (t : Fin n → F) (m : Fin n) : (others t m).length < n := by
  have := (List.length_filter_lt_length_iff_exists (l := List.finRange n) (p := (· ≠ m))).2
    ⟨m, List.mem_finRange m, by simp⟩
  simpa [others] using this

/-- `L_m (t k)` is 1 if `k = m`, and 0 if not. -/
theorem lagInv_right {n : ℕ} (t : Fin n → F) (ht : Function.Injective t) (k m : Fin n) :
    ∑ b : Fin n, t k ^ (b : ℕ) * lagInv t b m = if k = m then 1 else 0 := by
  simp only [lagInv, mul_div_assoc', ← Finset.sum_div]
  rw [sum_getD_eq_evalList _ _ _ (by rw [length_prodLin]; exact length_others_lt t m),
    evalList_prodLin]
  have hden : ((others t m).map (t m - ·)).prod ≠ 0 := by
    refine List.prod_ne_zero fun h0 => ?_
    simp only [others, List.map_map, List.mem_map, List.mem_filter, List.mem_finRange,
      true_and, Function.comp_apply] at h0
    obtain ⟨j, hj, e⟩ := h0
    exact (by simpa using hj : j ≠ m) (ht (sub_eq_zero.1 e).symm)
  split_ifs with hkm
  · subst hkm
    exact div_self hden
  · rw [List.prod_eq_zero, zero_div]
    simp only [others, List.map_map, List.mem_map, List.mem_filter, List.mem_finRange,
      true_and, Function.comp_apply]
    exact ⟨k, by simpa using hkm, sub_self _⟩

/-- `lagInv t` is a left inverse of the Vandermonde matrix of distinct points `t`. -/
theorem lagInv_spec {n : ℕ} (t : Fin n → F) (ht : Function.Injective t) (b j : Fin n) :
    ∑ k, lagInv t b k * t k ^ (j : ℕ) = if b = j then 1 else 0 := by
  let A : Matrix (Fin n) (Fin n) F := Matrix.of fun k b => t k ^ (b : ℕ)
  let B : Matrix (Fin n) (Fin n) F := Matrix.of fun b m => lagInv t b m
  have hAB : A * B = 1 := by
    ext k m
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact lagInv_right t ht k m
  have hBA' : B * A = 1 := mul_eq_one_comm.1 hAB
  have hBA := congrFun (congrFun hBA' b) j
  rw [Matrix.mul_apply, Matrix.one_apply] at hBA
  exact hBA

/-! Tests: the inverse of the Vandermonde matrix of `0, 1`. -/

example : lagInv (F := ℚ) ![0, 1] 0 0 = 1 := by decide +kernel
example : lagInv (F := ℚ) ![0, 1] 1 0 = -1 := by decide +kernel

end Audit.RangeProof.Sound
