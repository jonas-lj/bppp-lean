import Audit.NLA.Proofs

/-!
# Counterexamples for one NLA round

This file shows that the hypothesis `hk : k % 2 = 0` of `round_sound` is necessary.

Why it exists:
- A hypothesis that a proof does not need weakens a theorem for no reason.
- This file shows that `round_sound` is false without `hk`.

How it works:
1. Take `m = 0`, `k = 1` and `ρ = 1` over `ℚ`. The points are `ℚ²`, with `g = (1, 0)` and
   `G₀ = (0, 1)`. These generators are independent.
2. The instance is `C = -34 • g + 1 • G₀`. `Rel` needs `σ = 1² = 1`, so no witness exists.
3. With `X = 50 • g - 5 • G₀` and `R = -10 • g + G₀`, the responses `n' = γ² - 5γ` are accepted at
   `γ = 1, 2, 3, 4`.

Assumptions:
- The padded slot of `G` has no partner. So no cubic forces `n'` to be linear in `γ`, and `n'²`
  has degree 4. 4 points do not force a quartic to agree with a quadratic.
-/

namespace Audit.NLA

/-- A sum over `Fin (half 0)` is empty. -/
theorem sum_half_zero {M : Type} [AddCommMonoid M] (f : Fin (half 0) → M) : ∑ i, f i = 0 :=
  Finset.sum_eq_zero fun i _ => (Nat.not_lt_zero _ i.isLt).elim

/-- The generator `g = (1, 0)` of the counterexample. -/
def cexG : Fin 2 → ℚ := ![1, 0]

/-- The generator `G₀ = (0, 1)` of the counterexample. -/
def cexG₀ : Fin 2 → ℚ := ![0, 1]

/-- The instance of the counterexample: `C = -34 • g + 1 • G₀`, with no linear part. -/
def cexInst : Instance ℚ (Fin 2 → ℚ) 0 1 where
  C := ![-34, 1]
  g := cexG
  c := ![]
  H := ![]
  G := ![cexG₀]
  ρ := 1
  hρ := one_ne_zero

/-- The challenges `γ = 1, 2, 3, 4`. -/
def cexγ : Fin 4 → ℚ := ![1, 2, 3, 4]

/-- The response at challenge `γ`: `n' = γ² - 5γ`. -/
def cexWit (γ : ℚ) : Witness ℚ (half 0) (half 1) where
  ℓ := ![]
  n := fun _ => γ ^ 2 - 5 * γ

/-- Without `hk`, `round_sound` is false: 4 responses are accepted on an instance with no
witness and with independent generators. -/
theorem round_not_sound_odd :
    Function.Injective cexγ ∧
    (∀ i, (roundProtocol 0 1).verify cexInst (![50, -5], ![-10, 1]) (cexγ i)
      (cexWit (cexγ i)) = true) ∧
    cexInst.Independent ∧ ∀ w, ¬ Rel cexInst w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [cexγ]
  · intro i
    simp only [roundProtocol, decide_eq_true_eq]
    funext t
    fin_cases i <;> fin_cases t <;>
      simp [Instance.point, Instance.opening, foldInst, cexInst, cexWit, cexγ, cexG, cexG₀,
        ip, wip, msm, evens, odds, sum_half_zero] <;>
      rw [show half 1 = 1 from rfl] <;> norm_num
  · intro o h0
    have h1 := congrFun h0 0
    have h2 := congrFun h0 1
    simp [Instance.point, cexInst, cexG, cexG₀, msm] at h1 h2
    ext
    · show o.σ = 0
      simpa using h1
    · exact Fin.elim0 ‹_›
    · rename_i j
      fin_cases j
      show o.n 0 = 0
      simpa using h2
  · intro w h
    have h1 := congrFun h 0
    have h2 := congrFun h 1
    simp [Instance.point, Instance.opening, cexInst, cexG, cexG₀, ip, wip, msm] at h1 h2
    rw [← h2] at h1
    norm_num at h1

end Audit.NLA
