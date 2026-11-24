import Audit.NLAFull.Proofs
import Bppp.Model.NormLinear
import Bppp.Model.Crs

/-!
# The full NLA and the Rust round count

This file connects `IsBase` and `numRounds` in `Audit/04-NLAFull.lean` to the Rust code in `Model/`.

Why it exists:
- `nlaSystem` runs `numRounds m k` rounds, until `IsBase`. This file proves that the Rust
  verifier stops at the same place.
- `nla_sound` needs `EvenNorms m k`. This file proves it for every circuit size of the Rust code.

How it works:
1. `numRounds_eq_proof_shape`: both functions use the same recursion, so induction proves it.
2. `numRounds_le`: with norm length `2 ^ j` and linear length at most `2 ^ j`, at most `j` rounds
   occur.
3. `evenNorms_nm`: the norm length is `nm = 2 ^ c` with `c ≥ 4`, and the linear length is `8`. So
   `2 ^ numRounds 8 nm` divides `nm`, and `evenNorms_of_two_pow_dvd` gives `EvenNorms`.

Assumptions:
- The Rust verifier gets `8` linear generators (`H_LEN`) and `nm` norm generators.
-/

namespace Audit.NLA

open Bppp Bppp.NormLinear

/-- Our round count is the round count that the Rust verifier enforces (`proof_shape`). -/
theorem numRounds_eq_proof_shape (m k : ℕ) : numRounds m k = (proof_shape m k).1 := by
  induction m, k using numRounds.induct with
  | case1 m k hb =>
    have hb' : is_base_case m k = true := (is_base_case_iff m k).2 hb
    rw [numRounds, proof_shape]
    simp only [hb, hb', ↓reduceIte, ↓reduceDIte]
  | case2 m k hb ih =>
    have hb' : ¬ is_base_case m k = true := fun h => hb ((is_base_case_iff m k).1 h)
    rw [numRounds, proof_shape]
    simp only [hb, hb', ↓reduceIte]
    change 1 + numRounds (half m) (half k) = (proof_shape (half m) (half k)).1 + 1
    omega

/-- With norm length `2 ^ j` and linear length at most `2 ^ j`, at most `j` rounds occur. -/
theorem numRounds_le (j : ℕ) (hj : 2 ≤ j) :
    ∀ m, m ≤ 2 ^ j → numRounds m (2 ^ j) ≤ j := by
  induction j, hj using Nat.le_induction with
  | base =>
    intro m hm
    interval_cases m <;> simp [numRounds, IsBase, half]
  | succ j hj ih =>
    intro m hm
    rw [numRounds]
    split_ifs
    · omega
    · have hk : half (2 ^ (j + 1)) = 2 ^ j := by simp only [half, pow_succ]; omega
      have := ih (half m) (by simp only [half, pow_succ] at hm ⊢; omega)
      rw [hk]
      omega

/-- For every circuit size of the Rust code, `2 ^ numRounds 8 nm` divides `nm`. -/
theorem two_pow_numRounds_dvd_nm (n_d : ℕ) :
    2 ^ numRounds 8 (next_power_of_two (max n_d BASE)) ∣ next_power_of_two (max n_d BASE) := by
  set c := Nat.clog 2 (max n_d BASE)
  have h16 : 16 ≤ 2 ^ c := le_trans (le_max_right n_d 16) (Nat.le_pow_clog one_lt_two _)
  have hc : 2 ≤ c := by
    by_contra h
    have : 2 ^ c ≤ 2 ^ 1 := Nat.pow_le_pow_right two_pos (by omega)
    omega
  exact pow_dvd_pow 2 (numRounds_le c hc 8 (by omega))

/-- For every circuit size of the Rust code, all norm lengths are even until the base case. -/
theorem evenNorms_nm (n_d : ℕ) : EvenNorms 8 (next_power_of_two (max n_d BASE)) :=
  evenNorms_of_two_pow_dvd (two_pow_numRounds_dvd_nm n_d)

end Audit.NLA
