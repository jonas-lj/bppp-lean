import Audit.NLA.Proofs

/-!
# Bad challenges of one NLA round

This file bounds the challenges at which a commitment `(X, R)` can be accepted.

Why it exists:
- It restates `round_sound` as a count. That count is the step toward a soundness error.

How it works:
1. A challenge is bad if some response makes the commitment accept.
2. 4 distinct bad challenges and `round_sound` give a witness or a generator relation.
3. So, on an instance with neither, no more than 3 challenges are bad.

Assumptions:
- The norm length `k` is even, as `round_sound` needs.
-/

namespace Audit.NLA

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-- The bad challenges of a commitment `(X, R)`: the `γ` at which some response accepts. -/
def badSet {m k : ℕ} (x : Instance F E m k) (X R : E) : Set F :=
  {γ | ∃ w', (roundProtocol m k).verify x (X, R) γ w' = true}

/-- On an instance with no witness and no generator relation, each commitment has no more than
3 bad challenges. The counterexample in our notes shows that 3 can occur.

TODO (soundness error): turn this count into a bound of about `3r/|F|` for `r` rounds, by
round-by-round soundness. The paper states only an asymptotic bound (Theorem 2). -/
theorem badSet_encard_le {m k : ℕ} (x : Instance F E m k) (hk : k % 2 = 0)
    (hgen : ¬ GenRelation x) (hwit : ∀ w, ¬ Rel x w) (X R : E) :
    (badSet x X R).encard ≤ 3 := by
  by_contra h
  have h4 : (4 : ℕ∞) ≤ (badSet x X R).encard := Order.add_one_le_of_lt (not_le.mp h)
  obtain ⟨t, hts, ht⟩ := Set.exists_subset_encard_eq h4
  have htf : t.Finite := Set.finite_of_encard_eq_coe ht
  have hcard : htf.toFinset.card = 4 := by
    have := Set.encard_coe_eq_coe_finsetCard htf.toFinset
    rw [Set.Finite.coe_toFinset, ht] at this
    exact_mod_cast this.symm
  let e := htf.toFinset.equivFin
  let γ_vec : Fin 4 → F := fun i => (e.symm (Fin.cast hcard.symm i)).1
  have hγ : Function.Injective γ_vec := fun i j hij =>
    Fin.cast_injective _ (e.symm.injective (Subtype.ext hij))
  have hbad (i : Fin 4) : γ_vec i ∈ badSet x X R :=
    hts ((Set.Finite.mem_toFinset htf).mp (e.symm (Fin.cast hcard.symm i)).2)
  choose w_vec hacc using hbad
  rcases round_sound x ⟨X, R, γ_vec, w_vec, fun i j hij e => hij (hγ e), hacc⟩ hk with h | h
  · exact hgen h
  · exact hwit _ h

end Audit.NLA
