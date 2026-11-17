import Audit.NLAFull

/-!
# Proofs for the full NLA

This file proves `NLACompleteness` and `NLASoundness` from `Audit/NLAFull.lean`.

Why it exists:
- The statements stay in `Audit/NLAFull.lean`, so that file has no long proofs.

How it works:
1. `nla_complete`: induction on the challenges, with `rel_fold` in each round.
2. `evenNorms_of_two_pow_dvd`: if `2^r` divides `k`, with `r` rounds, then `EvenNorms m k`.
3. `nla_sound`: induction on the tree. At each node, the children give witnesses for the
   folded instances, and `round_sound` combines them.

Assumptions:
- The round facts are in `Audit/NLAFull/Lemmas.lean`.
-/

namespace Audit.NLA

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-- The honest prover always convinces the verifier. -/
theorem nla_complete : NLACompleteness F E := by
  intro m k x w h γs
  induction m, k using numRounds.induct generalizing γs with
  | case1 m k hb =>
    rw [honestTranscript]
    simp only [hb, ↓reduceDIte]
    exact h
  | case2 m k hb ih =>
    rw [honestTranscript]
    simp only [hb, ↓reduceDIte]
    exact ih _ _ (rel_fold x w h (γs 0)) _

/-- If `2^r` divides `k`, with `r = numRounds m k`, then the norm length is even in every
round. -/
theorem evenNorms_of_two_pow_dvd {m k : ℕ} (h : 2 ^ numRounds m k ∣ k) : EvenNorms m k := by
  rw [EvenNorms]
  rw [numRounds] at h
  split_ifs at h ⊢ with hb
  rw [add_comm] at h
  obtain ⟨h2, h'⟩ := even_of_two_pow_dvd h
  exact ⟨h2, evenNorms_of_two_pow_dvd h'⟩
termination_by m + k
decreasing_by all_goals (simp only [IsBase, half] at *; omega)

/-- The soundness of the full NLA. -/
theorem nla_sound : NLASoundness F E := by
  intro m k x t hind hk hacc
  classical
  induction t with
  | leaf w hBase => exact hacc (.done w) (by simp [ForkTree.transcripts])
  | @node m k head child hNotBase ih =>
    obtain ⟨X, R, γ, hDistinct⟩ := head
    obtain ⟨hk2, hk'⟩ : k % 2 = 0 ∧ EvenNorms (half m) (half k) := by
      rw [EvenNorms] at hk
      simpa only [hNotBase, ↓reduceIte] using hk
    -- Apply the induction hypothesis to each child.
    have hchild (i : Fin 4) :
        Rel (foldInst x X R (γ i)) (treeExtract (foldInst x X R (γ i)) (child i)) := by
      refine ih i _ (independent_fold x hind X R (γ i)) hk' fun q hq => ?_
      exact hacc (.round X R (γ i) q) (by
        simp only [ForkTree.transcripts, List.mem_flatMap, List.mem_map]
        exact ⟨i, List.mem_finRange i, q, hq, rfl⟩)
    refine round_sound x ⟨⟨X, R, γ, hDistinct⟩, _, fun i => ?_⟩ hind hk2
    simpa [roundProtocol] using hchild i

end Audit.NLA
