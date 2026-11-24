import Audit.NLAFull.Legacy

/-!
# Proofs for the old NLA types

This file proves `TranscriptCompleteness` and `ForkTreeSoundness` from
`Audit/NLAFull/Legacy.lean`. You do not need to review it.

How it works:
1. `transcript_complete`: induction on the challenges, with `rel_fold` in each round.
2. `treeExtractGeneratorLink_spec`: induction on the tree. A nonzero link of a child lifts to
   a link. Else each child gives a witness for its folded instance, and `extract_core` combines
   them.
3. `forkTree_sound` follows: the link is 0 and the witness is valid, or the link is a link.
4. `nla_sound_of_independent`: on independent generators, an accepted tree gives a witness.
-/

namespace Audit.NLA

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-- The honest prover always convinces the verifier. -/
theorem transcript_complete : TranscriptCompleteness F E := by
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

/-! ## Soundness -/

section Soundness

variable [DecidableEq F]

/-- The link opens 0. If it is 0, the witness opens `C`. -/
theorem treeExtractGeneratorLink_spec {m k : ℕ} (x : Instance F E m k) (t : ForkTree F E m k)
    (hk : EvenNorms m k) (hacc : ∀ p ∈ t.transcripts, verify x p) :
    x.point (treeExtractGeneratorLink x t) = 0 ∧
      (treeExtractGeneratorLink x t = 0 → Rel x (treeExtractWitness x t)) := by
  induction t with
  | leaf w hBase =>
    refine ⟨?_, fun _ => ?_⟩
    · change (0 : F) • x.g + msm 0 x.H + msm 0 x.G = 0
      simp [msm]
    exact hacc (.done w) (by simp [ForkTree.transcripts])
  | @node m k head child hNotBase ih =>
    obtain ⟨X, R, γ, hDistinct⟩ := head
    obtain ⟨hk2, hk'⟩ : k % 2 = 0 ∧ EvenNorms (half m) (half k) := by
      rw [EvenNorms] at hk
      simpa only [hNotBase, ↓reduceIte] using hk
    -- Apply the induction hypothesis to each child.
    have hchild (i : Fin 4) := ih i (foldInst x X R (γ i)) hk' fun q hq => by
      exact hacc (.round X R (γ i) q) (by
        simp only [ForkTree.transcripts, List.mem_flatMap, List.mem_map]
        exact ⟨i, List.mem_finRange i, q, hq, rfl⟩)
    simp only [treeExtractGeneratorLink, treeExtractWitness]
    split
    · -- A child has a nonzero link. Its lift is the link.
      rename_i i hf
      refine ⟨?_, fun h0 => ?_⟩
      · rw [point_liftLink x X R]
        exact (hchild i).1
      · have := List.find?_some hf
        simp [h0] at this
    · -- No child has a nonzero link. So each child gives a witness.
      rename_i hf
      have hz (i : Fin 4) := by
        simpa using List.find?_eq_none.mp hf i (List.mem_finRange i)
      have hrel (i : Fin 4) := (hchild i).2 (eq_zero_of_liftLink_eq_zero x.hρ _ _ (hz i))
      have hγ : Function.Injective γ := fun i j h => by_contra fun hij => hDistinct i j hij h
      obtain ⟨hp, himp⟩ := extract_core x.g x.c x.H x.G x.ρ x.hρ hk2 x.C X R γ hγ _ _ hrel
      refine ⟨hp, fun h0 => himp ?_⟩
      simp only [extractGeneratorLink, Opening.ext_iff] at h0
      exact Prod.ext h0.1 (Prod.ext h0.2.1 h0.2.2)


/-- The soundness of the full NLA. -/
theorem forkTree_sound : ForkTreeSoundness F E := by
  intro m k x t hk hacc
  obtain ⟨hp, himp⟩ := treeExtractGeneratorLink_spec x t hk hacc
  by_cases h : treeExtractGeneratorLink x t = 0
  · exact Or.inl (himp h)
  · exact Or.inr ⟨h, hp⟩

end Soundness

/-- On independent generators, an accepted `ForkTree` gives a witness. `Bridge.lean` uses it. -/
theorem nla_sound_of_independent {m k : ℕ} (x : Instance F E m k) (t : ForkTree F E m k)
    (hind : x.Independent) (hk : EvenNorms m k) (hacc : ∀ p ∈ t.transcripts, verify x p) :
    ∃ w, Rel x w := by
  classical
  rcases forkTree_sound x t hk hacc with h | ⟨hne, hp⟩
  · exact ⟨_, h⟩
  · exact absurd (hind _ hp) hne

end Audit.NLA
