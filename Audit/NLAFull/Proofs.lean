import Audit.NLAFull.Extract

/-!
# Proofs for the full NLA

This file proves `NLASoundness`, `NLACompleteness` and `NLATreesExist` from
`Audit/04-NLAFull.lean`. You do not need to review it.

How it works:
1. `roundReduction_sound`: one round is special sound with 4 challenges. If a child gives a
   link, its lift is a link. Else each child gives a witness, and `extract_core` combines them.
2. `base_sound`: the base case is special sound. The leaf is the witness.
3. `nla_sound`: induction on the rounds. `Reduction.comp_specialSound` joins one round with the
   rest.
4. `nla_complete`: induction on the rounds, with `rel_fold` in each round.
5. `nla_trees_exist`: a tree with the same 4 challenges at each node.
6. `evenNorms_of_two_pow_dvd`: if `2^r` divides `k`, with `r` rounds, then `EvenNorms m k`.

Assumptions:
- The round facts are in `Audit/NLA/Extract.lean` and `Audit/NLAFull/Lemmas.lean`.
-/

namespace Audit.NLA

open Audit.TreeSoundness

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-! ## The number of rounds -/

/-- With 0 rounds, `(m, k)` is the base case. -/
theorem isBase_of_numRounds_eq_zero {m k : ℕ} (h : numRounds m k = 0) : IsBase m k := by
  by_contra hb
  rw [numRounds] at h
  simp only [hb, ↓reduceIte] at h
  omega

/-- With 1 round or more, `(m, k)` is not the base case. -/
theorem not_isBase_of_numRounds_eq_succ {m k n : ℕ} (h : numRounds m k = n + 1) :
    ¬ IsBase m k := by
  intro hb
  rw [numRounds] at h
  simp only [hb, ↓reduceIte] at h
  omega

/-- After one round, one round fewer is left. -/
theorem numRounds_half_of_eq_succ {m k n : ℕ} (h : numRounds m k = n + 1) :
    numRounds (half m) (half k) = n := by
  have hb := not_isBase_of_numRounds_eq_succ h
  rw [numRounds] at h
  simp only [hb, ↓reduceIte] at h
  omega

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

/-! ## Soundness -/

section Soundness

variable [DecidableEq F]

/-- One round is special sound with 4 distinct challenges, when the norm length is even. -/
theorem roundReduction_sound {m k : ℕ} (hk : k % 2 = 0) :
    (roundReduction F E m k).SpecialSound (roundRules F E m k) roundExtract := by
  rintro x ⟨⟨X, R⟩, ⟨γ, hγ⟩, ws⟩ hacc
  -- Each child has a relaxed witness for its folded instance.
  have hchild (i : Fin 4) :
      (nlaRelation F E (half m) (half k)).RelaxedRel (foldInst x X R (γ i)) (ws i) :=
    hacc i
  simp only [roundExtract]
  rcases hf : (List.finRange 4).findSome?
      (fun i => (linkPart? (ws i)).map (liftLink x.ρ (γ i))) with _ | l
  · -- No child gives a link. So each child gives a witness.
    have hrel (i : Fin 4) : Rel (foldInst x X R (γ i)) (witnessPart (ws i)) := by
      have hi := List.findSome?_eq_none_iff.1 hf i (List.mem_finRange i)
      have := hchild i
      rcases hw : ws i with w | o
      · rw [hw] at this; exact this
      · simp [hw, linkPart?] at hi
    have hγ' : Function.Injective γ := fun i j h => by_contra fun hij => hγ i j hij h
    obtain ⟨hp, himp⟩ := extract_core x.g x.c x.H x.G x.ρ x.hρ hk x.C X R γ hγ' _ _ hrel
    split_ifs with h0
    · apply himp
      simp only [extractGeneratorLink, Opening.ext_iff] at h0
      exact Prod.ext h0.1 (Prod.ext h0.2.1 h0.2.2)
    · exact ⟨h0, hp⟩
  · -- A child gives a link. Its lift is a link of `x`.
    obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some hf
    have := hchild i
    rcases hw : ws i with w | o
    · simp [hw, linkPart?] at hi
    · simp only [hw, linkPart?, Option.map_some, Option.some.injEq] at hi
      subst hi
      rw [hw] at this
      obtain ⟨hne, hp⟩ := this
      refine ⟨fun h0 => hne (eq_zero_of_liftLink_eq_zero x.hρ _ _ h0), ?_⟩
      have h := point_liftLink x X R (γ i) o
      simp only [Instance.point] at h hp
      rw [h, hp]

omit [DecidableEq F] in
/-- The base case is special sound: the leaf is the witness. -/
theorem base_sound {m k : ℕ} :
    (baseSystem F E m k).SpecialSound () (fun _ w => .inl w) :=
  fun _ _ hacc => hacc

/-- `n` rounds and the base case are special sound, when `n = numRounds m k`. -/
theorem nla_sound_n : ∀ (n : ℕ) {m k : ℕ}, numRounds m k = n → EvenNorms m k →
    (nlaSystem F E n m k).SpecialSound (nlaForkRules F E n m k) (nlaExtractN n)
  | 0, _, _, _, _ => base_sound
  | n + 1, m, k, h, hk => by
    have hb := not_isBase_of_numRounds_eq_succ h
    obtain ⟨hk2, hk'⟩ : k % 2 = 0 ∧ EvenNorms (half m) (half k) := by
      rw [EvenNorms] at hk
      simpa only [hb, ↓reduceIte] using hk
    exact Reduction.comp_specialSound (roundReduction F E m k)
      (nlaSystem F E n (half m) (half k)) (fs := roundRules F E m k) (roundReduction_sound hk2)
      (nla_sound_n n (numRounds_half_of_eq_succ h) hk')

end Soundness

/-- The soundness of the full NLA, with the extractor `nlaExtract`. -/
theorem nla_sound : NLASoundness (fun x t => nlaExtract x t) :=
  fun _ _ _ _ _ _ _ _ hk => nla_sound_n _ rfl hk

/-! ## Completeness -/

/-- The honest strategy convinces the verifier for every number of rounds. -/
theorem honest_accepted : ∀ (n : ℕ) {m k : ℕ} (x : Instance F E m k) (w : Witness F m k),
    Rel x w → ∀ cs,
      let (tr, z) := (nlaSystem F E n m k).roundTypes.run (honestStrategy n x w) cs
      (nlaSystem F E n m k).Verify x tr z
  | 0, _, _, _, _, h, () => h
  | n + 1, _, _, x, w, h, (γ, cs) => honest_accepted n _ _ (rel_fold x w h γ) cs

/-- The completeness of the full NLA. -/
theorem nla_complete : NLACompleteness F E := by
  intro m k x w hw _ cs
  rcases w with w | o
  · exact honest_accepted _ x w hw cs
  · exact hw.elim

/-- Fork trees exist: use the same 4 distinct challenges at each node. -/
theorem nla_trees_exist : NLATreesExist F E := by
  intro γ hγ n
  induction n with
  | zero => intro m k; exact ⟨(⟨0, 0⟩ : Witness F m k)⟩
  | succ n ih =>
    intro m k
    obtain ⟨t⟩ := ih (half m) (half k)
    exact ⟨⟨(0, 0), ⟨γ, fun i j hij => hγ.ne hij⟩, fun _ => t⟩⟩

end Audit.NLA
