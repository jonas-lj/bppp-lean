import Audit.NLA

/-!
# Proofs for one NLA round

This file proves `RoundCompleteness` and `RoundSoundness` from `Audit/NLA.lean`.

Why it exists:
- The statements stay in `Audit/NLA.lean`, so that file has no long proofs.

How it works:
1. `rel_fold`: the honest fold keeps `Rel`. It uses the fold lemmas in
   `Audit/NLA/FoldLemmas.lean`.
2. `roundProtocol_complete` follows from `rel_fold` for every challenge.
3. `round_sound` applies `extract_core` from `Audit/NLA/Extract.lean`.
4. `Instance.Independent` and `round_sound_of_independent` serve the corollaries and the bridge
   to Jonas's types. In a real group, `Independent` is false.

Assumptions:
- `ρ ≠ 0`, as each `Instance` carries.
-/

namespace Audit.NLA

open OracleComp ChallengeVerifyProtocol

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-- The honest fold keeps `Rel`, for every challenge `γ`. -/
theorem rel_fold {m k : ℕ} (x : Instance F E m k) (w : Witness F m k) (h : Rel x w) (γ : F) :
    Rel (foldInst x (msgX x w) (msgR x w) γ) (foldWit x γ w) := by
  simp only [Rel, Instance.point, Instance.opening, foldInst, foldWit, msgX, msgR] at h ⊢
  rw [ip_fold, wip_fold _ _ x.hρ, msm_fold_H, msm_fold_G _ _ x.hρ, h]
  module

/-- The completeness of one round. -/
theorem roundProtocol_complete [SampleableType F] : RoundCompleteness F E := by
  classical
  intro m k x w hw
  simp [roundProtocol, rel_fold x w (of_decide_eq_true hw)]

/-- The soundness of one round. -/
theorem round_sound : RoundSoundness F E := by
  classical
  intro m k x f hk
  have hrel (i : Fin 4) : Rel (foldInst x f.X f.R (f.γ i)) (f.w i) := by
    simpa [roundProtocol] using f.hAccepted i
  have hγ : Function.Injective f.γ := fun i j h => by_contra fun hij => f.hDistinct i j hij h
  obtain ⟨hp, himp⟩ := extract_core x.g x.c x.H x.G x.ρ x.hρ hk x.C f.X f.R f.γ hγ
    (fun i => (f.w i).ℓ) (fun i => (f.w i).n) hrel
  by_cases h : extractGeneratorLink x f.γ f.w = 0
  · refine Or.inl (himp ?_)
    simp only [extractGeneratorLink, Opening.ext_iff] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
  · exact Or.inr ⟨h, hp⟩

/-- The generators of `x` are linearly independent: only the zero opening opens the zero point.
This is false in a real group with 2 or more generators. Only proof-side corollaries use it. -/
def Instance.Independent {m k : ℕ} (x : Instance F E m k) : Prop :=
  ∀ o : Opening F m k, x.point o = 0 → o = 0

/-- On independent generators, a fork gives a witness. -/
theorem round_sound_of_independent {m k : ℕ} (x : Instance F E m k) (f : Fork x)
    (hind : x.Independent) (hk : k % 2 = 0) : ∃ w, Rel x w := by
  rcases round_sound x f hk with h | ⟨hne, hp⟩
  · exact ⟨_, h⟩
  · exact absurd (hind _ hp) hne

end Audit.NLA
