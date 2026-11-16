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
  intro m k x f hind hk
  have hrel (i : Fin 4) : Rel (foldInst x f.X f.R (f.γ i)) (f.w i) := by
    simpa [roundProtocol] using f.accepted i
  have hγ : Function.Injective f.γ := fun i j h => by_contra fun hij => f.distinct i j hij h
  rcases extract_core x.g x.c x.H x.G x.ρ x.hρ hk x.C f.X f.R f.γ hγ
    (fun i => (f.w i).ℓ) (fun i => (f.w i).n) hrel with ⟨s, a, b, hne, h0⟩ | h
  · have ho := hind ⟨s, a, b⟩ h0
    simp only [Opening.ext_iff] at ho
    tauto
  · exact h

end Audit.NLA
