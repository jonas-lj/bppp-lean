import Audit.RangeProof.Sound.Leaf
import Audit.RangeProof.Complete

/-!
# Accepted paths of the range fork tree

This file turns one accepted path of a `RangeForkTree` into Jonas's NLA relation.

Why it exists:
- `leafVals_spec` (`Audit/RangeProof/Sound/Leaf.lean`) needs Jonas's NLA relation on every NLA
  path of a leaf. The fork tree gives only accepted runs of `verify_batch`.

How it works:
1. `verify_batch_run`: the run of `verify_batch` is a run of `Circuit.verify`.
2. The hash `hashOf answers` answers the 6 circuit challenges in order (`path_rel`).
3. `verify_run`: the run continues as a run of `norm_linear::verify` after `τ`.
4. `verify_accepts`: that run satisfies the NLA relation on the folded instance.
5. `gammasOf_hashOf`: the NLA challenges are the challenges of the path.

Assumptions:
- These are Jonas's lemmas from `Bppp/Proofs` and `Bppp/Soundness.lean`.
-/

namespace Audit.RangeProof.Sound

open Finset Bppp BpppTranscript Circuit Audit.TreeSoundness

variable {F E : Type} [Field F] [DecidableEq F] [AddCommGroup E] [Module F E] [DecidableEq E]

set_option linter.unusedSectionVars false

omit [DecidableEq F] [DecidableEq E] in
/-- An NLA transcript with `n` rounds has `n` messages and `n` challenges. -/
theorem length_nlaParts : ∀ {n : ℕ} (tr : (nlaRounds F E n).Transcript),
    (nlaParts tr).1.length = n ∧ (nlaParts tr).2.length = n
  | 0, () => ⟨rfl, rfl⟩
  | n + 1, (_, _, rest) => by
    simp [nlaParts, (length_nlaParts rest).1, (length_nlaParts rest).2]

omit [DecidableEq F] [DecidableEq E] in
/-- With the hash `hashOf A`, the NLA challenges are the entries of `A` after the challenges
that the log already has. -/
theorem gammasOf_hashOf (A : List F) : ∀ (rounds : List (E × E)) (T : BpppTranscript F E)
    (c : ℕ), T.oracle = hashOf A → T.log.countP isChallenge = c →
    NormLinear.gammasOf T rounds = (List.range rounds.length).map fun i => A.getD (c + i) 1
  | [], _, _, _, _ => by simp [NormLinear.gammasOf]
  | (X, R) :: rounds, T, c, ho, hc => by
    simp only [NormLinear.gammasOf, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    congr 1
    · simp [BpppTranscript.extend, ho, hashOf, List.countP_append, hc, isChallenge]
    · rw [gammasOf_hashOf A rounds _ (c + 1) (by simp [BpppTranscript.extend, ho])
        (by simp [BpppTranscript.extend, List.countP_append, hc, isChallenge])]
      simp [Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

/-- **One accepted path.** If `rangeVerify` accepts a path, then Jonas's NLA relation holds on
the instance of the leaf, folded with the NLA messages and challenges of the path. -/
theorem path_rel {P : CircuitParams} (x : RangeStatement F E P) (hv : P.Valid)
    (cL cO cR cS : E) (alpha : {α : F // ∀ j : ℕ, j < 16 → α + j ≠ 0}) (rho : {ρ : F // ρ ≠ 0})
    (delta : {δ : F // δ ≠ 0}) (beta : {β : F // β ≠ 0}) (lam : F) (tau : {τ : F // τ ≠ 0})
    (tr : (nlaRounds F E (numNlaRounds P)).Transcript) (z : F × List F) (C : Constraints F)
    (hCnew : Constraints.new P alpha.val (rho.val * rho.val) lam = .ok C)
    (hC : Constraints.Correct P alpha.val (rho.val * rho.val) lam C hv)
    (h : rangeVerify x
      ((cL, cO), alpha, cR, rho, (), delta, (), beta, (), lam, cS, tau, tr) z) :
    Spec.NormLinear.Rel x.gens.g (Spec.NormLinear.foldPath
      (leafSpecInst x.gens x.commitments cS cO cL cR
        (cTau C beta.val (Units.mk0 tau.val tau.property))
        (psTau P C rho.val delta.val (Units.mk0 tau.val tau.property))
        (pnTau P C delta.val (Units.mk0 tau.val tau.property)) C delta.val rho.val
        (Units.mk0 tau.val tau.property)) (nlaParts tr).1 (nlaParts tr).2)
      ⟨fun j => [z.1].getD j 0, fun j => z.2.getD j 0⟩ := by
  obtain ⟨l, nf⟩ := z
  set τu : Fˣ := Units.mk0 tau.val tau.property
  set A : List F := [alpha.val, rho.val, lam, beta.val, delta.val, tau.val] ++ (nlaParts tr).2
  set nlp : NormLinearProof F E := { rounds := (nlaParts tr).1, l_final := l, n_final := nf }
  set rp : Bppp.RangeProof F E :=
    { proof := { c_l := cL, c_o := cO, c_r := cR, c_s := cS, nl_proof := nlp } }
  have hb : rp.verify_batch (hashOf A) x.generators x.commitments x.range x.dst = .ok () := h
  obtain ⟨t', hrun⟩ := Bppp.RangeProof.verify_batch_run rp (hashOf A) x.generators
    x.commitments x.range x.dst x.gens P x.setup.hGens x.setup.hParams hb
  set t := Bppp.RangeProof.transcript (hashOf A) x.dst x.range.bits x.commitments.length
  have ho : t.oracle = hashOf A := rfl
  have hc0 : t.log.countP isChallenge = 0 := transcript_count _ _ _ _
  have hlog : ∀ log : List (Entry F E), t.oracle log = A.getD (log.countP isChallenge - 1) 1 :=
    fun log => by rw [ho]; rfl
  obtain ⟨-, -, hnl⟩ := verify_run x.gens P hv rp.proof x.commitments t t' alpha.val rho.val lam
    beta.val delta.val τu C
    (by rw [hlog]; simp [Circuit.alphaLog, Circuit.rhoLog, Circuit.lamLog, Circuit.betaLog,
      Circuit.deltaLog, Circuit.tauLog, Circuit.preAlpha, List.countP_append, List.countP_cons,
      hc0, isChallenge, List.countP_map, Function.comp_def, A])
    (by rw [hlog]; simp [Circuit.alphaLog, Circuit.rhoLog, Circuit.lamLog, Circuit.betaLog,
      Circuit.deltaLog, Circuit.tauLog, Circuit.preAlpha, List.countP_append, List.countP_cons,
      hc0, isChallenge, List.countP_map, Function.comp_def, A])
    (by rw [hlog]; simp [Circuit.alphaLog, Circuit.rhoLog, Circuit.lamLog, Circuit.betaLog,
      Circuit.deltaLog, Circuit.tauLog, Circuit.preAlpha, List.countP_append, List.countP_cons,
      hc0, isChallenge, List.countP_map, Function.comp_def, A])
    (by rw [hlog]; simp [Circuit.alphaLog, Circuit.rhoLog, Circuit.lamLog, Circuit.betaLog,
      Circuit.deltaLog, Circuit.tauLog, Circuit.preAlpha, List.countP_append, List.countP_cons,
      hc0, isChallenge, List.countP_map, Function.comp_def, A])
    (by rw [hlog]; simp [Circuit.alphaLog, Circuit.rhoLog, Circuit.lamLog, Circuit.betaLog,
      Circuit.deltaLog, Circuit.tauLog, Circuit.preAlpha, List.countP_append, List.countP_cons,
      hc0, isChallenge, List.countP_map, Function.comp_def, A])
    (by rw [hlog]; simp [Circuit.alphaLog, Circuit.rhoLog, Circuit.lamLog, Circuit.betaLog,
      Circuit.deltaLog, Circuit.tauLog, Circuit.preAlpha, List.countP_append, List.countP_cons,
      hc0, isChallenge, List.countP_map, Function.comp_def, A, τu])
    delta.property hCnew hC hrun
  have hacc := NormLinear.verify_accepts x.gens _ _ _ _ _ _ _ _
    (by rw [x.setup.hHLen]; decide) hnl
  have hγ : NormLinear.gammasOf ((afterTau t x.commitments rp.proof).extend
      [.message "dom-sep" ("norm_linear".toList.map Char.toNat)]) rp.proof.nl_proof.rounds =
      (nlaParts tr).2 := by
    rw [gammasOf_hashOf A _ _ 6 rfl (by
      simp [afterTau, Circuit.tauLog, Circuit.deltaLog, Circuit.betaLog, Circuit.lamLog,
        Circuit.rhoLog, Circuit.alphaLog, Circuit.preAlpha, BpppTranscript.extend,
        List.countP_append, List.countP_cons, hc0, isChallenge, List.countP_map,
        Function.comp_def])]
    obtain ⟨h1, h2⟩ := length_nlaParts tr
    apply List.ext_getElem (by simp [rp, nlp, h1, h2])
    intro i hi _
    simp only [List.getElem_map, List.getElem_range, A]
    rw [List.getD_eq_getElem _ _ (by simp at hi ⊢; omega), List.getElem_append_right (by simp)]
    simp
  rw [hγ] at hacc
  exact hacc

end Audit.RangeProof.Sound
