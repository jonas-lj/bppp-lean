import Audit.RangeProof.NestedTree
import Audit.RangeProof.Statement
import Audit.NLAFull.Rust
import Audit.NLAFull.LegacyProofs
import Bppp.Soundness

/-!
# The old range-proof soundness, with independent generators

This file proves the old soundness statement, which assumes `Independent`, with Jonas's
`Bppp.RangeProof.verify_extract`.

Why it exists:
- In a real group, `Independent` is false. So this result is not the audited statement. The
  audited statement is `RangeSoundness` in `Audit/02-RangeProof.lean`.
- The new proof reuses the plumbing of this file: from the Rust runs to Jonas's spec runs.

How it works:
1. `toTree` turns an NLA `ForkTree` into his `Tree`. It has `numRounds` rounds and distinct
   challenges.
2. `paths_toTree` maps each path of his tree to a transcript of our tree.
3. `gammasOf_eq` shows that the Rust verifier derives the NLA challenges of the run from
   `Run.oracle`.
4. `range_sound_of_independent` turns the nested fork tree into his indexed families and
   applies his theorem. `Independent` rules out his second case, a relation among the
   generators.
-/

namespace Audit.RangeProof

open Bppp

variable {F E : Type} [Field F] [DecidableEq F] [AddCommGroup E] [Module F E] [DecidableEq E]

set_option linter.unusedSectionVars false

/-! ## NLA trees -/

/-- The final opening of a leaf, in Jonas's form. -/
def finalWit {m k : ℕ} (w : NLA.Witness F m k) : Spec.NormLinear.Witness F :=
  ⟨fun j => [(List.ofFn w.ℓ).headD 0].getD j 0, fun j => (List.ofFn w.n).getD j 0⟩

/-- An NLA fork tree as Jonas's tree. -/
def toTree : ∀ {m k : ℕ}, NLA.ForkTree F E m k → Spec.NormLinear.Tree F E
  | _, _, .leaf w _ => .leaf (finalWit w)
  | _, _, .node head child _ => .node head.X head.R head.γ fun i => toTree (child i)

/-- Jonas's path of an NLA transcript. -/
def toPath {m k : ℕ} (p : NLA.Transcript F E m k) :
    List (E × E) × List F × Spec.NormLinear.Witness F :=
  ((nlaProof p).rounds, gammas p,
    ⟨fun j => [(nlaProof p).l_final].getD j 0, fun j => (nlaProof p).n_final.getD j 0⟩)

theorem depth_toTree : ∀ {m k : ℕ} (ft : NLA.ForkTree F E m k),
    (toTree ft).Depth (NLA.numRounds m k)
  | m, k, .leaf w hb => by
    rw [NLA.numRounds]
    simp only [hb, ↓reduceIte]
    exact .leaf _
  | m, k, .node head child hnb => by
    rw [NLA.numRounds]
    simp only [hnb, ↓reduceIte]
    rw [add_comm]
    exact .node _ _ _ _ _ fun i => depth_toTree (child i)

theorem distinct_toTree : ∀ {m k : ℕ} (ft : NLA.ForkTree F E m k), (toTree ft).Distinct
  | _, _, .leaf _ _ => trivial
  | _, _, .node head child _ =>
    ⟨fun i j h => by
      by_contra hij
      exact head.hDistinct i j hij h, fun i => distinct_toTree (child i)⟩

theorem paths_toTree : ∀ {m k : ℕ} (ft : NLA.ForkTree F E m k),
    ∀ q ∈ (toTree ft).paths, ∃ p ∈ ft.transcripts, q = toPath p
  | _, _, .leaf w hb, q, hq => by
    simp only [toTree, Spec.NormLinear.Tree.paths, List.mem_singleton] at hq
    subst hq
    exact ⟨.done w hb, by simp [NLA.ForkTree.transcripts], by simp [toPath, nlaProof, gammas,
      finalWit]⟩
  | _, _, .node head child hnb, q, hq => by
    simp only [toTree, Spec.NormLinear.Tree.paths, List.mem_flatMap, List.mem_finRange,
      List.mem_map, true_and] at hq
    obtain ⟨i, q', hq', rfl⟩ := hq
    obtain ⟨p, hp, rfl⟩ := paths_toTree (child i) q' hq'
    refine ⟨.round head.X head.R (head.γ i) p hnb, ?_, ?_⟩
    · simp only [NLA.ForkTree.transcripts, List.mem_flatMap, List.mem_finRange, List.mem_map,
        true_and]
      exact ⟨i, p, hp, rfl⟩
    · simp [toPath, nlaProof, gammas]

theorem transcripts_ne_nil : ∀ {m k : ℕ} (ft : NLA.ForkTree F E m k), ft.transcripts ≠ []
  | _, _, .leaf _ _ => by simp [NLA.ForkTree.transcripts]
  | _, _, .node _ child _ => by
    have := transcripts_ne_nil (child 0)
    simp only [NLA.ForkTree.transcripts, ne_eq, List.flatMap_eq_nil_iff, List.mem_finRange,
      List.map_eq_nil_iff, forall_const, not_forall]
    exact ⟨0, this⟩

theorem length_gammas : ∀ {m k : ℕ} (p : NLA.Transcript F E m k),
    (gammas p).length = (nlaProof p).rounds.length
  | _, _, .done _ _ => rfl
  | _, _, .round _ _ _ rest _ => by simp [gammas, nlaProof, length_gammas rest]

/-! ## The NLA challenges -/

variable {P : CircuitParams}

/-- With the hash of `r`, the Rust verifier derives the NLA challenges of `r`. -/
theorem gammasOf_eq (r : Run F E P) : ∀ (rounds : List (E × E)) (T : BpppTranscript F E) (c : ℕ),
    T.oracle = r.oracle → T.log.countP isGamma = c → c + rounds.length ≤ (gammas r.nla).length →
    NormLinear.gammasOf T rounds = ((gammas r.nla).drop c).take rounds.length
  | [], _, _, _, _, _ => by simp [NormLinear.gammasOf]
  | (X, R) :: rounds, T, c, ho, hc, hlen => by
    simp only [List.length_cons] at hlen
    have hc' : c < (gammas r.nla).length := by omega
    simp only [NormLinear.gammasOf, BpppTranscript.extend, List.length_cons]
    rw [List.drop_eq_getElem_cons hc', List.take_succ_cons]
    congr 1
    · rw [ho]
      simp [Run.oracle, isGamma, List.countP_append, hc, List.getElem?_eq_getElem hc']
    · exact gammasOf_eq r rounds _ (c + 1) ho (by simp [List.countP_append, hc, isGamma])
        (by omega)

/-- The circuit part of the transcript has no NLA challenge. -/
theorem countP_isGamma_afterTau (r : Run F E P) (dst : List ℕ) (bits : ℕ)
    (vcs : List (PedersenCommitment E)) (proof : Circuit.CircuitProof F E) :
    (((Circuit.afterTau (RangeProof.transcript r.oracle dst bits vcs.length) vcs proof).extend
      [.message "dom-sep" ("norm_linear".toList.map Char.toNat)]).log.countP isGamma) = 0 := by
  simp [Circuit.afterTau, Circuit.tauLog, Circuit.deltaLog, Circuit.betaLog, Circuit.lamLog,
    Circuit.rhoLog, Circuit.alphaLog, Circuit.preAlpha, RangeProof.transcript, BpppTranscript.new,
    BpppTranscript.extend, List.countP_append, isGamma, List.countP_map, Function.comp_def]

/-! ## Generators -/

/-- The generators `g`, `h_vec` and `g_vec` are linearly independent. This is false in a real
group with 2 or more generators. Only the old statement in this file uses it. -/
def Independent (gens : Generators E) : Prop :=
  ∀ (s : F) (h : Fin gens.h_vec.length → F) (n : Fin gens.g_vec.length → F),
    s • gens.g + ∑ i, h i • gens.h_vec[i] + ∑ j, n j • gens.g_vec[j] = 0 →
      s = 0 ∧ h = 0 ∧ n = 0

/-- Independent generators have no relation in Jonas's sense. -/
theorem not_relation (params : CircuitParams) (gens : Generators E) (hv : params.Valid)
    (hh : gens.h_vec.length = H_LEN) (hg : gens.g_vec.length = params.nm)
    (hind : Independent (F := F) gens) :
    ¬ Spec.Relation F (params.toSpec hv) gens.g (fun k => gens.h_vec.getD k 0)
      (fun k => gens.g_vec.getD k 0) := by
  rintro ⟨s, h, n, hnt, hz⟩
  have hh8 : gens.h_vec.length = 8 := hh
  have hz' : s • gens.g + ∑ i : Fin gens.h_vec.length, h i • gens.h_vec[i] +
      ∑ j : Fin gens.g_vec.length, n j • gens.g_vec[j] = 0 := by
    rw [← hz]
    simp only [Spec.commit, Spec.NormLinear.msm, CircuitParams.nm_toSpec]
    rw [← hh8, ← hg, Finset.sum_range, Finset.sum_range]
    simp
  obtain ⟨hs, hh0, hn0⟩ := hind s _ _ hz'
  rcases hnt with h1 | ⟨j, hj, hj'⟩ | ⟨j, hj, hj'⟩
  · exact h1 hs
  · exact hj' (by simpa using congrFun hh0 ⟨j, by omega⟩)
  · exact hj' (by simpa using congrFun hn0 ⟨j, by simp at hj; omega⟩)

/-! ## The theorem -/

variable (F E) in
/-- The old statement: with independent generators, each commitment opens to some value in the
range. -/
def RangeSoundnessOfIndependent : Prop :=
  ∀ (generators : ℕ → Result (Generators E)) (commitments : List (PedersenCommitment E))
    (range : Range) (dst : List ℕ) (params : CircuitParams) (gens : Generators E) (G H : E),
    CircuitParams.new range commitments.length = .ok params →
    generators params.nm = .ok gens →
    gens.h_vec.length = H_LEN → gens.g_vec.length = params.nm →
    gens.g = H → gens.h_vec.getD 0 0 = G →
    LargeChar F params →
    ∀ t : NestedTree F E params,
      (∀ a r b l i, ∀ p ∈ (t.nla a r b l i).transcripts,
        Accepted generators commitments range dst (t.run a r b l i p)) →
      Independent (F := F) gens →
      ∀ c ∈ commitments, ∃ (v : ℕ) (s : F),
        range.is_in_range v = true ∧ c = PedersenCommitment.new G H (v : F) s

theorem range_sound_of_independent : RangeSoundnessOfIndependent F E := by
  intro generators commitments range dst params gens G H hparams hgens hh hg hgH hhG hchar t hacc
    hind
  -- A run exists, and `verify_batch` rejects an empty batch.
  have hc : commitments ≠ [] := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (transcripts_ne_nil (t.nla 0 0 0 0 0))
    have h := hacc 0 0 0 0 0 p hp
    rintro rfl
    simp [Accepted, Bppp.RangeProof.verify_batch] at h
    cases h
  have hm : commitments.length ≠ 0 := by simpa using hc
  obtain ⟨params', hpn, hv, -, -, -⟩ := Bppp.RangeProof.params_new range commitments.length hm
  obtain rfl : params = params' := by rw [hparams] at hpn; exact Except.ok.inj hpn
  have hshape : params.nm = next_power_of_two (max params.n_d BASE) := by
    unfold CircuitParams.new at hparams
    split_ifs at hparams
    cases hparams
    rfl
  -- The indexed families of Jonas's statement.
  let τf := fun a r b l => (((t.next a).next r).next b).next l
  have hmain := Bppp.RangeProof.verify_extract generators commitments range dst gens params hgens
    hparams hv hh hg G H hgH hhG hc
    (by exact_mod_cast hchar.cast_ne_zero 2 (by norm_num) (by unfold Nd; omega))
    (fun k hk hk' => hchar.cast_ne_zero k hk (by
      simp only [CircuitParams.toSpec, Spec.Params.Nd] at hk'; unfold Nd; omega)) t.cO t.cL (fun a => (t.next a).cR)
    (fun a r b l => (τf a r b l).cS) t.α (fun a r => (t.next a).ρ r) (fun a r => (t.next a).δ r)
    (fun a r b => ((t.next a).next r).β b) (fun a r b l => (((t.next a).next r).next b).lam l)
    (fun a r b l => (τf a r b l).τ)
    (fun i j h => by_contra fun hij => t.hDistinct i j hij h)
    (fun a i j h => by_contra fun hij => (t.next a).hSqDistinct i j hij (by simpa [sq] using h))
    (fun a r i j h => by
      by_contra hij
      have := ((t.next a).next r).hDistinct
      fin_cases i <;> fin_cases j <;> simp_all)
    (fun a r b i j h => by_contra fun hij => (((t.next a).next r).next b).hDistinct i j hij h)
    (fun a r b l i j h => by_contra fun hij => (τf a r b l).hDistinct i j hij h)
    t.hPole (fun a r => (t.next a).hNonzero r) (fun a r => (t.next a).hδNonzero r)
    (fun a r b l i => (τf a r b l).hNonzero i)
    (fun a r b l i => toTree (t.nla a r b l i)) (NLA.numRounds H_LEN params.nm)
    (fun a r b l i => depth_toTree _) (fun a r b l i => distinct_toTree _)
    (by rw [hshape]; exact NLA.two_pow_numRounds_dvd_nm _)
    (by
      intro a r b l i q hq
      obtain ⟨p, hp, rfl⟩ := paths_toTree _ q hq
      have hrun := hacc a r b l i p hp
      set run := t.run a r b l i p with hrun_def
      refine ⟨run.proof, run.oracle, ?_⟩
      intro tr
      have hγ : NormLinear.gammasOf ((Circuit.afterTau tr commitments run.proof.proof).extend
          [.message "dom-sep" ("norm_linear".toList.map Char.toNat)]) (nlaProof p).rounds =
          gammas p := by
        rw [gammasOf_eq run _ _ 0 rfl (countP_isGamma_afterTau run dst range.bits commitments _)
          (by simp [run, NestedTree.run, length_gammas])]
        simp [run, NestedTree.run, ← length_gammas]
      refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, hγ.symm, rfl, hrun⟩ <;>
        simp [tr, run, τf, Run.oracle, NestedTree.run, Circuit.alphaLog, Circuit.rhoLog,
          Circuit.lamLog, Circuit.betaLog, Circuit.deltaLog, Circuit.tauLog])
  rcases hmain with ⟨v, s, hvs⟩ | hrel
  · intro c hcm
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hcm
    obtain ⟨hin, heq⟩ := hvs i hi
    exact ⟨v i, s i, hin, by simpa [List.getElem?_eq_getElem hi] using heq⟩
  · exact absurd hrel (not_relation params gens hv hh hg hind)

end Audit.RangeProof
