import Audit.«02-Reductions»

/-!
# The composition of special soundness

This file proves that `Reduction.comp` keeps special soundness: if a reduction and a proof system
are special sound, then their composition is special sound.

Why it exists:
- A protocol such as Bulletproofs++ is a chain of reductions, then a proof system. With this
  theorem, each part has its own soundness proof, and the proofs join without more work.

How it works:
1. `RoundTypes.appendRules`: the fork rules of the reduction, then the fork rules of the proof
   system.
2. `RoundTypes.Tree.split`: a fork tree of the composition is a fork tree of the reduction with a
   fork tree of the proof system at each leaf.
3. `RoundTypes.Tree.mapLeaves`: change each leaf of a tree. The change can read the messages of
   the path to the leaf.
4. `Reduction.compExtract`: at each leaf of the reduction tree, run the extractor of the proof
   system on the new statement of that path. Then run the extractor of the reduction.
5. `Reduction.comp_specialSound`: the composition is special sound with `compExtract`.
6. `ProofSystem.sendWitness_specialSound`: sending the witness is special sound when `Rel`
   implies `RelaxedRel`.

Assumptions:
- None beyond those of `Audit/01-TreeSoundness.lean` and `Audit/02-Reductions.lean`. The theorem is
  true for every reduction and every proof system.
-/

namespace Audit.TreeSoundness

/-! ## Fork rules and trees of a composition -/

/-- The fork rules of `p`, then the fork rules of `q`. -/
def RoundTypes.appendRules : {p q : RoundTypes} → p.ForkRules → q.ForkRules →
    (p.append q).ForkRules
  | .done, _, (), gs => gs
  | .round _ _ _, _, (f, fs), gs => (f, appendRules fs gs)

/-- A tree of `p.append q`, as a tree of `p` with a tree of `q` at each leaf. -/
def RoundTypes.Tree.split : {p q : RoundTypes} → {fs : p.ForkRules} → {gs : q.ForkRules} →
    {Leaf : Type} → (p.append q).Tree (RoundTypes.appendRules fs gs) Leaf →
    p.Tree fs (q.Tree gs Leaf)
  | .done, _, (), _, _, t => t
  | .round _ _ _, _, (_, _), _, _, (a, c, sub) => (a, c, fun i => split (sub i))

/-- Apply `f` to each leaf. `f` also gets the messages of the path to the leaf. -/
def RoundTypes.Tree.mapLeaves : {p : RoundTypes} → {fs : p.ForkRules} → {Leaf Leaf' : Type} →
    p.Tree fs Leaf → (p.Transcript Unit → Leaf → Leaf') → p.Tree fs Leaf'
  | .done, _, _, _, z, f => f () z
  | .round _ _ _, (_, _), _, _, (a, c, sub), f =>
      (a, c, fun i => mapLeaves (sub i) fun m z => f (a, c.1 i, m) z)

/-- The extractor of a composition: at each leaf of the reduction tree, run `extractS` on the new
statement of that path. Then run `extractRed` on the resulting tree. -/
def Reduction.compExtract {In Out : Relation} (red : Reduction In Out) (S : ProofSystem Out)
    {fs : red.roundTypes.ForkRules} {gs : S.roundTypes.ForkRules}
    (extractRed : In.StatementType → red.roundTypes.Tree fs Out.WitnessType → In.WitnessType)
    (extractS : Out.StatementType → S.roundTypes.Tree gs S.ResponseType → Out.WitnessType)
    (x : In.StatementType)
    (t : (red.comp S).roundTypes.Tree (RoundTypes.appendRules fs gs) (red.comp S).ResponseType) :
    In.WitnessType :=
  extractRed x (t.split.mapLeaves fun m t' => extractS (red.reduce x m) t')

/-! ## Transcripts of a composition -/

/-- The transcripts of a node: a child `i`, and a transcript of its subtree. -/
theorem RoundTypes.Tree.mem_transcripts_round {C Ch : Type} {rest : RoundTypes} {f : ForkRule Ch}
    {fs : rest.ForkRules} {Leaf : Type} (a : C) (c : {c : Fin f.arity → Ch // f.Allowed c})
    (sub : Fin f.arity → rest.Tree fs Leaf) (u : (RoundTypes.round C Ch rest).Transcript Leaf) :
    u ∈ RoundTypes.Tree.transcripts (p := .round C Ch rest) (fs := (f, fs)) (a, c, sub) ↔
      ∃ i, ∃ u' ∈ (sub i).transcripts, u = (a, c.1 i, u') := by
  simp only [RoundTypes.Tree.transcripts, List.mem_flatMap, List.mem_finRange, List.mem_map,
    true_and]
  constructor
  · rintro ⟨i, u', hu', rfl⟩; exact ⟨i, u', hu', rfl⟩
  · rintro ⟨i, u', hu', rfl⟩; exact ⟨i, u', hu', rfl⟩

/-- A transcript of `t.mapLeaves f` comes from a transcript `v` of `t`. It has the messages of
`v`, and its last value is `f` of the messages and the last value of `v`. -/
theorem RoundTypes.Tree.mem_mapLeaves : ∀ {p : RoundTypes} {fs : p.ForkRules} {Leaf Leaf' : Type}
    (t : p.Tree fs Leaf) (f : p.Transcript Unit → Leaf → Leaf') (u : p.Transcript Leaf'),
    u ∈ (t.mapLeaves f).transcripts →
      ∃ v ∈ t.transcripts, u.messages = v.messages ∧ u.last = f v.messages v.last
  | .done, _, _, _, z, f, u, hu => by
    simp only [mapLeaves, transcripts, List.mem_singleton] at hu
    exact ⟨z, List.mem_singleton_self z, rfl, hu⟩
  | .round _ _ rest, (_, _), _, _, (a, c, sub), f, u, hu => by
    obtain ⟨i, u', hu', rfl⟩ := (mem_transcripts_round _ _ _ u).1 hu
    obtain ⟨v', hv', hm, hl⟩ := mem_mapLeaves (sub i) _ u' hu'
    refine ⟨(a, c.1 i, v'), (mem_transcripts_round _ _ _ _).2 ⟨i, v', hv', rfl⟩, ?_, hl⟩
    simp only [RoundTypes.Transcript.messages, hm]

/-- A transcript `v` of `t.split`, joined with a transcript `w` of the tree at its leaf, is a
transcript of `t`. Its split gives back the messages of `v`, and `w`. -/
theorem RoundTypes.Tree.mem_split : ∀ {p q : RoundTypes} {fs : p.ForkRules} {gs : q.ForkRules}
    {Leaf : Type} (t : (p.append q).Tree (RoundTypes.appendRules fs gs) Leaf)
    (v : p.Transcript (q.Tree gs Leaf)), v ∈ t.split.transcripts → ∀ w ∈ v.last.transcripts,
      ∃ tr ∈ t.transcripts, tr.split = (v.messages, w)
  | .done, _, (), _, _, t, v, hv, w, hw => by
    obtain rfl := List.mem_singleton.1 hv
    exact ⟨w, hw, rfl⟩
  | .round _ _ rest, _, (_, _), _, _, (a, c, sub), v, hv, w, hw => by
    obtain ⟨i, v', hv', rfl⟩ := (mem_transcripts_round _ _ _ v).1 hv
    obtain ⟨tr, htr, hs⟩ := mem_split (sub i) v' hv' w hw
    refine ⟨(a, c.1 i, tr), (mem_transcripts_round _ _ _ _).2 ⟨i, tr, htr, rfl⟩, ?_⟩
    simp only [RoundTypes.Transcript.split, RoundTypes.Transcript.messages, hs]

/-! ## The theorem -/

/-- If the reduction and the proof system are special sound, then their composition is special
sound, with the fork rules of both and with `compExtract`. -/
theorem Reduction.comp_specialSound {In Out : Relation} (red : Reduction In Out)
    (S : ProofSystem Out) {fs : red.roundTypes.ForkRules} {gs : S.roundTypes.ForkRules}
    {extractRed : In.StatementType → red.roundTypes.Tree fs Out.WitnessType → In.WitnessType}
    {extractS : Out.StatementType → S.roundTypes.Tree gs S.ResponseType → Out.WitnessType}
    (hRed : red.SpecialSound fs extractRed) (hS : S.SpecialSound gs extractS) :
    (red.comp S).SpecialSound (RoundTypes.appendRules fs gs)
      (red.compExtract S extractRed extractS) := by
  intro x t hacc
  apply hRed
  intro u hu
  obtain ⟨v, hv, hm, hl⟩ := RoundTypes.Tree.mem_mapLeaves _ _ u hu
  rw [hm, hl]
  apply hS
  intro w hw
  obtain ⟨tr, htr, hs⟩ := RoundTypes.Tree.mem_split t v hv w hw
  have h : S.Verify (red.reduce x tr.split.1) tr.split.2 := hacc tr htr
  rw [hs] at h
  exact h

/-- Sending the witness is special sound: the extractor reads the leaf. -/
theorem ProofSystem.sendWitness_specialSound (R : Relation)
    (h : ∀ x w, R.Rel x w → R.RelaxedRel x w) :
    (ProofSystem.sendWitness R).SpecialSound () (fun _ w => w) :=
  fun x w hacc => h x w (hacc w (List.mem_singleton_self w))

/-! ## Test: two discrete logarithms, by `batch` and then Schnorr -/

namespace SchnorrExample

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-- The composition has 2 rounds: the challenge `c`, then `R` and the challenge of Schnorr. -/
example : ((batch F E).comp (schnorrSystem F E)).roundTypes = .round Unit F (.round E F .done) :=
  rfl

/-- The composition is special sound with 2 challenges in each round, so with 4 transcripts. -/
example : ((batch F E).comp (schnorrSystem F E)).SpecialSound
    (RoundTypes.appendRules (batchRules F) (rules F E))
    ((batch F E).compExtract (schnorrSystem F E) batchExtract extract) :=
  Reduction.comp_specialSound _ _ batch_sound schnorr_sound

end SchnorrExample

end Audit.TreeSoundness
