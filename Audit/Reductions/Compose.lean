import Audit.Reductions.Defs

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
2. `RoundTypes.ForkTree.split`: a fork tree of the composition is a fork tree of the reduction
   with a fork tree of the proof system at each leaf.
3. `RoundTypes.ForkTree.mapLeaves`: change each leaf of a tree. The change can read the messages
   of the path to the leaf.
4. `Reduction.compExtract`: at each leaf of the reduction tree, run the extractor of the proof
   system on the new statement of that path. Then run the extractor of the reduction.
5. `Reduction.comp_specialSound`: the composition is special sound with `compExtract`.
6. `ProofSystem.sendWitness_specialSound`: sending the witness is special sound when `Rel`
   implies `RelaxedRel`.

Assumptions:
- None beyond those of `Audit/01-TreeSoundness.lean` and `Audit/Reductions/Defs.lean`. The
  theorem is true for every reduction and every proof system.
-/

namespace Audit.TreeSoundness

/-! ## Fork rules and trees of a composition -/

/-- The fork rules of `p`, then the fork rules of `q`. -/
def RoundTypes.appendRules : {p q : RoundTypes} → p.ForkRules → q.ForkRules →
    (p.append q).ForkRules
  | .done, _, (), gs => gs
  | .round _ _ _, _, (f, fs), gs => (f, appendRules fs gs)

/-- A tree of `p.append q`, as a tree of `p` with a tree of `q` at each leaf. -/
def RoundTypes.ForkTree.split : {p q : RoundTypes} → {fs : p.ForkRules} → {gs : q.ForkRules} →
    {Leaf : Type} → (p.append q).ForkTree (RoundTypes.appendRules fs gs) Leaf →
    p.ForkTree fs (q.ForkTree gs Leaf)
  | .done, _, (), _, _, t => t
  | .round _ _ _, _, (_, _), _, _, ⟨a, c, sub⟩ => ⟨a, c, fun i => split (sub i)⟩

/-- Apply `f` to each leaf. `f` also gets the transcript of the path to the leaf. -/
def RoundTypes.ForkTree.mapLeaves : {p : RoundTypes} → {fs : p.ForkRules} → {Leaf Leaf' : Type} →
    p.ForkTree fs Leaf → (p.Transcript → Leaf → Leaf') → p.ForkTree fs Leaf'
  | .done, _, _, _, z, f => f () z
  | .round _ _ _, (_, _), _, _, ⟨a, c, sub⟩, f =>
      ⟨a, c, fun i => mapLeaves (sub i) fun m z => f (a, c.val i, m) z⟩

/-- The extractor of a composition: at each leaf of the reduction tree, run `extractS` on the new
statement of that path. Then run `extractRed` on the resulting tree. -/
def Reduction.compExtract {In Out : Relation} (red : Reduction In Out) (S : ProofSystem Out)
    {fs : red.roundTypes.ForkRules} {gs : S.roundTypes.ForkRules}
    (extractRed : In.StatementType → red.roundTypes.ForkTree fs Out.WitnessType → In.WitnessType)
    (extractS : Out.StatementType → S.roundTypes.ForkTree gs S.ResponseType → Out.WitnessType)
    (x : In.StatementType)
    (t : (red.comp S).ForkTree (RoundTypes.appendRules fs gs)) :
    In.WitnessType :=
  extractRed x (t.split.mapLeaves fun m t' => extractS (red.reduce x m) t')

/-! ## Paths of a composition -/

/-- A stronger check on every path gives a weaker check on every path. -/
theorem RoundTypes.ForkTree.AllPaths.mono :
    ∀ {p : RoundTypes} {fs : p.ForkRules} {Leaf : Type} {t : p.ForkTree fs Leaf}
    {P Q : p.Transcript → Leaf → Prop}, (∀ tr z, P tr z → Q tr z) → t.AllPaths P → t.AllPaths Q
  | .done, _, _, _, _, _, hPQ, h => hPQ _ _ h
  | .round _ _ _, (_, _), _, _, _, _, hPQ, h => fun i =>
      AllPaths.mono (fun _ _ => hPQ _ _) (h i)

/-- A check on every path of `t.mapLeaves f` follows from the check on every path of `t`, with
`f` applied to each leaf value. -/
theorem RoundTypes.ForkTree.allPaths_mapLeaves :
    ∀ {p : RoundTypes} {fs : p.ForkRules} {Leaf Leaf' : Type} (t : p.ForkTree fs Leaf)
    (f : p.Transcript → Leaf → Leaf') (check : p.Transcript → Leaf' → Prop),
    t.AllPaths (fun tr z => check tr (f tr z)) → (t.mapLeaves f).AllPaths check
  | .done, _, _, _, _, _, _, h => h
  | .round _ _ _, (_, _), _, _, ⟨_, _, sub⟩, _, _, h => fun i =>
      allPaths_mapLeaves (sub i) _ _ (h i)

/-- If a check reads the transcript of `p.append q` through its split, then it holds on every
path of `t` exactly when, on every path `v` of `t.split`, it holds on every path of the leaf tree
`t'` with `v` in front. -/
theorem RoundTypes.ForkTree.allPaths_split :
    ∀ {p q : RoundTypes} {fs : p.ForkRules} {gs : q.ForkRules} {Leaf : Type}
    (t : (p.append q).ForkTree (RoundTypes.appendRules fs gs) Leaf)
    (P : p.Transcript → q.Transcript → Leaf → Prop),
    t.AllPaths (fun tr z => P tr.split.1 tr.split.2 z) →
      t.split.AllPaths (fun v t' => t'.AllPaths (P v))
  | .done, _, (), _, _, _, _, h => h
  | .round _ _ _, _, (_, _), _, _, ⟨_, _, sub⟩, _, h => fun i =>
      allPaths_split (sub i) _ (h i)

/-! ## The theorem -/

/-- If the reduction and the proof system are special sound, then their composition is special
sound, with the fork rules of both and with `compExtract`. -/
theorem Reduction.comp_specialSound {In Out : Relation} (red : Reduction In Out)
    (S : ProofSystem Out) {fs : red.roundTypes.ForkRules} {gs : S.roundTypes.ForkRules}
    {extractRed : In.StatementType → red.roundTypes.ForkTree fs Out.WitnessType → In.WitnessType}
    {extractS : Out.StatementType → S.roundTypes.ForkTree gs S.ResponseType → Out.WitnessType}
    (hRed : red.SpecialSound fs extractRed) (hS : S.SpecialSound gs extractS) :
    (red.comp S).SpecialSound (RoundTypes.appendRules fs gs)
      (red.compExtract S extractRed extractS) := by
  intro x t hacc
  apply hRed
  apply RoundTypes.ForkTree.allPaths_mapLeaves
  -- Each leaf of `t.split` is a tree of `S` that `S.Verify` accepts. So `hS` applies.
  exact (RoundTypes.ForkTree.allPaths_split t (fun v w z => S.Verify (red.reduce x v) w z)
    hacc).mono fun v t' ht' => hS _ t' ht'

/-- Sending the witness is special sound: the extractor reads the leaf. -/
theorem ProofSystem.sendWitness_specialSound (R : Relation)
    (h : ∀ x w, R.Rel x w → R.RelaxedRel x w) :
    (ProofSystem.sendWitness R).SpecialSound () (fun _ w => w) :=
  fun x w hacc => h x w hacc

/-! ## Test: two discrete logarithms, by `batch` and then Schnorr -/

namespace SchnorrExample

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-- The composition has 2 rounds: the challenge `c`, then `R` and the challenge of Schnorr. -/
example : ((batch F E).comp (schnorrSystem F E)).roundTypes = .round Unit F (.round E F .done) :=
  rfl

/-- The composition is special sound with 2 challenges in each round, so with 4 paths. -/
example : ((batch F E).comp (schnorrSystem F E)).SpecialSound
    (RoundTypes.appendRules (batchRules F) (schnorrRules F E))
    ((batch F E).compExtract (schnorrSystem F E) batchExtract extract) :=
  Reduction.comp_specialSound _ _ batch_sound schnorr_sound

end SchnorrExample

end Audit.TreeSoundness
