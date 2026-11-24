import Audit.«01-TreeSoundness»

/-!
# Reductions

This file defines reductions between relations, their tree special soundness, and their
composition with a proof system.

Why it exists:
- Bulletproofs++ is a chain of steps. Each step turns a statement into a smaller statement. A
  `Reduction` is one such step, and `Reduction.comp` joins it to the next part. So each step can
  have its own small statement.

How it works:
1. A `Reduction` from `In` to `Out` has round types (`Audit/01-TreeSoundness.lean`), and a function
   `reduce` that computes the new statement from the old statement and the transcript.
2. `Reduction.SpecialSound`: take a statement `x` and a fork tree. At each leaf, take a relaxed
   witness for the new statement of its path. From these, the extractor computes a relaxed
   witness for `x`.
3. `Reduction.comp` runs a reduction, then a proof system on the new statement. The result is a
   proof system for the first relation. `Audit/Reductions/Compose.lean` proves that it is special
   sound when both parts are.
4. `ProofSystem.sendWitness` is the simplest proof system: the prover sends the witness in the
   clear. It ends a chain of reductions that made the witness small.
5. `Reduction.Complete`: the honest prover outputs a witness for the new statement.

The example at the end is a reduction from two discrete logarithms to one.

Assumptions:
- A reduction is a "reduction of knowledge" in the sense of Kothapalli and Parno, with special
  soundness in place of knowledge soundness.
- The verifier of a reduction rejects nothing. It only computes the new statement.
- Each round ends with a challenge. A last message of the prover with no challenge after it can
  use a round with the challenge type `Unit` and one child.
- The assumptions of `Audit/01-TreeSoundness.lean` also hold here.
-/

namespace Audit.TreeSoundness

/-! ## Reductions -/

/-- A public-coin protocol that turns a statement for `In` into a statement for `Out`. The
prover sends no response. The verifier computes the new statement with `reduce`. -/
structure Reduction (In Out : Relation) where
  /-- The rounds of the protocol. -/
  roundTypes : RoundTypes
  /-- The verifier: the new statement, from the old statement and the transcript. -/
  reduce : In.StatementType → roundTypes.Transcript → Out.StatementType

/-- A fork tree of a reduction with the fork rules `rules`. Each leaf holds a witness for the
new statement of its path. The prover does not send it. -/
abbrev Reduction.ForkTree {In Out : Relation} (red : Reduction In Out)
    (rules : red.roundTypes.ForkRules) : Type :=
  red.roundTypes.ForkTree rules Out.WitnessType

/-- Tree special soundness of a reduction with the fork rules `rules`: from every statement `x`
and every fork tree whose leaves hold relaxed witnesses for the new statements, `extract`
computes a witness for `x`. -/
def Reduction.SpecialSound {In Out : Relation} (red : Reduction In Out)
    (rules : red.roundTypes.ForkRules)
    (extract : In.StatementType → red.ForkTree rules → In.WitnessType) :
    Prop :=
  ∀ (x : In.StatementType) (t : red.ForkTree rules),
    t.AllPaths (fun tr w => Out.RelaxedRel (red.reduce x tr) w) →
    In.RelaxedRel x (extract x t)

/-- The rounds of `p`, then the rounds of `q`. -/
@[reducible] def RoundTypes.append (p q : RoundTypes) : RoundTypes :=
  match p with
  | .done => q
  | .round Commitment Challenge rest => .round Commitment Challenge (rest.append q)

/-- A transcript of `p.append q`, cut into its part for `p` and its part for `q`. -/
def RoundTypes.Transcript.split {p q : RoundTypes} (tr : (p.append q).Transcript) :
    p.Transcript × q.Transcript :=
  match p with
  -- No rounds of `p`: all of `tr` is for `q`.
  | .done => ((), tr)
  -- One round of `p`: keep `a` and `c` for `p`, then split the rest.
  | .round _ _ _ =>
      let (a, c, trRest) := tr
      let (trP, trQ) := split trRest
      ((a, c, trP), trQ)

/-- Run `red`, then run `S` on the new statement. The result is a proof system for `In`. -/
def Reduction.comp {In Out : Relation} (red : Reduction In Out) (S : ProofSystem Out) :
    ProofSystem In where
  roundTypes := red.roundTypes.append S.roundTypes
  ResponseType := S.ResponseType
  Verify x tr z := S.Verify (red.reduce x tr.split.1) tr.split.2 z

/-- The prover sends the witness in the clear, and the verifier checks `Rel`. It has no rounds.
It is the last part of a chain of reductions that made the witness small. -/
def ProofSystem.sendWitness (R : Relation) : ProofSystem R where
  roundTypes := .done
  ResponseType := R.WitnessType
  Verify x _ w := R.Rel x w

/-! ## The honest prover of a reduction -/

structure Reduction.HonestProver {In Out : Relation} (red : Reduction In Out) where
  /-- The type of the random coins of the prover. -/
  CoinsType : Type
  /-- The strategy of the prover. At the end, it keeps the new witness. It does not send it. -/
  prove : In.StatementType → In.WitnessType → CoinsType → red.roundTypes.Strategy Out.WitnessType

/-- Completeness of a reduction: for every witness `w` with `In.Rel x w`, every choice of coins
and every tuple of challenges, the new witness is a witness for the new statement. -/
def Reduction.Complete {In Out : Relation} (red : Reduction In Out) (P : red.HonestProver) :
    Prop :=
  ∀ (x : In.StatementType) (w : In.WitnessType), In.Rel x w →
    ∀ (coins : P.CoinsType) (cs : red.roundTypes.Challenges),
      let (tr, w') := red.roundTypes.run (P.prove x w coins) cs
      Out.Rel (red.reduce x tr) w'

namespace SchnorrExample

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-! ### Example: two discrete logarithms, by a reduction to one

The statement is `(G, X₁, X₂)`. The verifier sends a challenge `c`, and the new statement is
`(G, X₁ + c • X₂)`. The prover sends nothing in this round. Its new witness is `w₁ + c w₂`. Two
new witnesses `z₀`, `z₁` for different `c` give `w₂ = (z₀ - z₁) / (c₀ - c₁)` and
`w₁ = z₀ - c₀ w₂`. Then Schnorr can prove the new statement: `Audit/Reductions/Compose.lean`
shows that the composition is special sound. -/

variable (F E) in
/-- Two discrete logarithms with the same base: the statement is `(G, X₁, X₂)`, and the witness
is `(w₁, w₂)` with `w₁ • G = X₁` and `w₂ • G = X₂`. -/
@[reducible] def twoDlog : Relation where
  StatementType := E × E × E
  WitnessType := F × F
  Rel := fun (G, X₁, X₂) (w₁, w₂) => w₁ • G = X₁ ∧ w₂ • G = X₂
  RelaxedRel := fun (G, X₁, X₂) (w₁, w₂) => w₁ • G = X₁ ∧ w₂ • G = X₂

variable (F) in
/-- One round: no commitment, then the challenge `c : F`. -/
def batchRounds : RoundTypes := .round Unit F .done

variable (F E) in
/-- The reduction from `twoDlog` to `dlog`: the new statement is `(G, X₁ + c • X₂)`. -/
@[reducible] def batch : Reduction (twoDlog F E) (dlog F E) where
  roundTypes := batchRounds F
  reduce := fun (G, X₁, X₂) ((), c, ()) => (G, X₁ + c • X₂)

variable (F) in
/-- The fork rule: 2 distinct challenges. -/
def batchRules : (batchRounds F).ForkRules := (⟨2, (· ≠ ·)⟩, ())

/-- The extractor: `w₂ = (z₀ - z₁) / (c₀ - c₁)` and `w₁ = z₀ - c₀ w₂`. -/
def batchExtract (_ : E × E × E) (t : (batch F E).ForkTree (batchRules F)) : F × F :=
  let c := t.challenges.val
  let z := t.children
  let w₂ := (z 0 - z 1) / (c 0 - c 1)
  (z 0 - c 0 * w₂, w₂)

/-- The reduction is special sound with 2 challenges. -/
theorem batch_sound : (batch F E).SpecialSound (batchRules F) batchExtract := by
  rintro ⟨G, X₁, X₂⟩ ⟨⟨⟩, ⟨c, hc⟩, z⟩ hacc
  -- The tree has 2 paths. At each leaf, `z i` is a witness for `(G, X₁ + c i • X₂)`.
  have h0 : z 0 • G = X₁ + c 0 • X₂ := hacc (0 : Fin 2)
  have h1 : z 1 • G = X₁ + c 1 • X₂ := hacc (1 : Fin 2)
  have hne : c 0 - c 1 ≠ 0 := sub_ne_zero.2 (hc 0 1 (by decide : (0 : Fin 2) ≠ 1))
  -- Subtract the two equations to get `w₂`. Then `w₁` follows from the first equation.
  have key : (z 0 - z 1) • G = (c 0 - c 1) • X₂ := by
    rw [sub_smul, sub_smul, h0, h1]; abel
  have h2 : ((z 0 - z 1) / (c 0 - c 1)) • G = X₂ := by
    rw [div_eq_inv_mul, mul_smul, key, smul_smul, inv_mul_cancel₀ hne, one_smul]
  show (z 0 - c 0 * ((z 0 - z 1) / (c 0 - c 1))) • G = X₁ ∧ ((z 0 - z 1) / (c 0 - c 1)) • G = X₂
  refine ⟨?_, h2⟩
  rw [sub_smul, mul_smul, h2, h0]; abel

/-- The honest prover: no coins, and the new witness `w₁ + c w₂`. -/
@[reducible] def batchHonest : (batch F E).HonestProver where
  CoinsType := Unit
  prove := fun _ (w₁, w₂) () => ((), fun c => w₁ + c * w₂)

/-- The reduction is complete: `(w₁ + c w₂) • G = X₁ + c • X₂`. -/
theorem batch_complete : (batch F E).Complete batchHonest := by
  rintro ⟨G, X₁, X₂⟩ ⟨w₁, w₂⟩ ⟨h₁, h₂⟩ ⟨⟩ ⟨c, ⟨⟩⟩
  show (w₁ + c * w₂) • G = X₁ + c • X₂
  rw [add_smul, mul_smul, h₁, h₂]

end SchnorrExample

end Audit.TreeSoundness
