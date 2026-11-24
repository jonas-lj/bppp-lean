import Mathlib

/-!
# Tree special soundness

This file defines public-coin proof systems and their tree special soundness. It does not mention
a specific protocol.

Why it exists:
- A soundness statement must say what "sound" means. This file gives the textbook meaning, so
  that a reader can check it once.
- `Audit/Reductions.lean` builds on it: a reduction is a step that turns a statement into a
  smaller statement.
- `Audit/RangeProof.lean` uses it for the Bulletproofs++ range proof.

How it works:
1. A `Relation` is a relation `Rel` between statements and witnesses, and a relaxed form
   `RelaxedRel`. Completeness uses `Rel`. Soundness uses `RelaxedRel`.
2. `RoundTypes` lists the rounds of a protocol, with the types of their messages. In each
   round, the prover sends a commitment, and the verifier answers with a random challenge. The
   challenge type of a round is the set from which the verifier samples. It excludes the
   challenges for which the verifier cannot compute, for example a division by zero.
3. A `RoundTypes.Transcript` is one run: the commitments and the challenges in order, then one
   last value. For a proof system, the last value is the response of the prover.
4. A `RoundTypes.Tree` is a fork tree. In each round, a node has one commitment and several
   children, each with its own challenge. So all transcripts below a node share the commitments
   above it. A `ForkRule` gives the number of children in each round, and a rule for the
   challenges of two different children.
5. A `ProofSystem` for a relation has round types, a response type and a verifier `Verify`.
   `ProofSystem.SpecialSound`: from every statement `x` and every fork tree in which the verifier
   accepts every transcript, the extractor computes a witness `w` with `RelaxedRel x w`.
6. The honest prover gives a strategy (`RoundTypes.Strategy`): a commitment, then a strategy for
   the rest for each challenge. `ProofSystem.Complete`: for a witness `w` with `Rel x w`, the
   verifier accepts each transcript of the honest prover. Soundness does not use the prover.
7. Sizes, such as the length of a vector, are fixed outside. So there is one system for each
   size.

The examples at the end show the types for a Σ-protocol, and Schnorr as a proof system.

Assumptions:
- This is the `(k₁, …, k_μ)`-special soundness of Attema, Cramer and Kohl, when each `ForkRule`
  has `Apart = (· ≠ ·)`. The challenge type of a round is its challenge set.
- A challenge type can exclude a few bad values of a larger set, for example `0` of a field. A
  forking lemma and a completeness error must count them.
- Special soundness has no probabilities. So a protocol does not say how the verifier samples a
  challenge. Knowledge soundness also needs a forking lemma.
- The definition cannot stop an extractor that uses choice, for example "a witness, if one
  exists". Such an extractor makes the statement say only "a witness exists". So a statement must
  name an extractor that is computable and works for every field and group.
- If the fork rules allow no tree, then `SpecialSound` holds for every extractor. So each use
  must check that a tree exists: enough allowed challenges in each round.
- If the coin type of an honest prover is empty, then `Complete` holds for every prover. So a
  statement must use a coin type that has values.
-/

namespace Audit.TreeSoundness

/-! ## Relations -/

/-- A relation between statements and witnesses, with a relaxed form for soundness. -/
structure Relation where
  /-- The public input. -/
  StatementType : Type
  /-- The secret input of the prover. -/
  WitnessType : Type
  /-- The relation of the honest prover: `w` is a witness for `x`. Completeness uses it. -/
  Rel : StatementType → WitnessType → Prop
  /-- The relation that the extractor must meet. It is `Rel`, or a break of a hardness
  assumption, for example a link between generators. Soundness uses it. -/
  RelaxedRel : StatementType → WitnessType → Prop

/-! ## Rounds, transcripts and fork trees -/

/-- The types of the messages of a public-coin protocol, round by round. In each round, the
prover sends a commitment of type `Commitment`, and the verifier answers with a random challenge
of type `Challenge`. A Σ-protocol has one round: `.round Commitment Challenge .done`. -/
inductive RoundTypes : Type 1
  /-- No more rounds. -/
  | done
  /-- The prover sends a commitment, the verifier sends a challenge, and `rest` follows. -/
  | round (Commitment Challenge : Type) (rest : RoundTypes)

/-- One run: the commitments and the challenges in order, then one last value of type `Last`. -/
@[reducible] def RoundTypes.Transcript : RoundTypes → Type → Type
  | .done, Last => Last
  | .round Commitment Challenge rest, Last => Commitment × Challenge × rest.Transcript Last

/-- The commitments and the challenges of a transcript, without its last value. -/
def RoundTypes.Transcript.messages : {p : RoundTypes} → {Last : Type} → p.Transcript Last →
    p.Transcript Unit
  | .done, _, _ => ()
  | .round _ _ _, _, (a, c, rest) => (a, c, messages rest)

/-- The last value of a transcript. -/
def RoundTypes.Transcript.last : {p : RoundTypes} → {Last : Type} → p.Transcript Last → Last
  | .done, _, z => z
  | .round _ _ _, _, (_, _, rest) => last rest

/-- The rules for one round of a fork tree: the number of children, and a rule for the
challenges of each pair of different children. With `Apart = (· ≠ ·)` in each round, this is the
`(k₁, …, k_μ)`-special soundness of Attema, Cramer and Kohl. -/
structure ForkRule (Challenge : Type) where
  /-- The number of children of each node in this round, each with its own challenge. -/
  arity : ℕ
  /-- A rule for the challenges of two different children. -/
  Apart : Challenge → Challenge → Prop

/-- The challenges `c` of the children of one node follow the rule `f`. -/
def ForkRule.Allowed {Challenge : Type} (f : ForkRule Challenge) (c : Fin f.arity → Challenge) :
    Prop :=
  ∀ i j, i ≠ j → f.Apart (c i) (c j)

/-- One `ForkRule` for each round of a protocol, for the challenge type of that round. -/
@[reducible] def RoundTypes.ForkRules : RoundTypes → Type
  | .done => Unit
  | .round _ Challenge rest => ForkRule Challenge × rest.ForkRules

/-- A fork tree of a protocol. In each round: one commitment, then the challenges of the
`arity` children (they follow the rule), then the subtrees of the children. At each leaf: one
value of type `Leaf`. -/
@[reducible] def RoundTypes.Tree : (p : RoundTypes) → p.ForkRules → Type → Type
  | .done, _, Leaf => Leaf
  | .round Commitment Challenge rest, (f, fs), Leaf =>
      Commitment × {c : Fin f.arity → Challenge // f.Allowed c} × (Fin f.arity → rest.Tree fs Leaf)

/-- The transcripts of a tree: one for each path from the root to a leaf. -/
def RoundTypes.Tree.transcripts : {p : RoundTypes} → {fs : p.ForkRules} → {Leaf : Type} →
    p.Tree fs Leaf → List (p.Transcript Leaf)
  | .done, _, _, z => [z]
  | .round _ _ _, _, _, (a, ⟨c, _⟩, sub) =>
      -- For each child `i`: put `a` and its challenge `c i` in front of each transcript of its
      -- subtree `sub i`. Then join the lists of all children.
      (List.finRange _).flatMap fun i => (transcripts (sub i)).map fun tr => (a, c i, tr)

/-! ## Proof systems -/

/-- A public-coin protocol for the relation `R`: the rounds, then a response, then a check. -/
structure ProofSystem (R : Relation) where
  /-- The rounds of the protocol. -/
  roundTypes : RoundTypes
  /-- The type of the last message of the prover. -/
  ResponseType : Type
  /-- The verifier: it accepts or rejects one transcript for the statement `x`. -/
  Verify : R.StatementType → roundTypes.Transcript ResponseType → Prop

/-- Tree special soundness with the fork rules `fs`: from every statement `x` and every fork tree
in which `Verify` accepts every transcript, `extract` computes a witness for `x`. -/
def ProofSystem.SpecialSound {R : Relation} (S : ProofSystem R) (fs : S.roundTypes.ForkRules)
    (extract : R.StatementType → S.roundTypes.Tree fs S.ResponseType → R.WitnessType) : Prop :=
  ∀ x t, (∀ tr ∈ t.transcripts, S.Verify x tr) → R.RelaxedRel x (extract x t)

/-! ## The honest prover

Soundness does not use it. Completeness does. -/

/-- A prover strategy: a commitment, then a strategy for the rest for each challenge. At the end:
a value of type `Last`. -/
@[reducible] def RoundTypes.Strategy : RoundTypes → Type → Type
  | .done, Last => Last
  | .round Commitment Challenge rest, Last => Commitment × (Challenge → rest.Strategy Last)

/-- One challenge for each round, as a tuple. -/
@[reducible] def RoundTypes.Challenges : RoundTypes → Type
  | .done => Unit
  | .round _ Challenge rest => Challenge × rest.Challenges

/-- The transcript of a strategy on the challenges `cs`. -/
def RoundTypes.run : {p : RoundTypes} → {Last : Type} → p.Strategy Last → p.Challenges →
    p.Transcript Last
  | .done, _, z, _ => z
  | .round _ _ _, _, (a, next), (c, cs) => (a, c, run (next c) cs)

/-- An honest prover: from the statement, the witness and its random coins, a strategy. -/
structure ProofSystem.HonestProver {R : Relation} (S : ProofSystem R) where
  /-- The type of the random coins of the prover. -/
  CoinsType : Type
  /-- The strategy of the prover. At the end, it sends the response. -/
  prove : R.StatementType → R.WitnessType → CoinsType → S.roundTypes.Strategy S.ResponseType

/-- Completeness: for every witness `w` with `Rel x w`, every choice of coins and every tuple of
challenges, the verifier accepts the transcript of the honest prover. -/
def ProofSystem.Complete {R : Relation} (S : ProofSystem R) (P : S.HonestProver) : Prop :=
  ∀ x w, R.Rel x w → ∀ coins cs, S.Verify x (S.roundTypes.run (P.prove x w coins) cs)

/-! ### Example: a Σ-protocol with 3 challenges

The commitment, the challenge and the response are all in `ℕ`. The functions above compute
these types. -/

namespace SigmaExample

/-- One round. -/
def sigma : RoundTypes := .round ℕ ℕ .done

/-- One run with the response in `ℕ` is `(commitment, challenge, response)`. -/
example : sigma.Transcript ℕ = (ℕ × ℕ × ℕ) := rfl

/-- One rule: 3 distinct challenges. -/
def rules : sigma.ForkRules := (⟨3, (· ≠ ·)⟩, ())

/-- A tree is one commitment, then the 3 distinct challenges, then the 3 responses. -/
example : sigma.Tree rules ℕ =
    (ℕ × {c : Fin 3 → ℕ // rules.1.Allowed c} × (Fin 3 → ℕ)) := rfl

/-- The tree with the commitment 7, the challenges 10, 11, 12 and the responses 100, 101, 102. -/
def tree : sigma.Tree rules ℕ :=
  (7, ⟨fun i => 10 + (i : ℕ), by unfold ForkRule.Allowed; decide⟩, fun i => 100 + (i : ℕ))

/-- It has 3 transcripts, which share the commitment 7. -/
example : tree.transcripts = [(7, 10, 100), (7, 11, 101), (7, 12, 102)] := rfl

end SigmaExample

/-! ### Example: Schnorr as a proof system

Schnorr proves knowledge of `w` with `X = w • G`. The prover sends `R`, the verifier sends `c`,
and the prover sends `z`. The verifier checks `z • G = R + c • X`. Two accepted transcripts with
the same `R` and different `c` give `w = (z₀ - z₁) / (c₀ - c₁)`. -/

namespace SchnorrExample

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

variable (F E) in
/-- The discrete logarithm: the statement is `(G, X)`, and the witness is `w` with `w • G = X`.
`Rel` and `RelaxedRel` are the same. -/
@[reducible] def dlog : Relation where
  StatementType := E × E
  WitnessType := F
  Rel := fun (G, X) w => w • G = X
  RelaxedRel := fun (G, X) w => w • G = X

variable (F E) in
/-- One round: the commitment `R : E` and the challenge `c : F`. -/
def schnorrRounds : RoundTypes := .round E F .done

variable (F E) in
/-- Schnorr as a proof system. The response is `z : F`. -/
@[reducible] def schnorrSystem : ProofSystem (dlog F E) where
  roundTypes := schnorrRounds F E
  ResponseType := F
  Verify := fun (G, X) (R, c, z) => z • G = R + c • X

/-! #### Soundness -/

variable (F E) in
/-- The fork rule: 2 distinct challenges. -/
def rules : (schnorrRounds F E).ForkRules := (⟨2, (· ≠ ·)⟩, ())

/-- The extractor: `w = (z₀ - z₁) / (c₀ - c₁)`. -/
def extract (_ : E × E) (t : (schnorrRounds F E).Tree (rules F E) F) : F :=
  let (_, ⟨c, _⟩, z) := t
  (z 0 - z 1) / (c 0 - c 1)

/-- Schnorr is special sound with 2 challenges. -/
theorem schnorr_sound : (schnorrSystem F E).SpecialSound (rules F E) extract := by
  rintro ⟨G, X⟩ ⟨R, ⟨c, hc⟩, z⟩ hacc
  -- The tree has 2 transcripts, and the verifier accepts both.
  have ht : ∀ i, (R, c i, z i) ∈ [(R, c 0, z 0), (R, c 1, z 1)] := by
    intro i; fin_cases i <;> simp
  have h0 : z 0 • G = R + c 0 • X := hacc _ (ht 0)
  have h1 : z 1 • G = R + c 1 • X := hacc _ (ht 1)
  -- Subtract the two checks.
  have key : (z 0 - z 1) • G = (c 0 - c 1) • X := by
    rw [sub_smul, sub_smul, h0, h1]; abel
  have hne : c 0 - c 1 ≠ 0 := sub_ne_zero.2 (hc 0 1 (by decide : (0 : Fin 2) ≠ 1))
  show ((z 0 - z 1) / (c 0 - c 1)) • G = X
  rw [div_eq_inv_mul, mul_smul, key, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-! #### Completeness -/

/-- The honest prover: with the coin `r`, send `R = r • G`. Then answer `c` with `z = r + c w`. -/
@[reducible] def honest : (schnorrSystem F E).HonestProver where
  CoinsType := F
  prove := fun (G, _) w r => (r • G, fun c => r + c * w)

/-- Schnorr is complete: `(r + c w) • G = r • G + c • X` when `w • G = X`. -/
theorem schnorr_complete : (schnorrSystem F E).Complete honest := by
  rintro ⟨G, X⟩ w (hX : w • G = X) r ⟨c, ⟨⟩⟩
  show (r + c * w) • G = r • G + c • X
  rw [← hX, add_smul, mul_smul]

end SchnorrExample

end Audit.TreeSoundness
