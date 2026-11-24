import Mathlib

/-!
# Tree special soundness

This file defines public-coin proof systems and their tree special soundness. It does not mention
a specific protocol.

Why it exists:
- A soundness statement must say what "sound" means. This file gives the textbook meaning, so
  that a reader can check it once.
- `Audit/02-Reductions.lean` builds on it: a reduction is a step that turns a statement into a
  smaller statement.
- `Audit/05-RangeProof.lean` uses it for the Bulletproofs++ range proof.

How it works:
1. `Relation`: statements, witnesses, the relation `Rel` for completeness, and the relaxed
   relation `RelaxedRel` for soundness.
2. `RoundTypes`: the message types of a protocol, round by round.
3. `RoundTypes.Transcript`: the messages of one run.
4. `RoundTypes.ForkTree`: a fork tree, with one `ForkRule` for each round.
   `RoundTypes.ForkTree.AllPaths` says that a check holds on every path of a tree.
5. `ProofSystem`: the rounds, the response and the verifier. `ProofSystem.SpecialSound` is tree
   special soundness with a named extractor.
6. `RoundTypes.Strategy` and `ProofSystem.Complete`: the honest prover and completeness.
   Soundness does not use them.
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

/-- The types of the messages of a public-coin protocol, round by round. In each round, the prover
sends a `Commitment`, and the verifier answers with a random `Challenge`. It has no type for the
response. A Σ-protocol has one round: `.round Commitment Challenge .done`. -/
inductive RoundTypes : Type 1
  /-- No more rounds. -/
  | done
  /-- The prover sends a commitment, the verifier sends a challenge, and `rest` follows. -/
  | round (Commitment Challenge : Type) (rest : RoundTypes)

/-- The messages of one run: the commitments and the challenges in order. It ends with `()`. -/
@[reducible] def RoundTypes.Transcript : RoundTypes → Type
  | .done => Unit
  | .round Commitment Challenge rest => Commitment × Challenge × rest.Transcript

/-- The rules for one round of a fork tree: the number of children, and a rule for the
challenges of each pair of different children. -/
structure ForkRule (Challenge : Type) where
  /-- The number of children of each node in this round, each with its own challenge. -/
  arity : ℕ
  /-- A rule for the challenges of two different children. -/
  Apart : Challenge → Challenge → Prop

/-- The challenges of the `f.arity` children of one node: each pair of different children has
challenges that are `Apart`. -/
abbrev ForkRule.AllowedChallenges {Challenge : Type} (f : ForkRule Challenge) : Type :=
  {c : Fin f.arity → Challenge // ∀ i j, i ≠ j → f.Apart (c i) (c j)}

/-- One `ForkRule` for each round of a protocol, for the challenge type of that round. -/
@[reducible] def RoundTypes.ForkRules : RoundTypes → Type
  | .done => Unit
  | .round _ Challenge rest => ForkRule Challenge × rest.ForkRules

/-- One node of a fork tree, in a round with the rule `f`: a commitment, then one challenge and
one subtree for each of the `f.arity` children. -/
structure ForkNode (Commitment Challenge : Type) (f : ForkRule Challenge) (Child : Type) where
  /-- The commitment of the prover at this node. -/
  commitment : Commitment
  /-- The challenge of each child. They follow the rule `f`. -/
  challenges : f.AllowedChallenges
  /-- The subtree of each child. In the last round, it is a leaf value. -/
  children : Fin f.arity → Child

/-- A fork tree of a protocol: one `ForkNode` in each round, and one value of type `Leaf` at
each leaf. -/
@[reducible] def RoundTypes.ForkTree (p : RoundTypes) (rules : p.ForkRules) (Leaf : Type) :
    Type :=
  match p with
  | .done => Leaf
  | .round Commitment Challenge rest =>
      let (f, restRules) := rules
      ForkNode Commitment Challenge f (rest.ForkTree restRules Leaf)

/-- `check` holds on every path of the tree: on the transcript of the path and its leaf value. -/
def RoundTypes.ForkTree.AllPaths {Leaf : Type} {p : RoundTypes} {rules : p.ForkRules}
    (t : p.ForkTree rules Leaf) (check : p.Transcript → Leaf → Prop) : Prop :=
  match p with
  -- No rounds left: the tree is one leaf value, and the transcript is `()`.
  | .done => check () t
  -- One round: in each child `i`, the check holds with the commitment and `i`'s challenge first.
  | .round _ _ _ =>
      ∀ i, (t.children i).AllPaths fun trRest z =>
        check (t.commitment, t.challenges.val i, trRest) z

/-! ## Proof systems -/

/-- A public-coin protocol for the relation `R`: the rounds, then a response, then a check. -/
structure ProofSystem (R : Relation) where
  /-- The rounds of the protocol. -/
  roundTypes : RoundTypes
  /-- The type of the last message of the prover. -/
  ResponseType : Type
  /-- The verifier: it accepts or rejects a transcript and a response for a statement. -/
  Verify : R.StatementType → roundTypes.Transcript → ResponseType → Prop

/-- A fork tree of a proof system with the fork rules `rules`: a response at each leaf. -/
abbrev ProofSystem.ForkTree {R : Relation} (S : ProofSystem R) (rules : S.roundTypes.ForkRules) :
    Type :=
  S.roundTypes.ForkTree rules S.ResponseType

/-- Tree special soundness with the fork rules `rules`: from every statement `x` and every fork
tree in which `Verify` accepts every path, `extract` computes a witness for `x`. -/
def ProofSystem.SpecialSound {R : Relation} (S : ProofSystem R) (rules : S.roundTypes.ForkRules)
    (extract : R.StatementType → S.ForkTree rules → R.WitnessType) : Prop :=
  ∀ (x : R.StatementType) (t : S.ForkTree rules), t.AllPaths (S.Verify x) →
    R.RelaxedRel x (extract x t)

/-! ## The honest prover

Soundness does not use it. Completeness does. -/

/-- A prover strategy: a commitment, then a strategy for the rest for each challenge. At the end:
a value of type `Last`. -/
@[reducible] def RoundTypes.Strategy (p : RoundTypes) (Last : Type) : Type :=
  match p with
  | .done => Last
  | .round Commitment Challenge rest => Commitment × (Challenge → rest.Strategy Last)

/-- One challenge for each round, as a tuple. -/
@[reducible] def RoundTypes.Challenges : RoundTypes → Type
  | .done => Unit
  | .round _ Challenge rest => Challenge × rest.Challenges

/-- The transcript and the end value of a strategy on the challenges `cs`. -/
def RoundTypes.run {p : RoundTypes} {Last : Type} (s : p.Strategy Last) (cs : p.Challenges) :
    p.Transcript × Last :=
  match p with
  -- No rounds left: the strategy is the end value.
  | .done => ((), s)
  -- One round: send the commitment `a`, read the challenge `c`, then run the rest.
  | .round _ _ _ =>
      let (a, next) := s
      let (c, csRest) := cs
      let (tr, z) := run (next c) csRest
      ((a, c, tr), z)

/-- An honest prover: from the statement, the witness and its random coins, a strategy. -/
structure ProofSystem.HonestProver {R : Relation} (S : ProofSystem R) where
  /-- The type of the random coins of the prover. -/
  CoinsType : Type
  /-- The strategy of the prover. At the end, it sends the response. -/
  prove : R.StatementType → R.WitnessType → CoinsType → S.roundTypes.Strategy S.ResponseType

/-- Completeness: for every witness `w` with `Rel x w`, every choice of coins and every tuple of
challenges, the verifier accepts the transcript and the response of the honest prover. -/
def ProofSystem.Complete {R : Relation} (S : ProofSystem R) (P : S.HonestProver) : Prop :=
  ∀ (x : R.StatementType) (w : R.WitnessType), R.Rel x w →
    ∀ (coins : P.CoinsType) (cs : S.roundTypes.Challenges),
      let (tr, z) := S.roundTypes.run (P.prove x w coins) cs
      S.Verify x tr z

/-! ### Example: a Σ-protocol with 3 challenges

The commitment, the challenge and the response are all in `ℕ`. The functions above compute
these types. -/

namespace SigmaExample

/-- One round. -/
def sigma : RoundTypes := .round ℕ ℕ .done

/-- The messages of one run are `(commitment, challenge, ())`. -/
example : sigma.Transcript = (ℕ × ℕ × Unit) := rfl

/-- One rule: 3 distinct challenges. -/
def sigmaRules : sigma.ForkRules := (⟨3, (· ≠ ·)⟩, ())

/-- A tree is one node: a commitment, 3 distinct challenges, and 3 responses as its children. -/
example : sigma.ForkTree (rules := sigmaRules) (Leaf := ℕ) = ForkNode ℕ ℕ sigmaRules.1 ℕ := rfl

/-- The tree with the commitment 7, the challenges 10, 11, 12 and the responses 100, 101, 102. -/
def tree : sigma.ForkTree sigmaRules ℕ where
  commitment := 7
  challenges := ⟨fun i => 10 + (i : ℕ), by decide⟩
  children i := 100 + (i : ℕ)

/-- On each of its 3 paths, the response is the challenge plus 90. -/
example : tree.AllPaths (fun (_, c, ()) z => z = c + 90) := by
  intro i; fin_cases i <;> rfl

end SigmaExample

/-! ### Example: Schnorr as a proof system

Schnorr proves knowledge of `w` with `X = w • G`. The prover sends `R`, the verifier sends `c`,
and the prover sends `z`. The verifier checks `z • G = R + c • X`. Two accepted paths with the
same `R` and different `c` give `w = (z₀ - z₁) / (c₀ - c₁)`. -/

namespace SchnorrExample

variable (F E : Type) [Field F] [AddCommGroup E] [Module F E]

/-- The discrete logarithm: the statement is `(G, X)`, and the witness is `w` with `w • G = X`.
`Rel` and `RelaxedRel` are the same. -/
@[reducible] def dlog : Relation where
  StatementType := E × E
  WitnessType := F
  Rel := fun (G, X) w => w • G = X
  RelaxedRel := fun (G, X) w => w • G = X

/-- One round: the commitment `R : E` and the challenge `c : F`. -/
def schnorrRounds : RoundTypes := .round E F .done

/-- Schnorr as a proof system. The response is `z : F`. -/
@[reducible] def schnorrSystem : ProofSystem (dlog F E) where
  roundTypes := schnorrRounds F E
  ResponseType := F
  Verify := fun (G, X) (R, c, ()) z => z • G = R + c • X

/-! #### Soundness -/

/-- The fork rule: 2 distinct challenges. -/
def schnorrRules : (schnorrRounds F E).ForkRules := (⟨2, (· ≠ ·)⟩, ())

variable {F E}

/-- The extractor: `w = (z₀ - z₁) / (c₀ - c₁)`. -/
def extract (_ : E × E) (t : (schnorrSystem F E).ForkTree (schnorrRules F E)) : F :=
  (t.children 0 - t.children 1) / (t.challenges.val 0 - t.challenges.val 1)

/-- Schnorr is special sound with 2 challenges. -/
theorem schnorr_sound : (schnorrSystem F E).SpecialSound (schnorrRules F E) extract := by
  rintro ⟨G, X⟩ ⟨R, ⟨c, hc⟩, z⟩ hacc
  -- The tree has 2 paths, and the verifier accepts both.
  have h0 : z 0 • G = R + c 0 • X := hacc (0 : Fin 2)
  have h1 : z 1 • G = R + c 1 • X := hacc (1 : Fin 2)
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
