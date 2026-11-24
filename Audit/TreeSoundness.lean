import Mathlib

/-!
# Tree special soundness

This file defines public-coin protocols and their tree special soundness. It does not mention a
specific protocol.

Why it exists:
- A soundness statement must say what "sound" means. This file gives the textbook meaning, so
  that a reader can check it once.
- `Audit/RangeProof.lean` uses it for the Bulletproofs++ range proof.

How it works:
1. `RoundTypes` lists the rounds of a protocol, with the types of their messages. In each
   round, the prover sends a commitment, and the verifier answers with a random challenge. At
   the end, the prover sends a response. The challenge type of a round is the set from which the
   verifier samples. It excludes the challenges for which the verifier cannot compute.
2. A `RoundTypes.Transcript` is one run: the commitments and the challenges in order, then the
   response.
3. A `RoundTypes.Tree` is a fork tree. In each round, a node has one commitment and several
   children, each with its own challenge. So all transcripts below a node share the commitments
   above it. A `ForkRule` gives the number of children in each round, and a rule for the
   challenges of two different children.
4. A `ProofSystem` is a relation `Rel` between statements and witnesses, the round types of the
   protocol, and a verifier `Verify`. Sizes are fixed outside, so there is one system for each
   size.
5. `ProofSystem.SpecialSound`: from every statement `x` and every fork tree in which the verifier
   accepts every transcript, the extractor computes a witness `w` with `RelaxedRel x w`.
6. The honest prover (`ProofSystem.HonestProver`) gives a strategy (`RoundTypes.Strategy`):
   a commitment, then a strategy for the rest for each challenge. `ProofSystem.Complete`: for a
   witness `w` with `Rel x w`, the verifier accepts each transcript of the honest prover.
   Soundness does not use the prover.

The examples at the end show the types for a Σ-protocol, and Schnorr with its extractor and its
honest prover.

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
- The extractor is a named function, not an `∃`. A statement that uses this definition must say
  which extractor it names.
-/

namespace Audit.TreeSoundness

/-- The types of the messages of a public-coin protocol, round by round. In each round, the
prover sends a commitment of type
`Commitment`, and the verifier answers with a random challenge of type `Challenge`. At the end,
the prover sends a response of type `Response`. A Σ-protocol is
`.round Commitment Challenge (.done Response)`. -/
inductive RoundTypes : Type 1
  /-- The prover sends the response, and the protocol ends. -/
  | done (Response : Type)
  /-- The prover sends a commitment, the verifier sends a challenge, and `rest` follows. -/
  | round (Commitment Challenge : Type) (rest : RoundTypes)

/-- One run: the commitments and the challenges in order, then the response. -/
@[reducible] def RoundTypes.Transcript : RoundTypes → Type
  | .done Response => Response
  | .round Commitment Challenge rest => Commitment × Challenge × rest.Transcript

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
  | .done _ => Unit
  | .round _ Challenge rest => ForkRule Challenge × rest.ForkRules

/-- A fork tree of a protocol. In each round: one commitment, then the challenges of the
`arity` children (they follow the rule), then the subtrees of the children. At the end: one
response. -/
@[reducible] def RoundTypes.Tree : (p : RoundTypes) → p.ForkRules → Type
  | .done Response, _ => Response
  | .round Commitment Challenge rest, (f, fs) =>
      Commitment × {c : Fin f.arity → Challenge // f.Allowed c} × (Fin f.arity → rest.Tree fs)

/-- The transcripts of a tree: one for each path from the root to a leaf. -/
def RoundTypes.Tree.transcripts : {p : RoundTypes} → {fs : p.ForkRules} → p.Tree fs →
    List p.Transcript
  | .done _, _, z => [z]
  | .round _ _ _, _, (a, ⟨c, _⟩, sub) =>
      -- For each child `i`: put `a` and its challenge `c i` in front of each transcript of its
      -- subtree `sub i`. Then join the lists of all children.
      (List.finRange _).flatMap fun i => (transcripts (sub i)).map fun tr => (a, c i, tr)

/-- A relation, and a public-coin protocol for it. Sizes, such as the length of a vector, are
fixed outside: there is one proof system for each size. -/
structure ProofSystem where
  /-- The public input. -/
  StatementType : Type
  /-- The secret input of the prover. -/
  WitnessType : Type
  /-- The relation of the honest prover: `w` is a witness for `x`. Completeness uses it. -/
  Rel : StatementType → WitnessType → Prop
  /-- The relation that the extractor must meet. It is `Rel`, or a break of a hardness
  assumption, for example a link between generators. Soundness uses it. -/
  RelaxedRel : StatementType → WitnessType → Prop
  /-- The rounds of the protocol. -/
  roundTypes : RoundTypes
  /-- The verifier: it accepts or rejects one transcript for the statement `x`. -/
  Verify : StatementType → roundTypes.Transcript → Prop

/-- Tree special soundness with the fork rules `fs`: from every statement `x` and every fork tree
in which `Verify` accepts every transcript, `extract` computes a witness for `x`. -/
def ProofSystem.SpecialSound (S : ProofSystem) (fs : S.roundTypes.ForkRules)
    (extract : S.StatementType → S.roundTypes.Tree fs → S.WitnessType) : Prop :=
  ∀ x t, (∀ tr ∈ t.transcripts, S.Verify x tr) → S.RelaxedRel x (extract x t)

/-! ## The honest prover

Soundness does not use it. Completeness does. -/

/-- A prover strategy: a commitment, then a strategy for the rest for each challenge. At the end:
the response. -/
@[reducible] def RoundTypes.Strategy : RoundTypes → Type
  | .done Response => Response
  | .round Commitment Challenge rest => Commitment × (Challenge → rest.Strategy)

/-- One challenge for each round, as a tuple. -/
@[reducible] def RoundTypes.Challenges : RoundTypes → Type
  | .done _ => Unit
  | .round _ Challenge rest => Challenge × rest.Challenges

/-- The transcript of a strategy on the challenges `cs`. -/
def RoundTypes.run : {p : RoundTypes} → p.Strategy → p.Challenges → p.Transcript
  | .done _, z, _ => z
  | .round _ _ _, (a, next), (c, cs) => (a, c, run (next c) cs)

/-- An honest prover: from the statement, the witness and its random coins, a strategy. -/
structure ProofSystem.HonestProver (S : ProofSystem) where
  /-- The type of the random coins of the prover. -/
  CoinsType : Type
  /-- The strategy of the prover. -/
  prove : S.StatementType → S.WitnessType → CoinsType → S.roundTypes.Strategy

/-- Completeness: for every witness `w` with `Rel x w`, every choice of coins and every tuple of
challenges, the verifier accepts the transcript of the honest prover. -/
def ProofSystem.Complete (S : ProofSystem) (P : S.HonestProver) : Prop :=
  ∀ x w, S.Rel x w → ∀ coins cs, S.Verify x (S.roundTypes.run (P.prove x w coins) cs)

/-! ### Example: a Σ-protocol with 3 challenges

The commitment, the challenge and the response are all in `ℕ`. The functions above compute
these types. -/

namespace SigmaExample

/-- One round, then the response. -/
def sigma : RoundTypes := .round ℕ ℕ (.done ℕ)

/-- One run is `(commitment, challenge, response)`. -/
example : sigma.Transcript = (ℕ × ℕ × ℕ) := rfl

/-- One rule: 3 distinct challenges. -/
def rules : sigma.ForkRules := (⟨3, (· ≠ ·)⟩, ())

/-- A tree is one commitment, then the 3 distinct challenges, then the 3 responses. -/
example : sigma.Tree rules =
    (ℕ × {c : Fin 3 → ℕ // rules.1.Allowed c} × (Fin 3 → ℕ)) := rfl

/-- The tree with the commitment 7, the challenges 10, 11, 12 and the responses 100, 101, 102. -/
def tree : sigma.Tree rules :=
  (7, ⟨fun i => 10 + (i : ℕ), by unfold ForkRule.Allowed; decide⟩, fun i => 100 + (i : ℕ))

/-- It has 3 transcripts, which share the commitment 7. -/
example : tree.transcripts = [(7, 10, 100), (7, 11, 101), (7, 12, 102)] := rfl

end SigmaExample

/-! ### Example: Schnorr as a proof system

Schnorr proves knowledge of `w` with `X = w • G`. The prover sends `R`, the verifier sends `c`,
and the prover sends `z`. The verifier checks `z • G = R + c • X`. Two accepted transcripts with
the same `R` and different `c` give `w = (z₀ - z₁) / (c₀ - c₁)`. Both relations are the same. -/

namespace SchnorrExample

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

variable (F E) in
/-- One round: the commitment `R : E` and the challenge `c : F`. Then the response `z : F`. -/
def schnorr : RoundTypes := .round E F (.done F)

variable (F E) in
/-- Schnorr as a proof system. The statement is `(G, X)`, and the witness is `w`. -/
@[reducible] def schnorrSystem : ProofSystem where
  StatementType := E × E
  WitnessType := F
  Rel := fun (G, X) w => X = w • G
  RelaxedRel := fun (G, X) w => X = w • G
  roundTypes := schnorr F E
  Verify := fun (G, X) (R, c, z) => z • G = R + c • X

/-! #### Soundness -/

variable (F E) in
/-- The fork rule: 2 distinct challenges. -/
def rules : (schnorr F E).ForkRules := (⟨2, (· ≠ ·)⟩, ())

/-- The extractor: `w = (z₀ - z₁) / (c₀ - c₁)`. -/
def extract (_ : E × E) (t : (schnorr F E).Tree (rules F E)) : F :=
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
  show X = ((z 0 - z 1) / (c 0 - c 1)) • G
  rw [div_eq_inv_mul, mul_smul, key, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-! #### Completeness -/

/-- The honest prover: with the coin `r`, send `R = r • G`. Then answer `c` with `z = r + c w`. -/
@[reducible] def honest : (schnorrSystem F E).HonestProver where
  CoinsType := F
  prove := fun (G, _) w r => (r • G, fun c => r + c * w)

/-- Schnorr is complete: `(r + c w) • G = r • G + c • X` when `X = w • G`. -/
theorem schnorr_complete : (schnorrSystem F E).Complete honest := by
  rintro ⟨G, X⟩ w (hX : X = w • G) r ⟨c, ⟨⟩⟩
  show (r + c * w) • G = r • G + c • X
  rw [hX, add_smul, mul_smul]

end SchnorrExample

end Audit.TreeSoundness
