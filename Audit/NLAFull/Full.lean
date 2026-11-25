import Audit.NLA.Round
import Audit.Reductions.Defs

/-!
# The full norm-linear argument (NLA)

This file states the full NLA as a chain of reductions, then states its soundness and its
completeness.

Why it exists:
- The range proof uses the full NLA, not one round.
- Its soundness statement is the one that the circuit layers above it consume.

How it works:
1. `IsBase m k` is the Rust base case. `numRounds m k` counts the rounds before it.
2. `nlaRelation m k`: the statement is an `Instance` with the lengths `(m, k)`. A relaxed
   witness is a witness of `Rel`, or a link between the generators (`Sum`). The honest prover
   always has a witness.
3. `roundReduction m k`: one round. The prover sends `(X, R)`, the verifier sends `γ`, and the
   new statement is `foldInst x X R γ`, with the lengths `(half m, half k)`.
4. `baseSystem m k`: at the base case, the prover sends the witness in the clear, and the
   verifier checks `Rel`.
5. `nlaSystem n m k`: `n` rounds, then the base case. `fullSystem m k` runs `numRounds m k`
   rounds, as Rust does. `fullForkRules m k` are its fork rules.
6. `NLASoundness extract`: with 4 distinct challenges in each round, `extract` computes a
   relaxed witness from every fork tree in which every path accepts. `NLATreesExist`: such
   trees exist when the field has 4 distinct elements.
7. `NLACompleteness`: the honest prover (`honestStrategy`) always convinces the verifier.
- The spec `Audit/02-RangeProof.lean` does not use this file. Only the proof of `range_sound`
  uses it. You do not need to review it.
- This file only states 6 and 7. `Audit/NLAFull/Proofs.lean` proves them, with the extractor
  `nlaExtract` of `Audit/NLAFull/Extract.lean`.

Assumptions:
- Every round needs an even norm length, `EvenNorms`. The Rust parameters satisfy it, for
  example `(8, 16)` and `(8, 64)`.
- The definitions of one round are in `Audit/NLA/Round.lean`.
- In a real group, links always exist. So "a link exists" has no content. The type
  `NLAExtractor` makes the extractor work for every `F` and `E`, but it does not block choice.
  So `NLASoundness` is meaningful only for a computable extractor without choice, such as
  `nlaExtract`. Such an extractor cannot find a link by itself. A link that it outputs comes
  from the prover, and it breaks the discrete-log relation assumption.
- Lean does not check that the extractor is fast. `nlaExtract` uses the round extractors of
  `Audit/NLA/Round.lean` and `liftLink` (`Audit/NLAFull/Lemmas.lean`), so its time is polynomial in
  the size of the tree.
- Rust does not reject `ρ = 0`. `Instance.hρ` assumes `ρ ≠ 0`, so the caller must cover that
  case.
-/

namespace Audit.NLA

open Audit.TreeSoundness

section Defs

variable (F E : Type) [Field F] [AddCommGroup E] [Module F E]

/-! ## The base case -/

/-- The NLA stops folding here. Rust stops when `ℓ` has length ≤ 1 and `ℓ + n < 6`
(`is_base_case`, `FOLD_THRESHOLD = 6`). -/
def IsBase (m k : ℕ) : Prop := m ≤ 1 ∧ m + k < 6

instance (m k : ℕ) : Decidable (IsBase m k) := inferInstanceAs (Decidable (_ ∧ _))

/-- The number of rounds before the base case. -/
def numRounds (m k : ℕ) : ℕ :=
  if IsBase m k then 0 else 1 + numRounds (half m) (half k)
termination_by m + k
decreasing_by simp only [IsBase, half] at *; omega

/-! Tests: the Rust traces `(8, 16) → (4, 8) → (2, 4) → (1, 2)` and `… → (1, 8) → (1, 4)`. -/
example : numRounds 8 16 = 3 := by simp [numRounds, IsBase, half]
example : numRounds 8 32 = 3 := by simp [numRounds, IsBase, half]
example : numRounds 8 64 = 4 := by simp [numRounds, IsBase, half]
example : numRounds 8 128 = 5 := by simp [numRounds, IsBase, half]

/-- The norm length is even in every round. `round_sound` needs this in each round, and
`round_not_sound_odd` shows that it is necessary. -/
def EvenNorms (m k : ℕ) : Prop :=
  if IsBase m k then True else k % 2 = 0 ∧ EvenNorms (half m) (half k)
termination_by m + k
decreasing_by simp only [IsBase, half] at *; omega

/-! Tests: `(8, 16)` folds the norm lengths 16, 8 and 4. `(8, 1)` folds the norm length 1. -/
example : EvenNorms 8 16 := by simp [EvenNorms, IsBase, half]
example : EvenNorms 8 64 := by simp [EvenNorms, IsBase, half]
example : ¬ EvenNorms 8 1 := by simp [EvenNorms, IsBase, half]

/-! ## The relation -/

/-- The NLA relation for the lengths `(m, k)`. A relaxed witness is a witness of `Rel`, or a link
between the generators. The honest relation `Rel` rejects a link. -/
@[reducible] def nlaRelation (m k : ℕ) : Relation where
  StatementType := Instance F E m k
  WitnessType := Witness F m k ⊕ Opening F m k
  Rel x
    | .inl w => Rel x w
    | .inr _ => False
  RelaxedRel x
    | .inl w => Rel x w
    | .inr o => x.IsGeneratorLink o

/-! ## One round, and the base case -/

/-- One round as a reduction: the prover sends `(X, R)`, and the verifier sends `γ`. The new
statement is the fold. -/
@[reducible] def roundReduction (m k : ℕ) :
    Reduction (nlaRelation F E m k) (nlaRelation F E (half m) (half k)) where
  roundTypes := .round (E × E) F .done
  reduce x := fun ((X, R), γ, ()) => foldInst x X R γ

/-- The base case: the prover sends the witness in the clear, and the verifier checks `Rel`. -/
@[reducible] def baseSystem (m k : ℕ) : ProofSystem (nlaRelation F E m k) where
  roundTypes := .done
  ResponseType := Witness F m k
  Verify x _ w := Rel x w

/-! ## The full NLA -/

/-- `n` rounds, then the base case. Each round halves the lengths. -/
@[reducible] def nlaSystem : (n m k : ℕ) → ProofSystem (nlaRelation F E m k)
  | 0, m, k => baseSystem F E m k
  | n + 1, m, k => (roundReduction F E m k).comp (nlaSystem n (half m) (half k))

/-- The fork rules: 4 distinct challenges `γ` in each round. -/
def nlaForkRules : (n m k : ℕ) → (nlaSystem F E n m k).roundTypes.ForkRules
  | 0, _, _ => ()
  | n + 1, _, _ => (⟨4, (· ≠ ·)⟩, nlaForkRules n _ _)

/-- The full NLA, as Rust runs it: `numRounds m k` rounds, then the base case. -/
abbrev fullSystem (m k : ℕ) : ProofSystem (nlaRelation F E m k) :=
  nlaSystem F E (numRounds m k) m k

/-- The fork rules of `fullSystem`. -/
abbrev fullForkRules (m k : ℕ) : (fullSystem F E m k).roundTypes.ForkRules :=
  nlaForkRules F E (numRounds m k) m k

/-! ## Completeness -/

variable {F E} in
/-- The honest strategy: in each round, send `msgX` and `msgR`, then continue with the folded
instance and witness. At the end, send the witness. -/
def honestStrategy : (n : ℕ) → {m k : ℕ} → Instance F E m k → Witness F m k →
    (nlaSystem F E n m k).roundTypes.Strategy (nlaSystem F E n m k).ResponseType
  | 0, _, _, _, w => w
  | n + 1, _, _, x, w =>
      ((msgX x w, msgR x w), fun γ => honestStrategy n (foldInst x (msgX x w) (msgR x w) γ)
        (foldWit x γ w))

/-- The honest prover. It has no coins. The prover never sends a link, because `baseSystem`
sends only a `Witness`. With a link in place of a witness, it sends 0s. This case never occurs,
because `Rel` rejects a link. -/
def honest (n m k : ℕ) : (nlaSystem F E n m k).HonestProver where
  CoinsType := Unit
  prove x w _ := honestStrategy n x (w.elim id fun _ => ⟨0, 0⟩)

/-- Completeness: the honest prover always convinces the verifier. -/
def NLACompleteness : Prop :=
  ∀ m k, (fullSystem F E m k).Complete (honest F E (numRounds m k) m k)

/-- Fork trees exist: with 4 distinct field elements, every NLA system has a fork tree. With
completeness, accepted fork trees exist too. -/
def NLATreesExist : Prop :=
  ∀ γ : Fin 4 → F, Function.Injective γ → ∀ n m k,
    Nonempty ((nlaSystem F E n m k).ForkTree (nlaForkRules F E n m k))

end Defs

/-! ## Soundness -/

/-- An NLA extractor: from an instance and a fork tree of `fullSystem`, a relaxed witness. It must
work for every field `F` with decidable equality and every group `E`. The type does not block
choice, so a reviewer must check that the extractor is computable and has no choice. -/
abbrev NLAExtractor : Type 1 :=
  ∀ {F E : Type} [Field F] [AddCommGroup E] [Module F E] [DecidableEq F] {m k : ℕ},
    Instance F E m k → (fullSystem F E m k).ForkTree (fullForkRules F E m k) →
    Witness F m k ⊕ Opening F m k

/-- Soundness: for all lengths `(m, k)` with an even norm length in every round, the NLA is
special sound with 4 challenges in each round. From every fork tree in which every path
accepts, `extract` gives a witness or a link. `nla_sound` proves it for `nlaExtract`. -/
def NLASoundness (extract : NLAExtractor) : Prop :=
  ∀ (F E : Type) [Field F] [AddCommGroup E] [Module F E] [DecidableEq F] (m k : ℕ),
    EvenNorms m k →
    (fullSystem F E m k).SpecialSound (fullForkRules F E m k) extract

end Audit.NLA
