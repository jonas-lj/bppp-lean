import Audit.NLAFull.Lemmas

/-!
# Audit of the full norm-linear argument (NLA)

This file chains rounds of `roundProtocol` into the full NLA, then proves its completeness and
its tree special soundness.

Why it exists:
- The range proof uses the full NLA, not one round.
- Its soundness statement is the one that the circuit layers above it consume.

How it works:
1. `IsBase m k` is the Rust base case. `numRounds m k` counts the rounds before it.
2. A `Transcript` is one run: the rounds `(X, R, γ)` until the base case, then the final
   witness in the clear. Its type allows no other number of rounds.
3. `verify` folds the instance along the transcript and checks `Rel` at the end.
4. `NLACompleteness`: the honest transcript is accepted for every sequence of challenges.
5. `NLASoundness`: on independent generators, a `ForkTree` of accepted transcripts, with 4 distinct
   challenges per round, gives a witness. `treeExtract` computes it.
- This file only states 4 and 5. `Audit/NLAFull/Proofs.lean` proves them as `nla_complete` and
  `nla_sound`, and `Audit.lean` imports it, so the build checks the proofs.

Assumptions:
- The prover keeps each folded witness. It sends only the last one, so a transcript has one
  witness, at its end.
- Every round needs an even norm length, `EvenNorms`. The Rust parameters satisfy it, for
  example `(8, 16)` and `(8, 64)`.
- The definitions of one round are in `Audit/NLA.lean`.

TODO (comparison): compare with `Tree`, `foldPath` and `extract` in
`Bppp/Spec/NormLinearSoundness.lean`.
-/

namespace Audit.NLA

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

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

/-! ## The protocol -/

variable (F E) in
/-- One run of the NLA: rounds `(X, R, γ)` until the base case, then the final witness in the
clear. In Rust terms: `enum Transcript { Done(Witness), Round(X, R, γ, Box<Transcript>) }`.
The type also tracks the lengths `(m, k)`, which halve in each round. -/
inductive Transcript : ℕ → ℕ → Type
  /-- At the base case, the prover sends the final witness. -/
  | done {m k : ℕ} (w : Witness F m k) (hBase : IsBase m k := by assumption) : Transcript m k
  /-- Before the base case, one round: the prover sends `X` and `R`, and the verifier sends
  `γ`. -/
  | round {m k : ℕ} (X R : E) (γ : F) (rest : Transcript (half m) (half k))
      (hNotBase : ¬ IsBase m k := by assumption) : Transcript m k

/-- The NLA verifier: fold `x` along the transcript, then check `Rel` on the final witness. -/
def verify {m k : ℕ} : Instance F E m k → Transcript F E m k → Prop
  | x, .done w _ => Rel x w
  | x, .round X R γ rest _ => verify (foldInst x X R γ) rest

/-! ## Completeness -/

/-- The honest run. Round `i` uses the challenge `γs i`. -/
def honestTranscript {m k : ℕ} (x : Instance F E m k) (w : Witness F m k) (γs : ℕ → F) :
    Transcript F E m k :=
  if hBase : IsBase m k then
    .done w
  else
    let X := msgX x w
    let R := msgR x w
    let γ := γs 0
    let rest := honestTranscript (foldInst x X R γ) (foldWit x γ w) (fun i => γs (i + 1))
    .round X R γ rest
-- Lean must see that the recursion stops: `m + k` gets smaller in each round.
termination_by m + k
decreasing_by simp only [IsBase, half] at *; omega

variable (F E) in
/-- Completeness: the honest prover always convinces the verifier, for every sequence of
challenges. `nla_complete` in `Audit/NLAFull/Proofs.lean` proves it. -/
def NLACompleteness : Prop :=
  ∀ {m k : ℕ} (x : Instance F E m k) (w : Witness F m k), Rel x w →
    ∀ γs : ℕ → F, verify x (honestTranscript x w γs)

/-! ## Soundness -/

variable (F E) in
/-- A tree of forks: each round forks into 4 challenges, as in a `Fork`. In Rust terms:
`enum ForkTree { Leaf(Witness), Node(ForkHead, [Box<ForkTree>; 4]) }`. The type also
tracks the lengths `(m, k)`, which halve in each round. -/
inductive ForkTree : ℕ → ℕ → Type
  /-- At the base case, the final witness of one branch. -/
  | leaf {m k : ℕ} (w : Witness F m k) (hBase : IsBase m k := by assumption) : ForkTree m k
  /-- Before the base case, one round: a fork head, and one subtree for each challenge. -/
  | node {m k : ℕ} (head : ForkHead F E) (child : Fin 4 → ForkTree (half m) (half k))
      (hNotBase : ¬ IsBase m k := by assumption) : ForkTree m k

/-- The transcripts of the tree: one for each branch from the root to a leaf. -/
def ForkTree.transcripts {m k : ℕ} : ForkTree F E m k → List (Transcript F E m k)
  | .leaf w _ => [.done w]
  | .node head child _ =>
      (List.finRange 4).flatMap fun i =>
        (child i).transcripts.map fun t => .round head.X head.R (head.γ i) t

/-- The extractor: `extractWit` at each round, from the leaves up. -/
def treeExtract {m k : ℕ} : Instance F E m k → ForkTree F E m k → Witness F m k
  | _, .leaf w _ => w
  | x, .node head child _ =>
      extractWit x head.γ fun i => treeExtract (foldInst x head.X head.R (head.γ i)) (child i)

variable (F E) in
/-- Soundness: if the generators of `x` are independent, then `treeExtract` computes a witness
from a `ForkTree` of accepted transcripts. Every round needs an even norm length. `nla_sound`
in `Audit/NLAFull/Proofs.lean` proves it.

Note for reviewers: Lean does not check that `treeExtract` is efficient. It calls `extractWit`
once per node. See the note at `RoundSoundness`. -/
def NLASoundness : Prop :=
  ∀ {m k : ℕ} (x : Instance F E m k) (t : ForkTree F E m k), x.Independent →
    EvenNorms m k → (∀ p ∈ t.transcripts, verify x p) → Rel x (treeExtract x t)

end Audit.NLA
