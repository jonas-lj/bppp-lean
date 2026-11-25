import Audit.NLAFull.Full
import Audit.NLAFull.Lemmas

/-!
# The old NLA types

This file keeps the first NLA formalization: its own transcript type, its fork tree and its
extractors. You do not need to review it.

Why it exists:
- The old range route (`Audit/RangeProof/NestedTree.lean`, `Audit/RangeProof/Proofs.lean`,
  `Audit/RangeProof/Paper/`) and `Audit/NLAFull/Bridge.lean` still use these types.
- `Audit/NLAFull/Full.lean` now states the NLA with the reductions of `Audit/Reductions/Defs.lean`.
  When the new range proof replaces the old route, this file goes away.

How it works:
1. A `Transcript` is one run, and `verify` folds the instance along it.
2. `TranscriptCompleteness`: the honest transcript is accepted.
3. A `ForkTree` forks into 4 challenges in each round. `ForkTreeSoundness`: from a tree of
   accepted transcripts, `treeExtractWitness` gives a witness, or `treeExtractGeneratorLink`
   gives a link. `Audit/NLAFull/LegacyProofs.lean` proves both statements.
-/

namespace Audit.NLA

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

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
def TranscriptCompleteness : Prop :=
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

/-- The extractor: `extractWitness` at each round, from the leaves up. -/
def treeExtractWitness {m k : ℕ} : Instance F E m k → ForkTree F E m k → Witness F m k
  | _, .leaf w _ => w
  | x, .node head child _ =>
      extractWitness x head.γ fun i =>
        treeExtractWitness (foldInst x head.X head.R (head.γ i)) (child i)

/-- The candidate link: the first nonzero link of a child, lifted by `liftLink`. If all are 0,
then `extractGeneratorLink` at this node. -/
def treeExtractGeneratorLink [DecidableEq F] {m k : ℕ} :
    Instance F E m k → ForkTree F E m k → Opening F m k
  | _, .leaf _ _ => 0
  | x, .node head child _ =>
      let xᵢ := fun i => foldInst x head.X head.R (head.γ i)
      let l := fun i => liftLink x.ρ (head.γ i) (treeExtractGeneratorLink (xᵢ i) (child i))
      match (List.finRange 4).find? (fun i => l i ≠ 0) with
      | some i => l i
      | none => extractGeneratorLink x head.γ fun i => treeExtractWitness (xᵢ i) (child i)

variable (F E) in
/-- Soundness: from a `ForkTree` of accepted transcripts, `treeExtractWitness` gives a witness,
or `treeExtractGeneratorLink` gives a link. Every round needs an even norm length. `nla_sound`
proves it. -/
def ForkTreeSoundness [DecidableEq F] : Prop :=
  ∀ {m k : ℕ} (x : Instance F E m k) (t : ForkTree F E m k),
    EvenNorms m k → (∀ p ∈ t.transcripts, verify x p) →
    Rel x (treeExtractWitness x t) ∨ x.IsGeneratorLink (treeExtractGeneratorLink x t)

end Audit.NLA
