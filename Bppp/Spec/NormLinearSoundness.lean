import Bppp.Spec.NormLinearCompleteness

/-!
# Trees of transcripts of the norm-linear argument

This file defines the tree of transcripts (`Tree`) and the relation among generators
(`Relation`) that the circuit proofs use.

The extraction from such a tree is `Audit.NLA.Bridge.extract`. It uses `Audit.NLA.nla_sound`.
-/

open Finset

namespace Bppp.Spec.NormLinear

variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
variable (g : E)

/-- The point `s g + <h, H> + <n, G>` over the generators of `x`. -/
def pt (x : Instance F E) (s : F) (h n : ℕ → F) : E := s • g + msm x.Lℓ h x.H + msm x.Ln n x.G

/-- A nontrivial linear relation among the generators `g`, `H_0, ...` and `G_0, ...` of `x`. -/
def Relation (x : Instance F E) : Prop :=
  ∃ (s : F) (h n : ℕ → F), (s ≠ 0 ∨ (∃ j < x.Lℓ, h j ≠ 0) ∨ (∃ j < x.Ln, n j ≠ 0)) ∧
    pt g x s h n = 0

variable (F E) in
/-- A tree of transcripts of the interactive norm-linear argument: in each round the prover's
messages `X`, `R` and, for four challenges, the rest of the transcript; at the end the opening
sent in the clear. -/
inductive Tree
  | leaf (w : Witness F)
  | node (X R : E) (γ : Fin 4 → F) (child : Fin 4 → Tree)

/-- The tree has `d` rounds along every branch. -/
inductive Tree.Depth : Tree F E → ℕ → Prop
  | leaf (w : Witness F) : Depth (.leaf w) 0
  | node (X R : E) (γ : Fin 4 → F) (child : Fin 4 → Tree F E) (d : ℕ)
      (h : ∀ k, Depth (child k) d) : Depth (.node X R γ child) (d + 1)

/-- Every transcript of the tree is accepted, and the challenges of each round are distinct. -/
def Accepts : Instance F E → Tree F E → Prop
  | x, .leaf w => Rel g x w
  | x, .node X R γ child => Function.Injective γ ∧ ∀ k, Accepts (foldInst x X R (γ k)) (child k)

/-- The instance after folding with the messages `rounds` and the challenges `γs`. -/
def foldPath : Instance F E → List (E × E) → List F → Instance F E
  | x, (X, R) :: rounds, γ :: γs => foldPath (foldInst x X R γ) rounds γs
  | x, _, _ => x

/-- The transcripts of the tree: for each path, its messages, challenges and final opening. -/
def Tree.paths : Tree F E → List (List (E × E) × List F × Witness F)
  | .leaf w => [([], [], w)]
  | .node X R γ child => (List.finRange 4).flatMap fun k =>
      (child k).paths.map fun p => ((X, R) :: p.1, γ k :: p.2.1, p.2.2)

/-- The challenges of each round of the tree are distinct. -/
def Tree.Distinct : Tree F E → Prop
  | .leaf _ => True
  | .node _ _ γ child => Function.Injective γ ∧ ∀ k, (child k).Distinct

/-- A tree accepts when its challenges are distinct and each of its transcripts accepts. -/
lemma accepts_of_paths : ∀ (t : Tree F E) (x : Instance F E), t.Distinct →
    (∀ p ∈ t.paths, Rel g (foldPath x p.1 p.2.1) p.2.2) → Accepts g x t
  | .leaf w, x, _, h => h ([], [], w) (by simp [Tree.paths])
  | .node X R γ child, x, ⟨hγ, hd⟩, h => ⟨hγ, fun k => accepts_of_paths (child k) _ (hd k)
      fun p hp => h ((X, R) :: p.1, γ k :: p.2.1, p.2.2)
        (by simp only [Tree.paths, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
            exact ⟨k, p, hp, rfl⟩)⟩

end Bppp.Spec.NormLinear
