import Audit.NLAFull.Rust
import Bppp.Spec.NormLinearSoundness

/-!
# Bridge from Jonas's NLA to ours

This file proves Jonas's NLA extraction from our `nla_sound_of_independent`.

Why it exists:
- His circuit proofs use his NLA types (`ℕ → F` vectors with explicit lengths, and `Tree`).
- With this file, those proofs use our `nla_sound_of_independent` in place of his own NLA
  soundness proof.

How it works:
1. `toInst` and `toWit` turn his instance and witness into ours. `ofWit` turns our witness into
   his.
2. `rel_iff`, `independent_of` and `fold_toInst` show that his `Rel`, `Relation` and `foldInst`
   agree with ours.
3. `exists_forkTree` turns his accepting tree into our `ForkTree` with accepted transcripts.
4. `extract` applies `nla_sound_of_independent` to that tree.

Assumptions:
- His tree has `numRounds` rounds, which is the round count of the Rust verifier.
- His instance has `μ = ρ²` and `ρ ≠ 0`.
-/

namespace Audit.NLA.Bridge

open Finset Bppp.Spec

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-- His instance, with the value base `g`, as our instance. -/
def toInst (g : E) (x : NormLinear.Instance F E) (hρ : x.ρ ≠ 0) : Instance F E x.Lℓ x.Ln where
  C := x.C
  g := g
  c i := x.c i
  H i := x.H i
  G i := x.G i
  ρ := x.ρ
  hρ := hρ

/-- His witness as our witness, with the lengths of `x`. -/
def toWit (x : NormLinear.Instance F E) (w : NormLinear.Witness F) : Witness F x.Lℓ x.Ln :=
  ⟨fun i => w.ℓ i, fun i => w.n i⟩

/-- Our witness as his witness, with 0 after the end. -/
def ofWit {m k : ℕ} (w : Witness F m k) : NormLinear.Witness F :=
  ⟨fun i => if h : i < m then w.ℓ ⟨i, h⟩ else 0, fun i => if h : i < k then w.n ⟨i, h⟩ else 0⟩

omit [AddCommGroup E] [Module F E] in
theorem toWit_ofWit (x : NormLinear.Instance F E) (w : Witness F x.Lℓ x.Ln) :
    toWit x (ofWit w) = w := by
  cases w
  simp [toWit, ofWit]

/-- His relation is our relation. -/
theorem rel_iff (g : E) (x : NormLinear.Instance F E) (hρ : x.ρ ≠ 0) (hμ : x.μ = x.ρ ^ 2)
    (w : NormLinear.Witness F) : NormLinear.Rel g x w ↔ Rel (toInst g x hρ) (toWit x w) := by
  simp [NormLinear.Rel, Rel, Instance.point, Instance.opening, toInst, toWit, ip, wip, msm,
    NormLinear.ip, NormLinear.wip, NormLinear.msm, Finset.sum_range, hμ]

/-- If his generators have no relation, our generators are independent. -/
theorem independent_of (g : E) (x : NormLinear.Instance F E) (hρ : x.ρ ≠ 0)
    (hrel : ¬ NormLinear.Relation g x) : (toInst g x hρ).Independent := by
  intro o ho
  by_contra hne
  apply hrel
  refine ⟨o.σ, (ofWit ⟨o.ℓ, o.n⟩).ℓ, (ofWit ⟨o.ℓ, o.n⟩).n, ?_, ?_⟩
  · by_contra hz
    push Not at hz
    obtain ⟨hs, hl, hn⟩ := hz
    apply hne
    ext
    · exact hs
    · rename_i j
      exact (by simpa [ofWit] using hl j j.isLt : o.ℓ j = 0)
    · rename_i j
      exact (by simpa [ofWit] using hn j j.isLt : o.n j = 0)
  · rw [← ho]
    simp [NormLinear.pt, Instance.point, toInst, ofWit, msm, NormLinear.msm, Finset.sum_range]

/-- Our fold of his instance is his fold. -/
theorem fold_toInst (g : E) (x : NormLinear.Instance F E) (hρ : x.ρ ≠ 0) (hμ : x.μ = x.ρ ^ 2)
    (X R : E) (γ : F) :
    foldInst (toInst g x hρ) X R γ =
      toInst g (NormLinear.foldInst x X R γ) (by simpa [NormLinear.foldInst, hμ] using hρ) := by
  simp only [foldInst, toInst, NormLinear.foldInst, hμ]
  congr 1 <;> funext i <;> have hi := i.isLt <;> simp only [half] at hi <;>
    simp [evens, odds, NormLinear.ev, NormLinear.od, NormLinear.pad] <;> intro h <;> omega

/-- His accepting tree with `numRounds` rounds gives our fork tree with accepted transcripts. -/
theorem exists_forkTree (g : E) : ∀ (t : NormLinear.Tree F E) (d : ℕ)
    (x : NormLinear.Instance F E) (hρ : x.ρ ≠ 0), x.μ = x.ρ ^ 2 → t.Depth d →
    d = numRounds x.Lℓ x.Ln → NormLinear.Accepts g x t →
    ∃ ft : ForkTree F E x.Lℓ x.Ln, ∀ p ∈ ft.transcripts, verify (toInst g x hρ) p
  | .leaf w, _, x, hρ, hμ, .leaf _, hd, hacc => by
    have hb : IsBase x.Lℓ x.Ln := by
      by_contra hb
      rw [numRounds] at hd
      simp only [hb, ↓reduceIte] at hd
      omega
    refine ⟨.leaf (toWit x w), ?_⟩
    intro p hp
    simp only [ForkTree.transcripts, List.mem_singleton] at hp
    subst hp
    exact (rel_iff g x hρ hμ w).1 hacc
  | .node X R γ child, _, x, hρ, hμ, .node _ _ _ _ d hd', hd, ⟨hγ, hacc⟩ => by
    have hnb : ¬ IsBase x.Lℓ x.Ln := by
      intro hb
      rw [numRounds] at hd
      simp only [hb, ↓reduceIte] at hd
      omega
    have hd2 : d = numRounds (half x.Lℓ) (half x.Ln) := by
      rw [numRounds] at hd
      simp only [hnb, ↓reduceIte] at hd
      omega
    have hρ' : x.μ ≠ 0 := by rw [hμ]; exact pow_ne_zero 2 hρ
    have hch := fun i => exists_forkTree g (child i) d (NormLinear.foldInst x X R (γ i)) hρ' rfl
      (hd' i) hd2 (hacc i)
    choose ft hft using hch
    refine ⟨.node ⟨X, R, γ, fun i j hij e => hij (hγ e)⟩ ft, ?_⟩
    intro p hp
    simp only [ForkTree.transcripts, List.mem_flatMap, List.mem_finRange, List.mem_map,
      true_and] at hp
    obtain ⟨i, t, ht, rfl⟩ := hp
    simp only [verify]
    rw [fold_toInst g x hρ hμ]
    exact hft i t ht

/-- Jonas's NLA extraction, proved with `nla_sound_of_independent`: with `numRounds` rounds, an
accepting tree gives a witness, or a relation among the generators. -/
theorem extract (g : E) (t : NormLinear.Tree F E) (d : ℕ) (x : NormLinear.Instance F E)
    (hd : t.Depth d) (hr : d = numRounds x.Lℓ x.Ln) (hL : 2 ^ d ∣ x.Ln) (hρ : x.ρ ≠ 0)
    (hμ : x.μ = x.ρ ^ 2) (hacc : NormLinear.Accepts g x t) :
    (∃ w, NormLinear.Rel g x w) ∨ NormLinear.Relation g x := by
  by_cases hrel : NormLinear.Relation g x
  · exact Or.inr hrel
  obtain ⟨ft, hft⟩ := exists_forkTree g t d x hρ hμ hd hr hacc
  have hev : EvenNorms x.Lℓ x.Ln := evenNorms_of_two_pow_dvd (hr ▸ hL)
  obtain ⟨w, hw⟩ := nla_sound_of_independent (toInst g x hρ) ft (independent_of g x hρ hrel) hev hft
  refine Or.inl ⟨ofWit w, ?_⟩
  rw [rel_iff g x hρ hμ, toWit_ofWit]
  exact hw

omit [Field F] [AddCommGroup E] [Module F E] in
/-- Every path of a tree with `d` rounds has `d` messages. -/
theorem length_of_mem_paths : ∀ (t : NormLinear.Tree F E) (d : ℕ), t.Depth d →
    ∀ p ∈ t.paths, p.1.length = d
  | .leaf _, _, .leaf _, p, hp => by
    simp only [NormLinear.Tree.paths, List.mem_singleton] at hp
    subst hp
    rfl
  | .node _ _ _ child, _, .node _ _ _ _ d hd, p, hp => by
    simp only [NormLinear.Tree.paths, List.mem_flatMap, List.mem_finRange, List.mem_map,
      true_and] at hp
    obtain ⟨i, q, hq, rfl⟩ := hp
    simp [length_of_mem_paths (child i) d (hd i) q hq]

omit [Field F] [AddCommGroup E] [Module F E] in
/-- A tree has at least one path. -/
theorem paths_ne_nil : ∀ t : NormLinear.Tree F E, t.paths ≠ []
  | .leaf _ => by simp [NormLinear.Tree.paths]
  | .node _ _ _ child => by
    have := paths_ne_nil (child 0)
    simp only [NormLinear.Tree.paths, ne_eq, List.flatMap_eq_nil_iff, List.mem_finRange,
      List.map_eq_nil_iff, forall_const, not_forall]
    exact ⟨0, this⟩

end Audit.NLA.Bridge
