import Audit.NLAFull.Legacy
import Bppp.Model.Crs
import Bppp.Spec.CircuitSoundness

/-!
# The range extractors: design and shared parts

This file gives the design of the extractor for `RangeSoundness` (`Audit/02-RangeProof.lean`). It
also holds the parts that all levels use.

Why it exists:
- `RangeSoundness ext` is a statement about a named extractor `ext`. The proof must give one.
- The extractor must be generic in `F` and `E`, and computable. So it cannot use
  `Classical.choose`, and it cannot search the group for a link. The review checklist is the
  same as for the NLA extractors (`Audit/NLAFull/Full.lean`).

Terms:
- An opening of a point `P` is a tuple `(s, h, n)` of scalars with
  `s • g + Σ_j h_j • H_j + Σ_j n_j • G_j = P`. Here `g = gens.g`, `H = gens.h_vec`
  (`H_LEN = 8` points) and `G = gens.g_vec` (`nm` points).
- A link is an opening of the zero point. Its type is `NLA.Opening F H_LEN nm`. A nonzero link
  solves discrete log for the generators.
- A candidate is a link that the extractor computes from the tree. It always opens zero. If it
  is not 0, it is the output link.

How it works:
1. Leaves: at each `τ`, `treeExtractWitness` gives an NLA witness, and
   `treeExtractGeneratorLink` gives a candidate.
2. Levels: the fork tree has 5 levels, from the root down: `α`, `ρ`, `β`, `λ` and `τ`. The
   extractor goes up from the `τ` level. At each node, it computes an opening of the node's
   commitments from the openings of its children, by interpolation in the node's challenge.
3. Candidates at a node: each candidate is the difference of two openings of one point.
   - At a `τ` node: the opening of `τ • Y(τ)` at each of the 13 `τ`, minus the value at that `τ`
     of the curve through the first 5.
   - At the other levels: for each commitment, its opening on branch `i`, minus its opening on
     branch 0.
4. The link of the tree is the first nonzero candidate in this order: (a) the NLA candidates
   at the leaves, (b) the `τ` candidates, (c) the candidates of the other levels, from the
   bottom up. If all candidates are 0, the link is 0.
5. Values and blindings: they come from the opening at the root. Each value is
   `Σ_t 16^t d_t`, with the digits `d_t` read from the opening.

Invariant of each level: the candidate opens zero. If the candidate is 0, then the opening of
the level satisfies the conclusion of Jonas's lemma for that level. At the root, this gives
`OpensInRange ∨ IsGeneratorLink`.

Assumptions:
- The levels follow Jonas's lemmas `extract_tau`, `extract_lam`, `extract_beta`, `extract_rho`
  and `extract_alpha` (`Bppp/Spec`). His lemmas choose the opening with `∃`. Our levels name
  the opening and reuse his algebra.
- Interpolation uses `vinv`: the inverse of a Vandermonde matrix through its adjugate.
  `Matrix.inv` is noncomputable, so the extractor cannot use it.
- Each level lemma takes the leaf scalars as an argument `y`, with a hypothesis that `y` is
  equal to Jonas's (noncomputable) expression. So the extractor can compute `y` from the Rust
  model, and a bridge lemma gives the hypothesis.
- Digits: the extractor finds `d < 16` with `(d : F) = x` by a search over 16 values. This uses
  `DecidableEq F`. It does not search over `F`.
-/

namespace Audit.RangeProof

open Finset Bppp

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-! ## Links -/

/-- An opening with coordinates on `ℕ`, cut to the lengths `H_LEN` and `nm`. -/
def toLink (nm : ℕ) (s : F) (h n : ℕ → F) : NLA.Opening F H_LEN nm :=
  ⟨s, fun i => h i, fun j => n j⟩

/-- The point of an NLA opening of lengths `(H_LEN, nm)`, with generators indexed by `ℕ`. -/
def linkPoint {nm : ℕ} (g : E) (H G : ℕ → E) (o : NLA.Opening F H_LEN nm) : E :=
  o.σ • g + NLA.msm o.ℓ (fun i => H i) + NLA.msm o.n (fun j => G j)

theorem linkPoint_toLink (P : Spec.Params) (g : E) (H G : ℕ → E) (s : F) (h n : ℕ → F) :
    linkPoint g H G (toLink P.nm s h n) = Spec.commit P g H G s h n := by
  simp only [linkPoint, toLink, NLA.msm, Spec.commit, Spec.NormLinear.msm, H_LEN]
  rw [← Fin.sum_univ_eq_sum_range (fun i => h i • H i) 8,
    ← Fin.sum_univ_eq_sum_range (fun j => n j • G j) P.nm]
  rfl

theorem toLink_eq_zero {nm : ℕ} {s : F} {h n : ℕ → F} :
    toLink nm s h n = 0 ↔ s = 0 ∧ (∀ j < 8, h j = 0) ∧ ∀ j < nm, n j = 0 := by
  constructor
  · intro e
    have e1 := congrArg NLA.Opening.σ e
    have e2 := congrArg NLA.Opening.ℓ e
    have e3 := congrArg NLA.Opening.n e
    refine ⟨e1, fun j hj => congrFun e2 ⟨j, hj⟩, fun j hj => congrFun e3 ⟨j, hj⟩⟩
  · rintro ⟨h1, h2, h3⟩
    refine NLA.Opening.ext h1 (funext fun i => h2 i i.isLt) (funext fun j => h3 j j.isLt)

variable [DecidableEq F]

/-- The first nonzero opening of a list, or 0. -/
def firstLink {m k : ℕ} (l : List (NLA.Opening F m k)) : NLA.Opening F m k :=
  (l.find? fun o => o ≠ 0).getD 0

/-- If a property holds for 0 and for all elements, it holds for `firstLink`. If `firstLink`
is 0, then all elements are 0. -/
theorem firstLink_spec {m k : ℕ} (p : NLA.Opening F m k → Prop) (l : List (NLA.Opening F m k))
    (h0 : p 0) (hl : ∀ o ∈ l, p o) : p (firstLink l) ∧ (firstLink l = 0 → ∀ o ∈ l, o = 0) := by
  unfold firstLink
  cases hf : l.find? fun o => o ≠ 0 with
  | none =>
    refine ⟨h0, fun _ o ho => ?_⟩
    simpa using List.find?_eq_none.1 hf o ho
  | some o =>
    have ho := List.mem_of_find?_eq_some hf
    have hne := List.find?_some hf
    exact ⟨hl o ho, fun e => absurd e (by simpa using hne)⟩

/-! ## Interpolation -/

/-- The inverse of the Vandermonde matrix of `t`, through the adjugate. It is computable. -/
def vinv {n : ℕ} (t : Fin n → F) : Matrix (Fin n) (Fin n) F :=
  (Matrix.vandermonde t).det⁻¹ • (Matrix.vandermonde t).adjugate

omit [DecidableEq F] in
/-- `vinv t` is a left and a right inverse of the Vandermonde matrix of distinct `t`. -/
theorem vinv_spec {n : ℕ} (t : Fin n → F) (ht : Function.Injective t) :
    (∀ b j : Fin n, ∑ k, vinv t b k * t k ^ (j : ℕ) = if b = j then 1 else 0) ∧
      (∀ k m : Fin n, ∑ b : Fin n, t k ^ (b : ℕ) * vinv t b m = if k = m then 1 else 0) := by
  set M := Matrix.vandermonde t
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 ht)
  have hW : vinv t = M⁻¹ := by rw [Matrix.inv_def, Ring.inverse_eq_inv']; rfl
  refine ⟨fun b j => ?_, fun k m => ?_⟩
  · have := congrFun (congrFun (Matrix.nonsing_inv_mul M hdet) b) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa [hW, M, Matrix.vandermonde_apply] using this
  · have := congrFun (congrFun (Matrix.mul_nonsing_inv M hdet) k) m
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa [hW, M, Matrix.vandermonde_apply] using this

end Audit.RangeProof
