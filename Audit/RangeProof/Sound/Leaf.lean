import Audit.RangeProof.Sound.Coords
import Audit.NLAFull.Proofs
import Audit.NLAFull.Rust

/-!
# One leaf of the range fork tree

This file runs the NLA extractor at one `τ` leaf of a `RangeForkTree`.

Why it exists:
- Below each `τ`, the range fork tree holds an NLA fork tree. The extractor of the full NLA
  (`Audit/NLAFull/Full.lean`), `nlaExtractN`, is computable and proved sound (`nla_sound_n`).
  This file connects it to the leaf.

How it works:
1. `leafInputs` computes the inputs of `norm_linear::verify` at the leaf, with the same Model
   functions as `Circuit.verify`. `leafInputs_eq` gives Jonas's names for them.
2. `toInstAt` turns Jonas's NLA instance into an instance of the full NLA with given lengths.
3. `toNla` turns the NLA subtree into a fork tree of the full NLA. `allPaths_toNla` moves the
   accepted paths across.
4. `leafVals` gives two combinations: a candidate link, and the coordinates of
   `Y(τ) = C(τ) - P(τ)`. `leafVals_spec` gives their facts.

Assumptions:
- The facts hold when every NLA path at the leaf satisfies Jonas's NLA relation. The file
  `Audit/RangeProof/Sound/Runs.lean` gets this from the Rust runs.
-/

namespace Audit.RangeProof.Sound

open Finset Bppp Audit.TreeSoundness

variable {F E : Type} [Field F] [DecidableEq F] [AddCommGroup E] [Module F E] [DecidableEq E]

set_option linter.unusedSectionVars false

/-! ## The inputs of the NLA -/

/-- The inputs of `norm_linear::verify` at a leaf: `c(τ)`, `p_s(τ)`, `p_n(τ)` and the
constraints. These are the lines of `Circuit.verify` after `τ`. -/
def leafInputs (P : CircuitParams) (alpha rho lambda beta delta tau : F) :
    Result (List F × F × List F × Constraints F) := do
  let mu := rho * rho
  let delta_inv ← inverse delta
  let constraints ← Constraints.new P alpha mu lambda
  let p_n_tau ← (constraints.p_n delta_inv).eval tau
  let p_s_tau := weighted_norm p_n_tau mu +
    2 * (constraints.lambda_al + constraints.mu_am) * (tau * tau * tau)
  let c_tau ← (Circuit.c constraints beta).eval tau
  pure (c_tau, p_s_tau, p_n_tau, constraints)

/-- `leafInputs` gives the inputs with Jonas's names. -/
theorem leafInputs_eq (P : CircuitParams) (hv : P.Valid) (alpha rho lambda beta delta : F)
    (τ : Fˣ) (C : Constraints F) (hδ : delta ≠ 0)
    (hCnew : Constraints.new P alpha (rho * rho) lambda = .ok C)
    (hC : Constraints.Correct P alpha (rho * rho) lambda C hv) :
    leafInputs P alpha rho lambda beta delta τ = .ok (Circuit.cTau C beta τ,
      Circuit.psTau P C rho delta τ, Circuit.pnTau P C delta τ, C) := by
  obtain ⟨hcu, -⟩ := Circuit.c_spec P hv alpha rho lambda beta delta C hC
  have hpnu := Circuit.uniform_p_n P hv alpha rho lambda delta C hC
  simp [leafInputs, inverse, hδ, hCnew, Laurent.eval_eq hpnu τ, Laurent.eval_eq hcu τ, bind,
    Except.bind, pure, Except.pure, Circuit.cTau, Circuit.psTau, Circuit.pnTau]

/-! ## Jonas's NLA instances as instances of the full NLA -/

/-- Jonas's NLA instance `x` as an instance of the full NLA, with the lengths `m` and `k`. -/
def toInstAt (g : E) (m k : ℕ) (x : Spec.NormLinear.Instance F E) (hρ : x.ρ ≠ 0) :
    NLA.Instance F E m k where
  C := x.C
  g := g
  c i := x.c i
  H i := x.H i
  G i := x.G i
  ρ := x.ρ
  hρ := hρ

/-- Jonas's NLA relation is the relation of the full NLA. -/
theorem rel_iff_at (g : E) (x : Spec.NormLinear.Instance F E) (hρ : x.ρ ≠ 0)
    (hμ : x.μ = x.ρ ^ 2) {m k : ℕ} (hm : x.Lℓ = m) (hk : x.Ln = k)
    (w : Spec.NormLinear.Witness F) :
    Spec.NormLinear.Rel g x w ↔
      NLA.Rel (toInstAt g m k x hρ) ⟨fun i => w.ℓ i, fun i => w.n i⟩ := by
  subst hm hk
  exact NLA.Bridge.rel_iff g x hρ hμ w

/-- The fold of the full NLA is Jonas's fold. -/
theorem fold_at (g : E) (x : Spec.NormLinear.Instance F E) (hρ : x.ρ ≠ 0)
    (hμ : x.μ = x.ρ ^ 2) {m k : ℕ} (hm : x.Lℓ = m) (hk : x.Ln = k) (X R : E) (γ : F) :
    NLA.foldInst (toInstAt g m k x hρ) X R γ =
      toInstAt g (NLA.half m) (NLA.half k) (Spec.NormLinear.foldInst x X R γ)
        (by simpa [Spec.NormLinear.foldInst, hμ] using hρ) := by
  subst hm hk
  exact NLA.Bridge.fold_toInst g x hρ hμ X R γ

/-! ## The NLA subtree as a fork tree of the full NLA -/

/-- The NLA subtree of a leaf as a fork tree of the full NLA. The final `(l, n)` is the witness. -/
def toNla : (n : ℕ) → {m k : ℕ} → (nlaRounds F E n).ForkTree (nlaForks F E n) (F × List F) →
    (NLA.nlaSystem F E n m k).ForkTree (NLA.nlaForkRules F E n m k)
  | 0, _, _, z => (⟨fun _ => z.1, fun j => z.2.getD j 0⟩ : NLA.Witness F _ _)
  | n + 1, _, _, t => ⟨t.commitment, t.challenges, fun i => toNla n (t.children i)⟩

/-- If Jonas's relation holds on every path of the subtree, then the full NLA accepts every path of
`toNla`. -/
theorem allPaths_toNla (g : E) : ∀ (n : ℕ) {m k : ℕ} (x : Spec.NormLinear.Instance F E)
    (hρ : x.ρ ≠ 0) (hμ : x.μ = x.ρ ^ 2) (hm : x.Lℓ = m) (hk : x.Ln = k)
    (hn : NLA.numRounds m k = n) (t : (nlaRounds F E n).ForkTree (nlaForks F E n) (F × List F)),
    t.AllPaths (fun tr z => Spec.NormLinear.Rel g
      (Spec.NormLinear.foldPath x (nlaParts tr).1 (nlaParts tr).2)
      ⟨fun j => [z.1].getD j 0, fun j => z.2.getD j 0⟩) →
    (toNla n t).AllPaths ((NLA.nlaSystem F E n m k).Verify (toInstAt g m k x hρ))
  | 0, m, k, x, hρ, hμ, hm, hk, hn, z, h => by
    have hb := NLA.isBase_of_numRounds_eq_zero hn
    have h' := (rel_iff_at g x hρ hμ hm hk _).1 h
    change NLA.Rel (toInstAt g m k x hρ) ⟨fun _ => z.1, fun j => z.2.getD j 0⟩
    convert h' using 2
    funext i
    have : (i : ℕ) = 0 := by have := i.isLt; simp only [NLA.IsBase] at hb; omega
    simp [this]
  | n + 1, m, k, x, hρ, hμ, hm, hk, hn, t, h => by
    intro i
    have hρ' : x.μ ≠ 0 := by rw [hμ]; exact pow_ne_zero 2 hρ
    have ih := allPaths_toNla g n (Spec.NormLinear.foldInst x t.commitment.1 t.commitment.2
      (t.challenges.val i)) hρ' rfl (by rw [← hm]; rfl) (by rw [← hk]; rfl)
      (NLA.numRounds_half_of_eq_succ hn) (t.children i) (h i)
    rw [← fold_at g x hρ hμ hm hk] at ih
    exact ih

/-! ## The leaf -/

section Leaf

variable (P : CircuitParams) (gens : Generators E) (vcs : List (PedersenCommitment E))
  (cS cO cL cR : E)

/-- The instance of `norm_linear::verify` at a leaf, in Jonas's form. -/
def leafSpecInst (c : List F) (ps : F) (pn : List F) (C : Constraints F) (delta rho : F)
    (τ : Fˣ) : Spec.NormLinear.Instance F E :=
  NormLinear.vInst gens (ps • gens.g + (List.zipWith (· • ·) pn gens.g_vec).sum +
    ((Circuit.extraOf C delta τ vcs cS cO cL cR).map fun (s, p) => s • p).sum) c rho .new .new

/-- The instance of `norm_linear::verify` at a leaf, as an instance of the full NLA. -/
def leafInst (c : List F) (ps : F) (pn : List F) (C : Constraints F) (delta rho : F)
    (τ : Fˣ) (hρ : rho ≠ 0) : NLA.Instance F E H_LEN P.nm :=
  toInstAt gens.g H_LEN P.nm (leafSpecInst gens vcs cS cO cL cR c ps pn C delta rho τ) hρ

/-- An opening of the full NLA as a combination. -/
def toComb (o : NLA.Opening F H_LEN P.nm) : Combination F P := (o.σ, o.ℓ, o.n)

/-- The coordinates of the public part `P(τ) = p_s g + ⟨p_n, g_vec⟩`. -/
def pubPart (ps : F) (pn : List F) : Combination F P :=
  ps • eg P + (List.zipWith (· • ·) pn (unitGens P).g_vec).sum

/-- The values of a leaf: a candidate link, and the coordinates of `Y(τ) = C(τ) - P(τ)`. If the
NLA extractor gives a witness, the link is 0. If it gives a link, the coordinates are 0. -/
def leafVals (alpha : F) (rho : {ρ : F // ρ ≠ 0}) (lambda beta delta : F)
    (tau : {τ : F // τ ≠ 0})
    (t : (nlaRounds F E (numNlaRounds P)).ForkTree (nlaForks F E (numNlaRounds P)) (F × List F)) :
    Combination F P × Combination F P :=
  match leafInputs P alpha rho.val lambda beta delta tau.val with
  | .error _ => (0, 0)
  | .ok (c, ps, pn, C) =>
    let x := leafInst P gens vcs cS cO cL cR c ps pn C delta rho.val
      (Units.mk0 tau.val tau.property) rho.property
    match NLA.nlaExtractN (numNlaRounds P) x (toNla _ t) with
    | .inl w => (0, toComb P (x.opening w) - pubPart P ps pn)
    | .inr o => (toComb P o, 0)

/-- The witness that the NLA extractor gives at a leaf, in Jonas's form, or 0. The proofs use
it. The extractor does not. -/
def leafWit (alpha : F) (rho : {ρ : F // ρ ≠ 0}) (lambda beta delta : F)
    (tau : {τ : F // τ ≠ 0})
    (t : (nlaRounds F E (numNlaRounds P)).ForkTree (nlaForks F E (numNlaRounds P)) (F × List F)) :
    Spec.NormLinear.Witness F :=
  match leafInputs P alpha rho.val lambda beta delta tau.val with
  | .error _ => ⟨0, 0⟩
  | .ok (c, ps, pn, C) =>
    let x := leafInst P gens vcs cS cO cL cR c ps pn C delta rho.val
      (Units.mk0 tau.val tau.property) rho.property
    match NLA.nlaExtractN (numNlaRounds P) x (toNla _ t) with
    | .inl w => NLA.Bridge.ofWit w
    | .inr _ => ⟨0, 0⟩

/-! ## Facts about the leaf -/

omit [DecidableEq F] [DecidableEq E] in
theorem map_zipWith_sum {E' : Type} [AddCommGroup E'] [Module F E'] (φ : E' →ₗ[F] E) :
    ∀ (a : List F) (L : List E'),
      φ (List.zipWith (· • ·) a L).sum = (List.zipWith (· • ·) a (L.map φ)).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: a, y :: L => by simp [map_zipWith_sum φ a L]

omit [DecidableEq E] in
theorem map_unitGens_g (hg : gens.g_vec.length = P.nm) :
    (unitGens (F := F) P).g_vec.map (combMap P gens) = gens.g_vec := by
  apply List.ext_getElem (by simp [unitGens, hg])
  intro j h1 h2
  simp only [unitGens, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply]
  rw [combMap_eG gens hg, List.getD_eq_getElem _ _ h2]

omit [DecidableEq E] in
/-- `combMap` of the public part is the public part over the real generators. -/
theorem combMap_pubPart (hg : gens.g_vec.length = P.nm) (ps : F) (pn : List F) :
    combMap P gens (pubPart P ps pn) =
      ps • gens.g + (List.zipWith (· • ·) pn gens.g_vec).sum := by
  rw [pubPart, map_add, map_smul, combMap_eg, map_zipWith_sum, map_unitGens_g P gens hg]

omit [DecidableEq F] [DecidableEq E] in
theorem combMap_toComb (o : NLA.Opening F H_LEN P.nm) :
    combMap P gens (toComb P o) = o.σ • gens.g + NLA.msm o.ℓ (fun i => gens.h_vec.getD i 0) +
      NLA.msm o.n (fun j => gens.g_vec.getD j 0) := rfl

theorem leafSpecInst_facts (c : List F) (ps : F) (pn : List F) (C : Constraints F)
    (delta rho : F) (τ : Fˣ) (hg : gens.g_vec.length = P.nm) :
    let x := leafSpecInst gens vcs cS cO cL cR c ps pn C delta rho τ
    x.Lℓ = c.length ∧ x.Ln = P.nm ∧ x.μ = x.ρ ^ 2 ∧ x.ρ = rho ∧
      (∀ i, x.H i = gens.h_vec.getD i 0) ∧ (∀ j, x.G j = gens.g_vec.getD j 0) ∧
      x.C = ps • gens.g + (List.zipWith (· • ·) pn gens.g_vec).sum +
        ((Circuit.extraOf C delta τ vcs cS cO cL cR).map fun (s, p) => s • p).sum := by
  simp [leafSpecInst, NormLinear.vInst, NormLinear.LazyBases.new_w, NormLinear.contract'_one,
    hg, sq]

/-- **One leaf.** Take the NLA inputs `hdata`, and assume Jonas's NLA relation on every path.
Then the link of `leafVals` maps to 0. If the link is 0, the coordinates map to `Y(τ)`, and
`leafWit` satisfies the relation. -/
theorem leafVals_spec (hg : gens.g_vec.length = P.nm)
    (hrounds : NLA.numRounds H_LEN P.nm = numNlaRounds P) (heven : NLA.EvenNorms H_LEN P.nm)
    (alpha : F) (rho : {ρ : F // ρ ≠ 0}) (lambda beta delta : F) (tau : {τ : F // τ ≠ 0})
    (t : (nlaRounds F E (numNlaRounds P)).ForkTree (nlaForks F E (numNlaRounds P)) (F × List F))
    (c : List F) (ps : F) (pn : List F) (C : Constraints F)
    (hdata : leafInputs P alpha rho.val lambda beta delta tau.val = .ok (c, ps, pn, C))
    (hc : c.length = H_LEN)
    (hacc : t.AllPaths (fun tr z => Spec.NormLinear.Rel gens.g
      (Spec.NormLinear.foldPath (leafSpecInst gens vcs cS cO cL cR c ps pn C delta rho.val
        (Units.mk0 tau.val tau.property)) (nlaParts tr).1 (nlaParts tr).2)
      ⟨fun j => [z.1].getD j 0, fun j => z.2.getD j 0⟩)) :
    combMap P gens (leafVals P gens vcs cS cO cL cR alpha rho lambda beta delta tau t).1 = 0 ∧
      ((leafVals P gens vcs cS cO cL cR alpha rho lambda beta delta tau t).1 = 0 →
        combMap P gens (leafVals P gens vcs cS cO cL cR alpha rho lambda beta delta tau t).2 =
          ((Circuit.extraOf C delta (Units.mk0 tau.val tau.property) vcs cS cO cL cR).map
            fun (s, p) => s • p).sum ∧
        ∃ w : NLA.Witness F H_LEN P.nm,
          NLA.Rel (leafInst P gens vcs cS cO cL cR c ps pn C delta rho.val
            (Units.mk0 tau.val tau.property) rho.property) w ∧
          (leafVals P gens vcs cS cO cL cR alpha rho lambda beta delta tau t).2 =
            toComb P ((leafInst P gens vcs cS cO cL cR c ps pn C delta rho.val
              (Units.mk0 tau.val tau.property) rho.property).opening w) - pubPart P ps pn ∧
          leafWit P gens vcs cS cO cL cR alpha rho lambda beta delta tau t =
            NLA.Bridge.ofWit w) := by
  set τu : Fˣ := Units.mk0 tau.val tau.property
  set xS := leafSpecInst gens vcs cS cO cL cR c ps pn C delta rho.val τu
  set x := leafInst P gens vcs cS cO cL cR c ps pn C delta rho.val τu rho.property
  obtain ⟨hm, hk, hμ, hρ, hH, hG, hC⟩ :=
    leafSpecInst_facts P gens vcs cS cO cL cR c ps pn C delta rho.val τu hg
  have hacc' := allPaths_toNla gens.g _ xS rho.property hμ (hm.trans hc) hk hrounds t hacc
  have hs := NLA.nla_sound_n (F := F) (E := E) (numNlaRounds P) hrounds heven x (toNla _ t) hacc'
  have hpt : ∀ o : NLA.Opening F H_LEN P.nm, combMap P gens (toComb P o) = x.point o := by
    intro o
    rw [combMap_toComb]
    simp only [NLA.Instance.point, x, leafInst, toInstAt, hH, hG]
  simp only [leafVals, leafWit, hdata]
  rcases hout : NLA.nlaExtractN (numNlaRounds P) x (toNla _ t) with w | o
  · rw [hout] at hs
    have hs' : NLA.Rel x w := hs
    refine ⟨map_zero _, fun _ => ⟨?_, w, hs', rfl, rfl⟩⟩
    rw [map_sub, hpt, combMap_pubPart P gens hg, ← hs']
    change xS.C - _ = _
    rw [hC]
    abel
  · rw [hout] at hs
    obtain ⟨hne, hz⟩ := (hs : x.IsGeneratorLink o)
    refine ⟨?_, fun h0 => absurd ?_ hne⟩
    · rw [hpt]; exact hz
    · simp only [toComb, Prod.mk_eq_zero] at h0
      exact NLA.Opening.ext h0.1 h0.2.1 h0.2.2

end Leaf

end Audit.RangeProof.Sound
