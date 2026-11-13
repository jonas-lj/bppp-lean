import Audit.NLA.FoldLemmas
import VCVio.CryptoFoundations.SigmaProtocol

/-!
# Audit of the norm-linear argument (NLA)

This file states one round of the NLA as a VCVio `ChallengeVerifyProtocol`, then proves its
completeness and soundness.

Why it exists:
- We audit the completeness and soundness statements of `bppp-lean`.
- Our own `Rel` and fold give an independent view. Later we compare them with Jonas's.
- One round, then the opening in the clear, is a 3-move protocol, like Schnorr.

How it works:
1. Step 1 defines the relation and one round, from the paper (Section 4.9, eq. (19)).
2. Step 2 casts one round as a `ChallengeVerifyProtocol`.
3. Step 3 proves `PerfectlyComplete (roundProtocol m k)`. The fold lemmas are in
   `Audit/NLA/FoldLemmas.lean`.
4. Step 4 (to do) proves soundness from 4 accepting transcripts of `roundProtocol`.
5. Each section names the Spec file to compare with.
- The vector operations are in `Audit/NLA/Vectors.lean`.

Assumptions:
- Scalars are a field `F`. Points are a module `E` over `F`, as in `bppp-lean`.
- A vector of length `m` is a function `Fin m → F`, so the type fixes its length.
- A fold maps length `2m` to length `m`. Odd lengths do not occur in the Rust code: the norm
  length `nm` is a power of two, and the linear length starts at `H_LEN = 8`.
- Slots count from 0. Slot `i` of a weighted norm has the weight `μ^(i+1)`.
- `μ = ρ²`. A fold replaces `ρ` with `μ`. An `Instance` carries a proof that `ρ ≠ 0`.
- The guide's value base `G` is `g` here. The guide's bold `𝐆` is `G` here.

TODO (comparison): Jonas uses `ℕ → F` with an explicit length. To compare our results with
his, add one bridge lemma between the two forms.
-/

namespace Audit.NLA

open OracleComp ChallengeVerifyProtocol

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-! ## Step 1: the relation and one round

Compare with `Bppp/Spec/NormLinear.lean` only after Step 3 is done. -/

variable (F E) in
/-- An NLA instance. The linear part has length `m`, and the norm part has length `k`. -/
structure Instance (m k : ℕ) where
  /-- The commitment. -/
  C : E
  /-- The value base. A fold does not change it. -/
  g : E
  /-- The public vector of the linear part. -/
  c : Fin m → F
  /-- The generators of the linear part. -/
  H : Fin m → E
  /-- The generators of the norm part. -/
  G : Fin k → E
  /-- The weight. The norm uses `μ = ρ²`. -/
  ρ : F
  /-- The fold uses `ρ⁻¹`, so `ρ` must be nonzero. -/
  hρ : ρ ≠ 0

variable (F) in
/-- An NLA witness: the linear part `ℓ` and the norm part `n`. `σ` is not a field, because
`Rel` computes it from `ℓ` and `n`. -/
structure Witness (m k : ℕ) where
  /-- The linear part. -/
  ℓ : Fin m → F
  /-- The norm part. -/
  n : Fin k → F

/-- The relation (paper eq. 19): `w` opens `x.C` over `x.g`, `x.H` and `x.G`. -/
def Rel {m k : ℕ} (x : Instance F E m k) (w : Witness F m k) : Prop :=
  let σ := ip x.c w.ℓ + wip (x.ρ ^ 2) w.n w.n
  x.C = σ • x.g + msm w.ℓ x.H + msm w.n x.G

/-- The prover's first message `X` of a round: the `γ¹` coefficient of the fold.
With `a = ρ⁻¹ n₀` and `b = n₁`, its `g`-part is `2⟨a, b⟩_{μ²} + ⟨c₀, ℓ₁⟩ + ⟨c₁, ℓ₀⟩`. -/
def msgX {m k : ℕ} (x : Instance F E (2 * m) (2 * k)) (w : Witness F (2 * m) (2 * k)) : E :=
  let ρ := x.ρ
  let μ := ρ ^ 2
  let ℓ₀ := evens w.ℓ
  let ℓ₁ := odds w.ℓ
  let n₀ := evens w.n
  let n₁ := odds w.n
  let vX := 2 * ρ⁻¹ * wip (μ ^ 2) n₀ n₁ + ip (evens x.c) ℓ₁ + ip (odds x.c) ℓ₀
  vX • x.g
    + msm ℓ₁ (evens x.H) + msm ℓ₀ (odds x.H)
    + msm (ρ • n₁) (evens x.G) + msm (ρ⁻¹ • n₀) (odds x.G)

/-- The prover's second message `R` of a round: the `γ²` coefficient of the fold.
With `b = n₁`, its `g`-part is `‖b‖²_{μ²} + ⟨c₁, ℓ₁⟩`. -/
def msgR {m k : ℕ} (x : Instance F E (2 * m) (2 * k)) (w : Witness F (2 * m) (2 * k)) : E :=
  let μ := x.ρ ^ 2
  let ℓ₁ := odds w.ℓ
  let n₁ := odds w.n
  let vR := wip (μ ^ 2) n₁ n₁ + ip (odds x.c) ℓ₁
  vR • x.g + msm ℓ₁ (odds x.H) + msm n₁ (odds x.G)

/-- The verifier's fold: the next instance from `X`, `R` and the challenge `γ`. -/
def foldInst {m k : ℕ} (x : Instance F E (2 * m) (2 * k)) (X R : E) (γ : F) :
    Instance F E m k where
  C := x.C + γ • X + (γ ^ 2 - 1) • R
  g := x.g
  c := evens x.c + γ • odds x.c
  H := evens x.H + γ • odds x.H
  G := x.ρ • evens x.G + γ • odds x.G
  ρ := x.ρ ^ 2
  hρ := pow_ne_zero 2 x.hρ

/-- The prover's fold of the witness, with the challenge `γ` and the weight `x.ρ`. -/
def foldWit {m k : ℕ} (x : Instance F E (2 * m) (2 * k)) (γ : F)
    (w : Witness F (2 * m) (2 * k)) : Witness F m k where
  ℓ := evens w.ℓ + γ • odds w.ℓ
  n := x.ρ⁻¹ • evens w.n + γ • odds w.n

/-! ## Step 2: one round as a VCVio protocol

1. `commit`: the prover sends the honest `(X, R)`. It keeps the witness as its state.
2. The verifier sends a uniform challenge `γ`.
3. `respond`: the prover sends the folded witness.
4. `verify`: `Rel` holds for the folded instance and the response.

`Rel` is a `Prop`, and VCVio needs a `Bool` relation, so we use classical `decide`.
The fold uses `x.ρ⁻¹`. The field `Instance.hρ` makes sure that `x.ρ ≠ 0`, so the protocol
relation is `Rel` itself. -/

/-- One NLA round as a VCVio `ChallengeVerifyProtocol`. It maps length `2m` to length `m`. -/
noncomputable def roundProtocol (m k : ℕ) :
    ChallengeVerifyProtocol (Instance F E (2 * m) (2 * k)) (Witness F (2 * m) (2 * k)) (E × E)
      (Witness F (2 * m) (2 * k)) F (Witness F m k)
      (fun x w => by classical exact decide (Rel x w)) where
  commit x w := pure ((msgX x w, msgR x w), w)
  respond x w _ γ := pure (foldWit x γ w)
  verify x XR γ w' := by
    classical exact decide (Rel (foldInst x XR.1 XR.2 γ) w')

/-! ## Step 3: completeness

The honest prover always convinces the verifier. The proof uses the fold lemmas in
`Audit/NLA/FoldLemmas.lean`. Compare with `fold_rel` in
`Bppp/Spec/NormLinearCompleteness.lean`. -/

/-- The honest prover always convinces the verifier. -/
theorem roundProtocol_complete [SampleableType F] (m k : ℕ) :
    PerfectlyComplete (roundProtocol (F := F) (E := E) m k) := by
  classical
  intro x w hw
  have hfold (γ : F) : Rel (foldInst x (msgX x w) (msgR x w) γ) (foldWit x γ w) := by
    have h : Rel x w := of_decide_eq_true hw
    simp only [Rel, foldInst, foldWit, msgX, msgR] at h ⊢
    rw [ip_fold, wip_fold _ _ x.hρ, msm_fold_H, msm_fold_G _ _ x.hρ, h]
    module
  simp [roundProtocol, hfold]

/-! ## Step 4: soundness

From one commitment `(X, R)` and 4 accepted responses at distinct challenges, get a witness
for `x`, or a nontrivial relation among the generators of `x`.

Why 4 challenges and not 3:
1. 3 challenges give openings of `C`, `X` and `R`, because `1`, `γ` and `γ² - 1` are linearly
   independent. The opening of `C` gives the candidate `(ℓ, n)`.
2. The 4th challenge makes a cubic in `γ` vanish. This forces each response to be the honest
   fold of `(ℓ, n)`, and then `σ = ⟨c, ℓ⟩ + ‖n‖²_μ`.

Notes:
- VCVio's `SpeciallySound` takes exactly 2 transcripts and has no escape, so it does not fit.
- `GenRelation` is a trusted part of the statement. A weak escape makes `round_sound` empty.
  So it reads only the generators of `x`, and it needs a nonzero coefficient.
- Compare with `extract_round` and `Relation` in `Bppp/Spec/NormLinearSoundness.lean`.

TODO (ArkLib): decide if we use ArkLib's coordinate-wise special soundness. Its theorem
`coordinateWiseSpecialSoundWithEscape_of_mkWitness_scalar` (`ScalarRound.lean`, at `c488a3a`)
turns a statement of this shape into tree special soundness, and `Composition.lean` chains the
rounds. Its `mkWitness` is our `extractWit`. ArkLib pins a different VCVio commit. -/

/-- A nontrivial linear relation among the generators `g`, `H` and `G` of `x`. -/
def GenRelation {m k : ℕ} (x : Instance F E m k) : Prop :=
  ∃ (s : F) (a : Fin m → F) (b : Fin k → F),
    (s ≠ 0 ∨ a ≠ 0 ∨ b ≠ 0) ∧ s • x.g + msm a x.H + msm b x.G = 0

/-- The vector of length `2m` with the even slots `a` and the odd slots `b`. -/
def interleave {α : Type} {m : ℕ} (a b : Fin m → α) : Fin (2 * m) → α :=
  fun j => if j.val % 2 = 0 then a ⟨j.val / 2, by omega⟩ else b ⟨j.val / 2, by omega⟩

/-- The extractor. Each accepted response is the honest fold `[v]₀ + γ [v]₁` (with `ρ⁻¹` on
`[n]₀`). So a line through the responses at `γ_vec 0` and `γ_vec 1` gives both halves. -/
def extractWit {m k : ℕ} (x : Instance F E (2 * m) (2 * k)) (γ_vec : Fin 4 → F)
    (w_vec : Fin 4 → Witness F m k) : Witness F (2 * m) (2 * k) :=
  let d := (γ_vec 0 - γ_vec 1)⁻¹
  let ℓ₁ := d • ((w_vec 0).ℓ - (w_vec 1).ℓ)
  let ℓ₀ := (w_vec 0).ℓ - γ_vec 0 • ℓ₁
  let n₁ := d • ((w_vec 0).n - (w_vec 1).n)
  let n₀ := x.ρ • ((w_vec 0).n - γ_vec 0 • n₁)
  { ℓ := interleave ℓ₀ ℓ₁, n := interleave n₀ n₁ }

/-- 4 accepted responses with one commitment and distinct challenges give a generator
relation, or `extractWit` computes a witness for `x`. -/
theorem round_sound {m k : ℕ} (x : Instance F E (2 * m) (2 * k)) (X R : E)
    (γ_vec : Fin 4 → F) (hγ : Function.Injective γ_vec) (w_vec : Fin 4 → Witness F m k)
    (hacc : ∀ i, (roundProtocol m k).verify x (X, R) (γ_vec i) (w_vec i) = true) :
    GenRelation x ∨ Rel x (extractWit x γ_vec w_vec) := by
  -- TODO: port the proof of `extract_round` to `Fin` vectors when we replace Jonas's Spec.
  sorry

/-- The bad challenges of a commitment `(X, R)`: the `γ` at which some response accepts. -/
def badSet {m k : ℕ} (x : Instance F E (2 * m) (2 * k)) (X R : E) : Set F :=
  {γ | ∃ w', (roundProtocol m k).verify x (X, R) γ w' = true}

/-- On an instance with no witness and no generator relation, each commitment has no more than
3 bad challenges. The counterexample in our notes shows that 3 can occur.

TODO (soundness error): turn this count into a bound of about `3r/|F|` for `r` rounds, by
round-by-round soundness. The paper states only an asymptotic bound (Theorem 2). -/
theorem badSet_encard_le {m k : ℕ} (x : Instance F E (2 * m) (2 * k))
    (hgen : ¬ GenRelation x) (hwit : ∀ w, ¬ Rel x w) (X R : E) :
    (badSet x X R).encard ≤ 3 := by
  by_contra h
  have h4 : (4 : ℕ∞) ≤ (badSet x X R).encard := Order.add_one_le_of_lt (not_le.mp h)
  obtain ⟨t, hts, ht⟩ := Set.exists_subset_encard_eq h4
  have htf : t.Finite := Set.finite_of_encard_eq_coe ht
  have hcard : htf.toFinset.card = 4 := by
    have := Set.encard_coe_eq_coe_finsetCard htf.toFinset
    rw [Set.Finite.coe_toFinset, ht] at this
    exact_mod_cast this.symm
  let e := htf.toFinset.equivFin
  let γ_vec : Fin 4 → F := fun i => (e.symm (Fin.cast hcard.symm i)).1
  have hγ : Function.Injective γ_vec := fun i j hij =>
    Fin.cast_injective _ (e.symm.injective (Subtype.ext hij))
  have hbad (i : Fin 4) : γ_vec i ∈ badSet x X R :=
    hts ((Set.Finite.mem_toFinset htf).mp (e.symm (Fin.cast hcard.symm i)).2)
  choose w_vec hacc using hbad
  rcases round_sound x X R γ_vec hγ w_vec hacc with h | h
  · exact hgen h
  · exact hwit _ h

end Audit.NLA
