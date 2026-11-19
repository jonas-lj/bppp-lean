import Audit.NLA.Extract
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
3. Step 3 states completeness, `RoundCompleteness`.
4. Step 4 states soundness from 4 accepting transcripts, `RoundSoundness`. The extractor's
   formula is in `Audit/NLA/Extract.lean`.
- This file only states 3 and 4. `Audit/NLA/Proofs.lean` proves them as
  `roundProtocol_complete` and `round_sound`, and `Audit.lean` imports it.
5. `Audit/NLA/BadChallenges.lean` derives a corollary: each commitment has no more than 3 bad
   challenges.
6. Each section names the Spec file to compare with.
- The vector operations are in `Audit/Vectors.lean`.
- `Audit/NLA.lean` and `Audit/Vectors.lean` hold everything to review. The folder `Audit/NLA/`
  holds only proofs, the extractor's formula, and corollaries.

Assumptions:
- Scalars are a field `F`. Points are a module `E` over `F`, as in `bppp-lean`.
- A vector of length `m` is a function `Fin m → F`, so the type fixes its length.
- A fold maps each length `m` to `half m = ⌈m/2⌉`.
- `odds` pads an odd length with 0, as the Rust code does. In the Rust code, this occurs only
  when the linear part has length 1 and the norm part is still long.
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

variable (F) in
/-- The coefficients of a point over the generators `g`, `H` and `G`. -/
@[ext]
structure Opening (m k : ℕ) where
  /-- The coefficient on `g`. -/
  σ : F
  /-- The coefficients on `H`. -/
  ℓ : Fin m → F
  /-- The coefficients on `G`. -/
  n : Fin k → F

instance {m k : ℕ} : Zero (Opening F m k) := ⟨⟨0, 0, 0⟩⟩

/-- The point that `o` opens over the generators of `x`. -/
def Instance.point {m k : ℕ} (x : Instance F E m k) (o : Opening F m k) : E :=
  o.σ • x.g + msm o.ℓ x.H + msm o.n x.G

/-- The opening that a witness gives: `w.ℓ` and `w.n`, with `σ = ⟨c, ℓ⟩ + ‖n‖²_μ` on `g`. -/
def Instance.opening {m k : ℕ} (x : Instance F E m k) (w : Witness F m k) : Opening F m k where
  σ := ⟪x.c, w.ℓ⟫ + ‖w.n‖²_(x.ρ²)
  ℓ := w.ℓ
  n := w.n

/-- The relation (paper eq. 19): `C = σ•g + ⟨ℓ, H⟩ + ⟨n, G⟩` with `σ = ⟨c, ℓ⟩ + ‖n‖²_μ`.
That is, the opening that `w` gives opens `x.C`. -/
def Rel {m k : ℕ} (x : Instance F E m k) (w : Witness F m k) : Prop :=
  x.C = x.point (x.opening w)

/-- The prover's first message `X` of a round: the `γ¹` coefficient of the fold.
With `a = ρ⁻¹ n₀` and `b = n₁`, its `g`-part is `2⟨a, b⟩_{μ²} + ⟨c₀, ℓ₁⟩ + ⟨c₁, ℓ₀⟩`. -/
def msgX {m k : ℕ} (x : Instance F E m k) (w : Witness F m k) : E :=
  let ρ := x.ρ
  let μ := ρ²
  let ℓ₀ := evens w.ℓ
  let ℓ₁ := odds w.ℓ
  let n₀ := evens w.n
  let n₁ := odds w.n
  let vX := 2 * ρ⁻¹ * ⟪n₀, n₁⟫_(μ²) + ⟪evens x.c, ℓ₁⟫ + ⟪odds x.c, ℓ₀⟫
  vX • x.g
    + msm ℓ₁ (evens x.H) + msm ℓ₀ (odds x.H)
    + msm (ρ • n₁) (evens x.G) + msm (ρ⁻¹ • n₀) (odds x.G)

/-- The prover's second message `R` of a round: the `γ²` coefficient of the fold.
With `b = n₁`, its `g`-part is `‖b‖²_{μ²} + ⟨c₁, ℓ₁⟩`. -/
def msgR {m k : ℕ} (x : Instance F E m k) (w : Witness F m k) : E :=
  let μ := x.ρ²
  let ℓ₁ := odds w.ℓ
  let n₁ := odds w.n
  let vR := ‖n₁‖²_(μ²) + ⟪odds x.c, ℓ₁⟫
  vR • x.g + msm ℓ₁ (odds x.H) + msm n₁ (odds x.G)

/-- The verifier's fold: the next instance from `X`, `R` and the challenge `γ`. A padded slot
is the identity, so it adds nothing. -/
def foldInst {m k : ℕ} (x : Instance F E m k) (X R : E) (γ : F) :
    Instance F E (half m) (half k) where
  C := x.C + γ • X + (γ² - 1) • R
  g := x.g
  c := evens x.c + γ • odds x.c
  H := evens x.H + γ • odds x.H
  G := x.ρ • evens x.G + γ • odds x.G
  ρ := x.ρ²
  hρ := pow_ne_zero 2 x.hρ

/-- The prover's fold of the witness, with the challenge `γ` and the weight `x.ρ`. -/
def foldWit {m k : ℕ} (x : Instance F E m k) (γ : F)
    (w : Witness F m k) : Witness F (half m) (half k) where
  ℓ := evens w.ℓ + γ • odds w.ℓ
  n := x.ρ⁻¹ • evens w.n + γ • odds w.n

/-! ## Step 2: one round as a VCVio protocol

1. `commit`: the prover sends the honest `(X, R)`. It needs no state, because `respond` gets
   the witness.
2. The verifier sends a uniform challenge `γ`.
3. `respond`: the prover sends the folded witness.
4. `verify`: `Rel` holds for the folded instance and the response.

`Rel` is a `Prop`, and VCVio needs a `Bool` relation, so we use classical `decide`.
The fold uses `x.ρ⁻¹`. The field `Instance.hρ` makes sure that `x.ρ ≠ 0`, so the protocol
relation is `Rel` itself. -/

/-- One NLA round as a VCVio `ChallengeVerifyProtocol`. It maps the lengths `(m, k)` to
`(half m, half k)`. -/
noncomputable def roundProtocol (m k : ℕ) :
    ChallengeVerifyProtocol (Instance F E m k) (Witness F m k) (E × E)
      Unit F (Witness F (half m) (half k))
      (fun x w => by classical exact decide (Rel x w)) where
  commit x w := pure ((msgX x w, msgR x w), ())
  respond x w _ γ := pure (foldWit x γ w)
  verify x XR γ w' := by
    classical exact decide (Rel (foldInst x XR.1 XR.2 γ) w')

/-! ## Step 3: completeness

The honest prover always convinces the verifier. Compare with `fold_rel` in
`Bppp/Spec/NormLinearCompleteness.lean`. -/

variable (F E) in
/-- Completeness: the honest prover always convinces the verifier. `roundProtocol_complete` in
`Audit/NLA/Proofs.lean` proves it. -/
def RoundCompleteness [SampleableType F] : Prop :=
  ∀ m k : ℕ, PerfectlyComplete (roundProtocol (F := F) (E := E) m k)

/-! ## Step 4: soundness

From one commitment `(X, R)` and 4 accepted responses at distinct challenges, get a witness
for `x`, or a nontrivial relation among the generators of `x`.

Why 4 challenges and not 3:
1. 3 challenges give openings of `C`, `X` and `R`, because `1`, `γ` and `γ² - 1` are linearly
   independent. The opening of `C` gives the candidate `(ℓ, n)`.
2. The 4th challenge makes a cubic in `γ` vanish for each pair of slots. This forces the
   pairs to fold honestly, and then `σ = ⟨c, ℓ⟩ + ‖n‖²_μ`.

Notes:
- VCVio's `SpeciallySound` takes exactly 2 transcripts and has no escape, so it does not fit.
- `Instance.Independent` is a trusted part of the statement. A strong assumption makes
  `RoundSoundness` empty. So it reads only the generators of `x`.
- Compare with `extract_round` and `Relation` in `Bppp/Spec/NormLinearSoundness.lean`.

TODO (ArkLib): decide if we use ArkLib's coordinate-wise special soundness. Its theorem
`coordinateWiseSpecialSoundWithEscape_of_mkWitness_scalar` (`ScalarRound.lean`, at `c488a3a`)
turns a statement of this shape into tree special soundness, and `Composition.lean` chains the
rounds. Its `mkWitness` is our `extractWit`. ArkLib pins a different VCVio commit. -/

/-- The generators `g`, `H` and `G` of `x` are linearly independent: only the zero opening
opens the zero point. The discrete-log assumption makes this hold for a prover. -/
def Instance.Independent {m k : ℕ} (x : Instance F E m k) : Prop :=
  ∀ o : Opening F m k, x.point o = 0 → o = 0

/-- The extractor. Its formula `extractVec` is in `Audit/NLA/Extract.lean`. -/
def extractWit {m k : ℕ} (x : Instance F E m k) (γ_vec : Fin 4 → F)
    (w_vec : Fin 4 → Witness F (half m) (half k)) : Witness F m k where
  ℓ := extractVec 1 γ_vec (fun i => (w_vec i).ℓ)
  n := extractVec x.ρ γ_vec (fun i => (w_vec i).n)

variable (F E) in
/-- The top of a fork: one commitment `(X, R)` and 4 distinct challenges. -/
structure ForkHead where
  /-- The prover's first message. -/
  X : E
  /-- The prover's second message. -/
  R : E
  /-- The 4 challenges. -/
  γ : Fin 4 → F
  /-- The challenges are distinct. -/
  hDistinct : ∀ i j, i ≠ j → γ i ≠ γ j

/-- 4 accepted transcripts of one round: a fork head and 4 accepted responses. -/
structure Fork {m k : ℕ} (x : Instance F E m k) extends ForkHead F E where
  /-- The 4 responses. -/
  w : Fin 4 → Witness F (half m) (half k)
  /-- The verifier accepts each response. -/
  hAccepted : ∀ i, (roundProtocol m k).verify x (X, R) (γ i) (w i) = true

variable (F E) in
/-- Soundness: if the generators of `x` are independent, then `extractWit` computes a witness
from a fork. `round_sound` in `Audit/NLA/Proofs.lean` proves it. The norm length `k` must be even:
`round_not_sound_odd` in `Audit/NLA/Counterexamples.lean` shows that this is necessary.

Note for reviewers: Lean does not check that `extractWit` is efficient. Check that `extractVec`
in `Audit/NLA/Extract.lean` uses only field operations, and no choice. -/
def RoundSoundness : Prop :=
  ∀ {m k : ℕ} (x : Instance F E m k) (f : Fork x), x.Independent → k % 2 = 0 →
    Rel x (extractWit x f.γ f.w)

end Audit.NLA
