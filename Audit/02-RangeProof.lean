import Audit.«01-TreeSoundness»
import Bppp.Model.RangeProof

/-!
# Soundness and completeness of the Bulletproofs++ range proof

This file states that the Rust range proof is sound and complete.

Why it exists:
- It is the one file to read to see what we prove about the range proof.
- The proofs and the extractor are in `Audit/RangeProof/`. Nobody needs to review them.

What the theorems say:
1. Soundness (`RangeSoundness`): take a fork tree (`RangeForkTree`) in which the Rust verifier
   `verify_batch` accepts every path. Then the extractor computes a witness (`RangeWitness`)
   that satisfies the relaxed relation (`RangeRel`). The relation has two cases:
   - Each commitment is `V_i = v_i • H + s_i • G` with `v_i < 2^bits` (`OpensInRange`). This is
     the relation of a range proof.
   - The witness has a link between the generators (`IsGeneratorLink`). A link solves discrete
     log.
2. Completeness (`RangeCompleteness`): for a witness in `OpensInRange`, the verifier accepts the
   run of the Rust prover `prove_batch` (`honest`) for all random coins and all challenges.

What this file takes from the Rust code (`Bppp/Model/`, a Lean copy of the Rust code):
- The two calls: `RangeProof.verify_batch` (`RangeProof.lean:49`) in `rangeVerify`, and
  `RangeProof.prove_batch` (`RangeProof.lean:38`) in `proveWith`.
- The circuit sizes `CircuitParams.new` (`Constraints.lean:23`). It fails only for `m = 0`.
- The constants `H_LEN = 8` (`Crs.lean:16`) and `NormLinear.proof_shape` (`NormLinear.lean:48`,
  the number of NLA rounds).
- The transcript log `Entry` (`Transcript.lean:15`). The Model replaces the hash with a function
  of the log, and `hashOf` is such a function.
- The types that the two calls take: `Range` (`Fastcrypto.lean:45`), `Generators` (`Crs.lean:25`),
  `PedersenCommitment` (`Fastcrypto.lean:66`), `CircuitProof` (`Circuit.lean:37`),
  `NormLinearProof` (`NormLinear.lean:22`) and `Circuit.Randomness` (`Circuit.lean:79`).
- Everything else is defined here: the statement, the protocol rounds, the fork rules and the
  relation. `RangeStatement.gens`, `.generators` and `.commitments` build the Rust inputs from
  the statement.

Why this is a real range proof:
- The witness comes from a named extractor, `extract`. It is not "some witness that exists". In
  a real group, an opening and a link always exist, so an `∃` form says nothing.
- `Audit.RangeProof.Sound.range_sound : RangeSoundness rangeExtract` names the extractor
  (`Audit/RangeProof/Sound/Extractor.lean`). Check that it works for every `F` and `E`, is not
  `noncomputable`, has no `@[implemented_by]`, and that its tests run. Then a link that it
  outputs comes from the prover.
- `Audit.RangeProof.range_complete : RangeCompleteness` proves completeness.
- Soundness alone holds for a verifier that rejects everything. Completeness rules this out.

How the range proof fits tree special soundness:
- `Audit/01-TreeSoundness.lean` defines tree special soundness and completeness for any
  public-coin protocol (`Relation`, `RoundTypes`, `RoundTypes.ForkTree`, `ProofSystem`,
  `ProofSystem.SpecialSound`, `ProofSystem.Complete`). Read it first.
- This file adds only the facts about the range proof. Check them against `circuit.rs`:
  1. `rangeProtocol` and `nlaRounds`: the commitment and the challenge of each round.
  2. `rangeVerify` and `hashOf`: the Rust `verify_batch` on a transcript. The hash answers each
     query with the next challenge of the transcript.
  3. `rangeForks` and `nlaForks`: for each round, the number of challenges and the rules for
     them.
  4. `RangeStatement`, `RangeWitness` and `RangeRel`: the relation. The statement holds the
     generators directly. Rust's `verify_batch` reads its `generators` function only at `nm`,
     so the result holds for every choice of generators, and the real CRS is one of them.
  5. `honestStrategy`: each message is a part of the Rust proof, computed with the challenges
     so far.

Assumptions:
- `Bppp/Model/` is a correct copy of the Rust code. Review it against the Rust code.
- Each transcript has its own hash, `hashOf`. This is the usual programmable random-oracle view
  of a fork.
- A valid tree needs enough allowed challenges in each round. The largest need is `λ`, with
  `m(nm + 8) + 1` values. In a smaller field, no valid tree exists, and the statement says
  nothing. Real fields have about `2^252` elements.
- Some challenges are excluded: 16 values of `α`, and the value 0 of `ρ`, `δ`, `β` and `τ` (in
  `rangeProtocol`), and `-ρ` for each `ρ` (in `rangeForks`). A forking lemma must count them.
- The result is special soundness, with no probabilities. Knowledge soundness also needs a
  forking lemma.
-/

namespace Audit.RangeProof

open Bppp Audit.TreeSoundness

variable {F E : Type} [Field F] [DecidableEq F] [AddCommGroup E] [Module F E] [DecidableEq E]

/-- The number of digits `Nd = m · d`. Rust stores it as `n_d`. -/
abbrev Nd (P : CircuitParams) : ℕ := P.m * P.d

/-- The number of NLA rounds. The Rust verifier rejects a proof with another number. -/
abbrev numNlaRounds (P : CircuitParams) : ℕ := (NormLinear.proof_shape H_LEN P.nm).1


/-! ## The range proof as a protocol -/

section Protocol

variable (F E)

/-- The NLA rounds: in each round, the commitment `(X, R)` and the challenge `γ`. After them,
the response is `(l, n)`, the final opening. -/
def nlaRounds : ℕ → RoundTypes
  | 0 => .done
  | n + 1 => .round (E × E) F (nlaRounds n)

/-- The range proof as a protocol (`circuit.rs`, `verify`). The comment on each round names the
commitment and the challenge. The input commitments `V_i` are not prover messages. -/
def rangeProtocol (P : CircuitParams) : RoundTypes :=
  .round (E × E) {α : F // ∀ j : ℕ, j < 16 → α + j ≠ 0} <|   -- `C_L`, `C_O`; then `α`
  .round E {ρ : F // ρ ≠ 0} <|                               -- `C_R`; then `ρ`
  .round Unit {δ : F // δ ≠ 0} <|                            -- nothing; then `δ`
  .round Unit {β : F // β ≠ 0} <|                            -- nothing; then `β`
  .round Unit F <|                                           -- nothing; then `λ`
  .round E {τ : F // τ ≠ 0} <|                               -- `C_S`; then `τ`
  nlaRounds F E (numNlaRounds P)            -- `(X_j, R_j)`; then `γ_j`. At the end, `(l, n)`.
-- The excluded values make Rust fail: `α + j = 0` in `batch_invert`, and an inverse of `ρ`,
-- `δ` or `τ` in the verifier. The prover also inverts `β`.

/-- The rules of the NLA rounds: 4 distinct challenges `γ` in each round. -/
def nlaForks : (n : ℕ) → (nlaRounds F E n).ForkRules
  | 0 => ()
  | n + 1 => (⟨4, (· ≠ ·)⟩, nlaForks n)

/-- The rules of the fork tree, one for each round of `rangeProtocol`. The number of challenges
in a round is one more than the degree of that challenge in the verifier's equations. -/
def rangeForks (P : CircuitParams) : (rangeProtocol F E P).ForkRules :=
  (⟨Nd P + 16, (· ≠ ·)⟩,                                     -- `α`
   ⟨P.nm + 1, fun ρ ρ' => ρ.val ^ 2 ≠ ρ'.val ^ 2⟩,            -- `ρ`
   ⟨1, (· ≠ ·)⟩,                                              -- `δ`
   ⟨2, (· ≠ ·)⟩,                                              -- `β`
   ⟨P.m * (P.nm + 8) + 1, (· ≠ ·)⟩,                           -- `λ`
   ⟨13, (· ≠ ·)⟩,                                             -- `τ`
   nlaForks F E (numNlaRounds P))                             -- `γ_j`
-- The degrees: `α` is `Nd + 15` (the reciprocal identity). `ρ` is `nm` in `μ = ρ²`. `δ` is not
-- forked. `β` is 1. `λ` is `m(nm + 8)`. `τ` has 13 Laurent coefficients, the powers -2 to 10.
-- Each NLA round fits a parabola in `γ` through 3 openings and checks it with the 4th.

/-- A fork tree of the range proof. -/
abbrev RangeForkTree (P : CircuitParams) : Type :=
  (rangeProtocol F E P).ForkTree (rangeForks F E P) (F × List F)

end Protocol


/-! ## The transcript and the hash -/

/-- The NLA part of a transcript: the commitments `(X, R)` and the challenges `γ`. -/
def nlaParts : {n : ℕ} → (nlaRounds F E n).Transcript → List (E × E) × List F
  | 0, () => ([], [])
  | _ + 1, (xr, γ, rest) =>
      let parts := nlaParts rest
      (xr :: parts.1, γ :: parts.2)

/-- Whether a transcript entry is a query for a challenge. -/
def isChallenge : Entry F E → Bool
  | .challenge _ => true
  | _ => false

/-- The hash that answers the `k`-th query for a challenge (from 0) with `answers[k]`. After the
end of the list, it answers 1. -/
def hashOf (answers : List F) (log : List (Entry F E)) : F :=
  answers.getD (log.countP isChallenge - 1) 1

/-! ## The relation -/

variable (F) in
/-- The field is large enough: its characteristic is 0 or larger than `Nd + 16`. So no integer
from 1 to `Nd + 16` is 0 in `F`. Soundness needs the integers up to `Nd`. The honest prover
needs the integers up to 16, because it uses `α = 1` before it gets `α`. -/
def LargeChar (P : CircuitParams) : Prop :=
  ringChar F = 0 ∨ Nd P + 16 < ringChar F

variable (F) in
/-- A linear combination of the generators: a scalar for `g`, a scalar for each `h_vec[i]`, and
a scalar for each `g_vec[j]`. -/
abbrev Combination (P : CircuitParams) : Type := F × (Fin H_LEN → F) × (Fin P.nm → F)

variable (F E) in
/-- The statement for the circuit sizes `P`: the range, the input commitments, the generators and
the domain separator. -/
structure RangeStatement (P : CircuitParams) where
  range : Range
  /-- The input commitments `V_i`. -/
  V : Fin P.m → E
  /-- The generator `g`. It is the value base `H` of the commitments. -/
  g : E
  /-- The generators `h_vec`. `hVec 0` is the blinding base `G` of the commitments. -/
  hVec : Fin H_LEN → E
  /-- The generators `g_vec`. -/
  gVec : Fin P.nm → E
  /-- The domain separator of the hash. -/
  dst : List ℕ
  /-- `P` are the circuit sizes that Rust computes for the range and the batch size. -/
  hParams : CircuitParams.new range P.m = .ok P
  largeChar : LargeChar F P

namespace RangeStatement

variable {P : CircuitParams} (x : RangeStatement F E P)

/-- The value base `H = g`. -/
abbrev H : E := x.g

/-- The blinding base `G = h_vec[0]`. -/
abbrev G : E := x.hVec ⟨0, by decide⟩

/-- The generators as the Rust type. -/
def gens : Generators E := ⟨x.g, List.ofFn x.hVec, List.ofFn x.gVec⟩

/-- The Rust function that derives the generators. Rust calls it only at `nm`. -/
def generators : ℕ → Result (Generators E) := fun _ => .ok x.gens

/-- The input commitments as the Rust type. -/
def commitments : List (PedersenCommitment E) := List.ofFn fun i => ⟨x.V i⟩

end RangeStatement

/-- `o` is a link between the generators: a nonzero combination of them that is the zero
point. -/
def IsGeneratorLink {P : CircuitParams} (x : RangeStatement F E P) (o : Combination F P) :
    Prop :=
  let (s, h, n) := o
  o ≠ 0 ∧ s • x.g + ∑ i, h i • x.hVec i + ∑ j, n j • x.gVec j = 0

variable (F) in
/-- The witness: the value and the blinding of each commitment `i`, and a candidate link between
the generators. -/
structure RangeWitness (P : CircuitParams) where
  value : ℕ → ℕ
  blinding : ℕ → F
  link : Combination F P

/-- Each commitment `V_i` is `v i • H + s i • G`, with `v i < 2^bits`. -/
def OpensInRange {P : CircuitParams} (x : RangeStatement F E P) (v : ℕ → ℕ) (s : ℕ → F) : Prop :=
  ∀ i : Fin P.m, v i < 2 ^ x.range.bits ∧ x.V i = (v i : F) • x.H + s i • x.G

/-! ## The verifier -/

/-- The verifier: build the Rust proof from the transcript and the response `(l, n)`. Then run
`verify_batch` with the hash `hashOf answers`. Rust asks for `λ, β, δ`; `rangeProtocol` has them
in the reverse order. The extractor may choose this order, because the prover sends nothing
between them. -/
def rangeVerify {P : CircuitParams} (x : RangeStatement F E P) :
    (rangeProtocol F E P).Transcript → F × List F → Prop
  | ((cL, cO), α, cR, ρ, (), δ, (), β, (), lam, cS, τ, nla), (l, n) =>
      let (rounds, γs) := nlaParts nla
      let proof : Bppp.RangeProof F E :=
        ⟨{ c_l := cL, c_o := cO, c_r := cR, c_s := cS, nl_proof := ⟨rounds, l, n⟩ }⟩
      let answers := [α.val, ρ.val, lam, β.val, δ.val, τ.val] ++ γs
      proof.verify_batch (hashOf answers) x.generators x.commitments x.range x.dst = .ok ()

section System

variable (F E)

/-- The relation of the range proof, for the circuit sizes `P`. -/
def rangeRelation (P : CircuitParams) : Relation where
  StatementType := RangeStatement F E P
  WitnessType := RangeWitness F P
  Rel x w := OpensInRange x w.value w.blinding
  RelaxedRel x w := (OpensInRange x w.value w.blinding) ∨ (IsGeneratorLink x w.link)

/-- The range proof as a proof system, for the circuit sizes `P`. The response is `(l, n)`. -/
def rangeSystem (P : CircuitParams) : ProofSystem (rangeRelation F E P) where
  roundTypes := rangeProtocol F E P
  ResponseType := F × List F
  Verify x := rangeVerify x

end System


/-! ## Soundness -/

/-- Soundness: for all circuit sizes `P`, `extract P` computes a witness from every fork tree in
which `verify_batch` accepts every path. -/
def RangeSoundness (extract : (P : CircuitParams) → RangeStatement F E P →
    RangeForkTree F E P → RangeWitness F P) : Prop :=
  ∀ P, (rangeSystem F E P).SpecialSound (rangeForks F E P) (extract P)


/-! ## Completeness -/

section Completeness

variable {P : CircuitParams}

/-- The Rust prover `prove_batch` with the hash `hashOf answers`, on the values and the
blindings of `w`. If Rust fails, the result is a proof of zeros. -/
def proveWith (x : RangeStatement F E P) (w : RangeWitness F P) (coins : Circuit.Randomness F)
    (answers : List F) : Circuit.CircuitProof F E :=
  let values := (List.range P.m).map w.value
  let blindings := (List.range P.m).map w.blinding
  match Bppp.RangeProof.prove_batch (hashOf answers) x.generators x.G x.H values blindings x.range
      x.dst coins with
  | .ok rp => rp.proof
  | .error _ => { c_l := 0, c_o := 0, c_r := 0, c_s := 0, nl_proof := ⟨[], 0, []⟩ }

/-- The NLA rounds of the honest prover. `proof γs` is the Rust NLA proof after the challenges
`γs`. Each round sends the next pair `(X, R)` of it. At the end, it sends `(l, n)`. -/
def nlaStrategy (proof : List F → NormLinearProof F E) :
    (n : ℕ) → List F → (nlaRounds F E n).Strategy (F × List F)
  | 0, γs => ((proof γs).l_final, (proof γs).n_final)
  | n + 1, γs =>
      ((proof γs).rounds.getD γs.length (0, 0), fun γ => nlaStrategy proof n (γs ++ [γ]))

/-- The honest prover. Each message is a part of the Rust proof that `proveWith` computes with
the challenges so far. Rust computes this part before it asks for the later challenges. -/
def honestStrategy (x : RangeStatement F E P) (w : RangeWitness F P)
    (coins : Circuit.Randomness F) : (rangeProtocol F E P).Strategy (F × List F) :=
  let proof := proveWith x w coins
  (((proof []).c_l, (proof []).c_o), fun α =>
    ((proof [α.val]).c_r, fun ρ =>
      ((), fun δ =>
        ((), fun β =>
          ((), fun lam =>
            let five := [α.val, ρ.val, lam, β.val, δ.val]
            ((proof five).c_s, fun τ =>
              nlaStrategy (fun γs => (proof (five ++ [τ.val] ++ γs)).nl_proof)
                (numNlaRounds P) []))))))

variable (F E)

/-- The honest prover of the range proof. Its coins are the random draws of the Rust prover. -/
def honest (P : CircuitParams) : (rangeSystem F E P).HonestProver where
  CoinsType := Circuit.Randomness F
  prove := honestStrategy

/-- Completeness: for all circuit sizes `P`, the verifier accepts every run of the honest prover
on a witness in `OpensInRange`. -/
def RangeCompleteness : Prop :=
  ∀ P, (rangeSystem F E P).Complete (honest F E P)

end Completeness

end Audit.RangeProof
