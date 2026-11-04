# bppp-lean

Lean 4 proofs about the batched Bulletproofs++ range proof in `fastcrypto::bulletproofspp`:
completeness, special soundness, honest-verifier zero-knowledge and Fiat–Shamir hygiene. The Rust
code is mirrored function by function, and the theorems are about that mirror. The protocol is
[ePrint 2026/2648](https://eprint.iacr.org/2026/2648) §5.

## How to check it

Six declarations are `theorem`s, and they are the results to check. Everything else is a `lemma`
used to prove them, so a reviewer needs to read the six statements, the definitions they mention
and the mirror of the Rust code. Each theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound` (`#print axioms`).

```bash
lake exe cache get && lake build
```

```bash
grep -rn "^theorem" Bppp/
```

It builds with Lean 4.35, Mathlib and VCVio. The Mathlib cache covers Mathlib only, so the first
build also compiles the VCVio modules the zero-knowledge proof imports.

Most results assume that `Generators::new` returns `H_LEN` and `nm` generators, with
`g = pedersen::H` and `h_vec[0] = pedersen::G`. This is called *generators of the right shape*
below.

## Completeness

`RangeProof.completeness` (`Correctness.lean`): for values in `range` and blindings of the same
length, `prove_batch` returns a proof that `verify_batch` accepts for the Pedersen commitments to
the values, for every choice of the prover's random draws. It assumes:

- generators of the right shape;
- the transcript hash never outputs `-j` for `j < 16`, so no inversion fails.

## Special soundness

`RangeProof.verify_extract` (`Soundness.lean`): take a tree of accepting runs of `verify_batch`
on fixed commitments, `range` and `dst`, each with its own transcript hash. Then every
commitment is `PedersenCommitment::new` of a value in `range`, or the generators satisfy a
nontrivial linear relation. The challenges at every fork are distinct, `C_O` and `C_L` are the
same throughout, `C_R` depends only on `α`, and `C_S` only on the path down to `λ`. It assumes:

- generators of the right shape, and `2^rounds` divides `nm`;
- `α ∉ {0, -1, ..., -15}` and `ρ, δ, τ ≠ 0`;
- `2 ≠ 0`, and no `m = 1, ..., N_d` is zero in the field.

The proof follows §5.3 of the paper, from the innermost level outward:

| Level | Branches | Lemma | Outcome |
| --- | --- | --- | --- |
| `γ` | 4 per round | `NormLinear.verify_extract` | an opening of `C(τ)` satisfying (27) |
| `τ` | 13 | `Spec.extract_tau` | openings of `C_S, C_O, C_L, C_R, V̂` with `f(T) ≡ 0` |
| `λ` | `M(nm+8)+1` | `Spec.extract_lam` | inputs in the `(g, H_0)`-plane, set membership, value links `i ≥ 1` |
| `β` | 2 | `Spec.extract_beta` | the residue (36) |
| `ρ` | `nm+1`, distinct `ρ²` | `Spec.extract_rho` | the first value link and the Hadamard rows |
| `α` | `N_d+16` | `Spec.extract_alpha` | every digit in `{0, ..., 15}` |

`Spec.circuit_extract` composes the levels from `τ` outward, `Circuit.leaf_extract` links each
`τ` to `norm_linear::verify` through `Circuit.verify_run`, and `Circuit.verify_extract` is the
result for `circuit::verify`.

## Zero-knowledge

`RangeProof.zero_knowledge` (`ZeroKnowledge.lean`) is Theorem 1 of the paper, stated with
[VCVio](https://github.com/Verified-zkEVM/VCV-io)'s `ChallengeVerifyProtocol.HVZK`. `protocol`
casts `range_proof` for batches of `m` values as a VCVio protocol:

- the statement is the commitments, and the witness the values and blindings, related by
  `commitments` and range membership;
- the honest verifier's challenges `(α, ρ, λ, β, δ, τ, γ_1, ..., γ_r)` are one uniform draw
  (`Chal`), since they don't depend on the prover's messages, and `chalOracle` is the transcript
  hash that returns them in order;
- the response is `prove_batch` under uniform masks `n_S`, `ℓ_S` and blindings of `C_O`, `C_L`,
  `C_R`.

The theorem says the real transcripts are within total variation distance `22 / |F|` of
`simTranscript`, which sees only the commitments, `range`, `dst` and the generators. The `22` is
the number of bad challenge values (`pr_bad_le`): 16 for `α`, one each for `ρ`, `δ`, `τ`, and
three for `β` (`β = 0` and the two roots of condition (32), `β² = h_0 (h_1 + λ^{g_1})`). For good
challenges the distributions are equal (`zero_knowledge_at`). It assumes:

- a finite field with a uniform sampler (`SampleableType`), and `m ≥ 1`;
- generators of the right shape, all multiples of `g`, as in a prime-order group:
  `h_vec[j] = h_j g`, with `h_0 ≠ 0`.

The proof (`Spec/ZeroKnowledge.lean`) differs from the paper's pivot table but needs the same
condition. With the masks fixed, the solved `r_S` is affine in the other 15 blindings, so they map
to `ℓ(τ)_0, ..., ℓ(τ)_6` and the discrete logs of `C_O`, `C_L`, `C_R` by an affine map
(`linRow`). `linInv` is an explicit right inverse under the conditions above, and the masks give
`n(τ)`, `ℓ(τ)_7` bijectively, so the view is uniform (`map_realY`). The simulator solves `C_S`
from (25) and runs the norm-linear prover, as the real prover does (`Circuit.prove_view`).

## Fiat–Shamir hygiene

`Proofs/Hygiene.lean`: `verify_batch` derives each challenge from an unambiguous encoding of the
statement and every prover message before it, and from nothing else.

- `RangeProof.verify_batch_local`: two transcript hashes that agree on `Circuit.challengeLogs`
  give the same result, accepting or rejecting. These are the logs at `α`, `ρ`, `λ`, `β`, `δ`, `τ`
  and each round's `γ`. Each is the verifier's log up to that challenge, starting with the
  statement (`dst`, `n_bits`, `m`, every `V_i`) and containing every prover message before it.
- `RangeProof.challenge_decodes`: if two challenge logs, of any statements and proofs, absorb
  the same labels and bytes, they are the same log of the same statement. Points are under any
  injective encoding and are not tagged as points, as in Rust: the labels alone tell entries apart.
  It assumes `n_bits` and `m` fit a `u64`.
- `RangeProof.challengeLogs_nodup`: within a run, no two challenges are drawn at the same log.

## The model

Checking that the mirror matches the Rust code is the part Lean cannot do.

| Files | Contents |
| --- | --- |
| `Bppp/Fastcrypto.lean`, `Crs.lean`, `Util.lean`, `Transcript.lean`, `Laurent.lean`, `Constraints.lean`, `NormLinear.lean`, `Circuit.lean`, `RangeProof.lean` | The Rust code, one file per module, with the same names |
| `Bppp/Proofs/` | Lemmas about each module, and completeness and special soundness of `norm_linear` and `circuit` |
| `Bppp/Spec/` | The protocol of the paper, used inside the proofs |
| `Bppp/Correctness.lean`, `Bppp/Soundness.lean`, `Bppp/ZeroKnowledge.lean` | Completeness, special soundness and zero-knowledge of `range_proof` |

- Scalars are any field and points any module over it. `Vec` is `List`, `FastCryptoResult` is
  `Except`, and `&mut BpppTranscript` is a state monad.
- The Merlin transcript is a log of labelled entries and an arbitrary function from logs to
  challenges. `Transcript::new` absorbs its label under `"dom-sep"`, and a `u64` is 8
  little-endian bytes, as in Merlin.
- The prover's random draws are an input.
- Not modelled: `Generators::new` (hash-to-curve), the MSM precomputation tables, serialization,
  and test-only code.

## Not covered

These are standard steps, cited rather than proved:

- from special soundness to knowledge soundness of the non-interactive proof: tree extraction,
  and the Fiat–Shamir transform in the random-oracle model;
- zero-knowledge of the non-interactive proof in the random-oracle model, by programming the
  oracle with the simulator's challenges.

These are assumed:

- Merlin frames `(label, message)` pairs unambiguously, and Ristretto points have a canonical
  encoding;
- `Generators::new` returns generators with no known linear relation. They are not absorbed into
  the transcript, because `range` and `m` determine them.

Hygiene of the prover's transcript is not needed: by completeness it derives the same challenges
as the verifier on honest runs.
