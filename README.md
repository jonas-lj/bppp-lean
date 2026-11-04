# bppp-lean

Lean 4 proofs about the batched Bulletproofs++ range proof in `fastcrypto::bulletproofspp`: it
is complete (`RangeProof::verify_batch` accepts what `RangeProof::prove_batch` outputs) and
special sound (a tree of accepting `verify_batch` runs extracts an opening of every commitment to
a value in range), and honest-verifier zero-knowledge.

## The results

Six declarations are `theorem`s, and they are the results to check; everything else is a
`lemma` used to prove them:

- `RangeProof.completeness` (`Correctness.lean`)
- `RangeProof.verify_extract` (`Soundness.lean`)
- `RangeProof.zero_knowledge` (`ZeroKnowledge.lean`)
- `RangeProof.verify_batch_local`, `RangeProof.challenge_decodes` and
  `RangeProof.challengeLogs_nodup` (`Proofs/Hygiene.lean`)

```bash
grep -rn "^theorem" Bppp/
```

## Layout

| Files | Contents |
| --- | --- |
| `Bppp/Fastcrypto.lean`, `Crs.lean`, `Util.lean`, `Transcript.lean`, `Laurent.lean`, `Constraints.lean`, `NormLinear.lean`, `Circuit.lean`, `RangeProof.lean` | The Rust code, one file per module, with the same names |
| `Bppp/Proofs/` | Lemmas about each module, and completeness and special soundness of `norm_linear` and `circuit` |
| `Bppp/Spec/` | The protocol of [ePrint 2026/2648](https://eprint.iacr.org/2026/2648) §5, used inside the proofs |
| `Bppp/Correctness.lean`, `Bppp/Soundness.lean`, `Bppp/ZeroKnowledge.lean` | Completeness, special soundness and zero-knowledge of `range_proof` |

## Completeness

`RangeProof.completeness`: for values in `range` and blindings of the same length,
`prove_batch` returns a proof that `verify_batch` accepts for the Pedersen commitments to the
values. It assumes:

- `Generators::new` returns `H_LEN` and `nm` generators, with `g = pedersen::H` and
  `h_vec[0] = pedersen::G`;
- the transcript hash never outputs `-j` for `j < 16`, so no inversion fails.

It depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## The model

- Scalars are any field and points any module over it. `Vec` is `List`, `FastCryptoResult` is
  `Except`, and `&mut BpppTranscript` is a state monad.
- The Merlin transcript is a log of absorbed entries and an arbitrary function from logs to
  challenges.
- The prover's random draws are an input.
- Not modelled: `Generators::new` (hash-to-curve), the MSM precomputation tables, serialization,
  and test-only code.

## Special soundness

`RangeProof.verify_extract` (`Soundness.lean`): take a tree of accepting runs of
`verify_batch` on fixed commitments, `range` and `dst`, each with its own transcript hash and
with the challenges that transcript derives. It forks `α` (`N_d + 16` values), `ρ` (`nm + 1`,
with distinct squares), `β` (2), `λ` (`M(nm+8)+1`), `τ` (13) and then the norm-linear `γ` (4 per
round), with distinct values at every fork. `C_O` and `C_L` are the same throughout, `C_R`
depends only on `α` and `C_S` only on the path down to `λ`. Then every commitment is
`PedersenCommitment::new` of a value in `range`, or the generators satisfy a nontrivial linear
relation. It assumes:

- `Generators::new` returns `H_LEN` and `nm` generators, with `g = pedersen::H` and
  `h_vec[0] = pedersen::G`, and `2^rounds` divides `nm`;
- the challenges are in the good set: `α ∉ {0, -1, ..., -15}` and `ρ, δ, τ ≠ 0`;
- `2 ≠ 0`, and no `m = 1, ..., N_d` is zero in the field.

It depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. The proof follows
§5.3 of the paper, from the innermost level outward:

| Level | Lemma | Outcome |
| --- | --- | --- |
| `γ` | `NormLinear.verify_extract` | an opening of `C(τ)` satisfying (27) |
| `τ` | `Spec.extract_tau` | openings of `C_S, C_O, C_L, C_R, V̂` with `f(T) ≡ 0` |
| `λ` | `Spec.extract_lam` | inputs in the `(g, H_0)`-plane, set membership, value links `i ≥ 1` |
| `β` | `Spec.extract_beta` | the residue (36) |
| `ρ` | `Spec.extract_rho` | the first value link and the Hadamard rows |
| `α` | `Spec.extract_alpha` | every digit in `{0, ..., 15}` |

`Spec.circuit_extract` composes the levels from `τ` outward, `Circuit.leaf_extract` links each
`τ` to `norm_linear::verify` through `Circuit.verify_run`, and `Circuit.verify_extract` is the
result for `circuit::verify`.

Not covered: the probabilistic steps from special soundness to knowledge soundness of the
non-interactive proof (tree extraction, Fiat–Shamir).

## Zero-knowledge

`RangeProof.zero_knowledge` (`ZeroKnowledge.lean`): against an honest verifier, whose challenges
depend only on which challenges came before, `prove_batch` with uniform masks `n_S`, `ℓ_S` and
blindings of `C_O`, `C_L`, `C_R` has the distribution of `simBatch`, which sees only the
commitments, `range`, `dst`, the generators and the challenges. It assumes:

- values in `range`, and generators of the right shape with `g = pedersen::H`,
  `h_vec[0] = pedersen::G`, all in the span of `g` (a prime-order group): `h_vec[j] = h_j g`;
- `α ∉ {0, -1, ..., -15}`, `ρ, β, δ, τ ≠ 0`, `h_0 ≠ 0` and `β² ≠ h_0 (h_1 + λ^{g_1})`, the
  condition of (32) in the paper.

The proof (`Spec/ZeroKnowledge.lean`) differs from the paper's pivots: with the masks fixed, the
solved `r_S` is affine in the other 15 blindings, so they map to `ℓ(τ)_0, ..., ℓ(τ)_6` and the
discrete logs of `C_O`, `C_L`, `C_R` by an affine map (`linRow`). `linInv` is an explicit right
inverse under the conditions above, and the masks give `n(τ)`, `ℓ(τ)_7` bijectively, so the view
is uniform (`map_realY`). The simulator then solves `C_S` from (25) and runs the norm-linear
prover, as the real prover does (`Circuit.prove_view`). Zero-knowledge of the non-interactive
proof in the random-oracle model is not covered.

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

The generators are not absorbed: they are determined by `range` and `m` through
`Generators::new`. Merlin's framing of `(label, message)` pairs and the canonical encoding of
Ristretto points are assumed. Only the verifier is covered; the prover's challenges agree with
it on honest runs by completeness.

## Build

```bash
lake exe cache get && lake build
```
