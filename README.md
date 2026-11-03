# bppp-lean

Lean 4 proofs about the batched Bulletproofs++ range proof in `fastcrypto::bulletproofspp`: it
is complete (`RangeProof::verify_batch` accepts what `RangeProof::prove_batch` outputs) and
special sound (a tree of accepting `verify_batch` runs extracts an opening of every commitment to
a value in range).

## Layout

| Files | Contents |
| --- | --- |
| `Bppp/Fastcrypto.lean`, `Crs.lean`, `Util.lean`, `Transcript.lean`, `Laurent.lean`, `Constraints.lean`, `NormLinear.lean`, `Circuit.lean`, `RangeProof.lean` | The Rust code, one file per module, with the same names |
| `Bppp/Proofs/` | Lemmas about each module, and completeness and special soundness of `norm_linear` and `circuit` |
| `Bppp/Spec/` | The protocol of [ePrint 2026/2648](https://eprint.iacr.org/2026/2648) §5, used inside the proofs |
| `Bppp/Correctness.lean`, `Bppp/Soundness.lean` | Completeness and special soundness of `range_proof` |

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

| Level | Theorem | Outcome |
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

Not covered: zero-knowledge, and the probabilistic steps from special soundness to knowledge
soundness of the non-interactive proof (tree extraction, Fiat–Shamir).

## Build

```bash
lake exe cache get && lake build
```
