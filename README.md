# bppp-lean

Lean 4 proof that the batched Bulletproofs++ range proof in `fastcrypto::bulletproofspp` is
complete: `RangeProof::verify_batch` accepts what `RangeProof::prove_batch` outputs.

## Layout

| Files | Contents |
| --- | --- |
| `Bppp/Fastcrypto.lean`, `Crs.lean`, `Util.lean`, `Transcript.lean`, `Laurent.lean`, `Constraints.lean`, `NormLinear.lean`, `Circuit.lean`, `RangeProof.lean` | The Rust code, one file per module, with the same names |
| `Bppp/Proofs/` | Lemmas about each module, and completeness of `norm_linear` and `circuit` |
| `Bppp/Spec/` | The protocol of [ePrint 2026/2648](https://eprint.iacr.org/2026/2648) §5, used inside the proofs |
| `Bppp/Correctness.lean` | The main theorem |

## The theorem

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

## Soundness (in progress)

`NormLinear.verify_extract`: special soundness of `norm_linear::verify`. Take a tree of
transcripts with four distinct challenges per round, each of whose paths is an accepting run of
`verify` on its own transcript, with the challenges that transcript derives. Then the commitment
opens to a witness of the relation (19), or the generators satisfy a nontrivial linear relation.
A fork is two transcripts whose oracles agree up to one challenge. The norm vector's length must
be divisible by `2^rounds`, as it is in `norm_linear.rs`.

It combines `NormLinear.verify_accepts` (an accepting run is an accepting transcript of the
interactive argument) with `Spec.NormLinear.extract` (special soundness of that argument).

`Spec.extract_tau`: the `τ` level of the circuit extractor (§5.3). From openings of `C(τ)` at 13
distinct `τ`, either `C_S`, `C_O`, `C_L`, `C_R`, `V̂` open to an opening with `f(T) ≡ 0`, or the
generators satisfy a nontrivial linear relation.

`Spec.extract_lam`: the `λ` level. From `M(nm+8)+1` distinct `λ`, each with openings of `C_O`,
`C_L`, `C_R` and `V̂ = 2Σ λ^i V_i` whose error polynomial vanishes, either every `V_i` opens in
the `(g, H_0)`-plane, set membership and the value links of inputs `i ≥ 1` hold, and the degree-0
residue vanishes, or the generators satisfy a nontrivial linear relation. It assumes `2 ≠ 0`
and a nonempty batch.

`Spec.extract_beta`: the `β` level. From two distinct `β`, with the openings of `C_O`, `C_L`,
`C_R` and `V_0` the `λ` level returns, either (36) holds or the generators satisfy a nontrivial
linear relation.

`Spec.extract_rho`: the `ρ` level. From `nm + 1` distinct `μ = ρ²`, each satisfying (36) with
the same openings of `C_L`, `C_R` and `V_0`, either the first value link and the Hadamard rows
`(α + n_{L,k})n_{R,k} = 1` (`k < N_d`), `n_{L,k}n_{R,k} = 0` (`k ≥ N_d`) hold, or the generators
satisfy a nontrivial linear relation.

`Spec.extract_alpha`: the `α` level. From `N_d + 16` distinct `α`, none in `{-15, ..., 0}`, each
with set membership and the Hadamard rows for the same openings of `C_O`, `C_L`, either every
digit `n_{L,k}` (`k < N_d`) is in `{0, ..., 15}`, or the generators satisfy a nontrivial linear
relation. It assumes no `m = 1, ..., N_d` is zero in the field.

The levels are in `Spec/CircuitSoundness.lean` (`τ`) and `Spec/RowSoundness.lean` (the rest).

`Spec.circuit_extract` composes them (output (38)). Take a tree that forks `α`, `μ`, `β`, `λ`,
`τ` with distinct values at every fork and challenges in the good set, with `C_O`, `C_L` and the
inputs fixed, `C_R` depending on `α` and `C_S` on the path down to `λ`. If every leaf opens
`C(τ)` to a norm-linear witness, every input is `V_i = v_i g + s_i H_0` with `v_i < 16^D`, or the
generators satisfy a nontrivial linear relation. It assumes `2 ≠ 0`, that no `m = 1, ..., N_d`
is zero in the field, and a nonempty batch.

Not yet covered: linking `circuit_extract` to `circuit::verify` (as `verify_extract` does for the
norm-linear argument), zero-knowledge, and the probabilistic steps (tree extraction,
Fiat–Shamir).

## Build

```bash
lake exe cache get && lake build
```
