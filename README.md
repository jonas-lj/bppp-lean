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

Not yet covered: the `λ`, `β`, `ρ`, `α` levels of the extractor, zero-knowledge, and the
probabilistic steps (tree extraction, Fiat–Shamir).

## Build

```bash
lake exe cache get && lake build
```
