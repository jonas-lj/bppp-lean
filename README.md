# bppp-lean

Lean 4 proofs about the batched Bulletproofs++ range proof of
[ePrint 2026/2648](https://eprint.iacr.org/2026/2648) (§5), as implemented in
`fastcrypto::bulletproofspp`. Definitions follow the paper's notation and equation numbers.

| File | Contents |
| --- | --- |
| `Bppp/Laurent.lean` | Monomials, coefficients and supports of Mathlib's `F[T;T⁻¹]` |
| `Bppp/Protocol.lean` | Public data (23)–(24), openings (21)–(22), Laurent vectors (26), error polynomial (28) |
| `Bppp/Honest.lean` | The honest witness placement and the solved blinding `r_S` |
| `Bppp/Completeness.lean` | Completeness of the circuit: `f(T) ≡ 0`, hence (27) at every `τ` |
| `Bppp/NormLinear.lean` | The norm-linear argument (§4.9): relation (19), messages `X`, `R`, folds |
| `Bppp/NormLinearCompleteness.lean` | Completeness of the norm-linear argument |

## Proved

- `completeness`: for an honest witness with blinding in the zero pattern (22), the solved
  `r_S` makes `f(T) ≡ 0`, given `α + j ≠ 0` for `j < 16`, and `β`, `δ`, `μ` nonzero.
- `norm_linear_relation`: the same at every `τ ≠ 0`, `σ(τ) = ⟨c(τ), ℓ(τ)⟩ + ‖n(τ)‖²_μ`.
- `NormLinear.fold_rel`: one honest round, with zero padding to even length, maps an opening
  satisfying (19) to one satisfying (19) for the folded instance, given `ρ ≠ 0` and `μ = ρ²`.
- `NormLinear.completeness`: hence the verifier's final check passes after any number of rounds.
  The group is modelled as any `F`-module.

Not covered: that the verifier's `C(τ)` (25) is the commitment to the circuit's opening,
soundness, and zero-knowledge.

## Build

```bash
lake exe cache get && lake build
```
