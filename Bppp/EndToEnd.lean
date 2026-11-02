import Bppp.Commitment
import Bppp.Completeness
import Bppp.NormLinearCompleteness

/-!
# End-to-end completeness

The verifier's combined commitment `C(τ)` (25), formed from the honest prover's messages and the
inputs `V_i`, is the commitment to the honest opening `(σ(τ), ℓ(τ), n(τ))` (`combined_honest`).
Together with the circuit's completeness this gives the norm-linear relation (19) on `C(τ)`, and
the completeness of the norm-linear argument then gives acceptance (`end_to_end`).
-/

open Finset LaurentPolynomial

namespace Bppp

variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
variable (P : Params) (g : E) (H G : ℕ → E) (ch : Challenges F) (τ : Fˣ)

theorem evalAt_mono (p : ℤ) (x : F) : evalAt τ (mono p x) = x * (τ : F) ^ p := by
  simp [evalAt, mono, eval₂_C_mul_T, Units.val_zpow_eq_zpow_val]

/-- `C(τ)` is linear in the openings of the commitments it combines. -/
theorem combined_commit (σS σO σL σR σV : F) (ℓS ℓO ℓL ℓR ℓV nS nO nL nR nV : ℕ → F) :
    combined P g G ch τ (commit P g H G σS ℓS nS) (commit P g H G σO ℓO nO)
      (commit P g H G σL ℓL nL) (commit P g H G σR ℓR nR) (commit P g H G σV ℓV nV) =
    commit P g H G
      (evalAt τ (ps P ch) + (τ : F) ^ (-1 : ℤ) * σS + ch.δ * σO + (τ : F) * σL +
        (τ : F) ^ 2 * σR + (τ : F) ^ 3 * σV)
      (fun s => (τ : F) ^ (-1 : ℤ) * ℓS s + ch.δ * ℓO s + (τ : F) * ℓL s + (τ : F) ^ 2 * ℓR s +
        (τ : F) ^ 3 * ℓV s)
      (fun k => evalAt τ (pn P ch k) + (τ : F) ^ (-1 : ℤ) * nS k + ch.δ * nO k +
        (τ : F) * nL k + (τ : F) ^ 2 * nR k + (τ : F) ^ 3 * nV k) := by
  simp only [combined, commit, NormLinear.msm, smul_add, smul_sum, smul_smul, add_smul,
    sum_add_distrib]
  module

variable (w : Opening F)

/-- `C(τ)` commits to the evaluated opening `(σ(τ), ℓ(τ), n(τ))` (26), for any opening. -/
theorem combined_eq (w : Opening F) :
    combined P g G ch τ (cS P g H G w) (cO P g H G w) (cL P g H G w) (cR P g H G w)
      (commit P g H G w.vhat (lin w.rV w.ℓV) w.nV) =
    commit P g H G (evalAt τ (σ P ch w)) (fun s => evalAt τ (ℓ ch w s))
      (fun k => evalAt τ (n P ch w k)) := by
  rw [cS, cO, cL, cR, combined_commit]
  congr 1
  case e_σ =>
    simp only [σ, map_add, evalAt_mono, zpow_ofNat]; ring
  case e_ℓ =>
    funext s; simp only [lin, ℓ]; split_ifs <;> simp only [map_add, evalAt_mono, zpow_ofNat] <;> ring
  case e_n =>
    funext k; simp only [n, pn, map_add, evalAt_mono, zpow_ofNat]; ring

variable (h : Honest F)

/-- The honest inputs aggregate to the commitment to the input coordinates of the opening:
`2Σ_i λ^i V_i = v̂g + r_{V,1}H_0`. -/
theorem vHat_honest (rS : ℕ → F) :
    vHat P ch (Honest.inputs (P := P) g H h) = commit P g H G (h.opening P ch rS).vhat
      (lin (h.opening P ch rS).rV (h.opening P ch rS).ℓV) (h.opening P ch rS).nV := by
  have h8 : NormLinear.msm 8 (lin (h.opening P ch rS).rV (h.opening P ch rS).ℓV) H =
      (2 * ∑ i ∈ range P.M, ch.lam ^ i * h.s i) • H 0 := by
    simp [NormLinear.msm, lin, Honest.opening, sum_range_succ]
  rw [commit, h8]
  simp only [vHat, Honest.inputs, Honest.opening, NormLinear.msm, zero_smul, sum_const_zero,
    add_zero, smul_add, sum_add_distrib, smul_sum, smul_smul, mul_sum, sum_smul]

/-- **End-to-end completeness.** For an honest prover with blinding in the zero pattern (22) and
the solved `r_S`, the verifier's `C(τ)`, formed from the messages and the inputs
`V_i = v_i g + s_i H_0`, satisfies the norm-linear relation (19) with the honest opening, so the
verifier accepts after any number of rounds `γs` of the norm-linear argument. -/
theorem end_to_end (hα : ∀ j : ℕ, j < 16 → ch.α + j ≠ 0) (hβ : ch.β ≠ 0) (hδ : ch.δ ≠ 0)
    (hd : ∀ i < P.M, ∀ t < P.D, h.d i t < 16) (hz : h.ZeroPattern) (ρ : F) (hρ : ρ ≠ 0)
    (hμ : ch.μ = ρ ^ 2) (γs : List F) :
    let w := h.opening P ch (h.rS P ch)
    let x : NormLinear.Instance F E :=
      { C := combined P g G ch τ (cS P g H G w) (cO P g H G w) (cL P g H G w) (cR P g H G w)
          (vHat P ch (Honest.inputs (P := P) g H h))
        c := fun s => evalAt τ (c P ch s)
        H := H
        G := G
        Lℓ := 8
        Ln := P.nm
        ρ := ρ
        μ := ch.μ }
    let o : NormLinear.Witness F :=
      { ℓ := fun s => evalAt τ (ℓ ch w s), n := fun k => evalAt τ (n P ch w k) }
    NormLinear.Rel g (NormLinear.run g γs x o).1 (NormLinear.run g γs x o).2 := by
  intro w x o
  have hμ0 : ch.μ ≠ 0 := by rw [hμ]; exact pow_ne_zero 2 hρ
  refine NormLinear.completeness g x o γs hρ hμ ?_
  have hrel := norm_linear_relation P ch h hα hβ hδ hμ0 hd hz τ
  simp only [NormLinear.Rel, x, o]
  rw [vHat_honest P g H G ch h, combined_eq, commit]
  congr 3

end Bppp
