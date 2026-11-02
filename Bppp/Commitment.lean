import Bppp.Honest
import Bppp.NormLinear

/-!
# Commitments and the combined commitment

The norm-linear commitments (22) and the combined commitment `C(τ)` (25) the verifier forms, over
any `F`-module `E` in place of the group, with generators `g` (the paper's `G`), `H_0, ..., H_7`
and `G_0, ..., G_{nm-1}`.
-/

open Finset LaurentPolynomial

namespace Bppp

variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
variable (P : Params) (g : E) (H G : ℕ → E)

/-- The norm-linear commitment `σg + ⟨ℓ, H⟩ + ⟨n, G⟩`, with `ℓ ∈ F⁸` and `n ∈ F^{nm}`. -/
def commit (σ : F) (ℓ n : ℕ → F) : E :=
  σ • g + NormLinear.msm 8 ℓ H + NormLinear.msm P.nm n G

/-- The `H`-coordinates `r_{X,1:7} ‖ ℓ_X` of a commitment (22). -/
def lin (r : ℕ → F) (ℓX : F) : ℕ → F := fun s => if s < 7 then r (s + 1) else ℓX

variable (w : Opening F)

/-- `C_S`, `C_O`, `C_L`, `C_R` (22) for the opening `w`; only `C_S` has a nonzero `ℓ_X`. -/
def cS : E := commit P g H G (w.rS 0) (lin w.rS w.ℓS) w.nS
def cO : E := commit P g H G (w.rO 0) (lin w.rO 0) w.nO
def cL : E := commit P g H G (w.rL 0) (lin w.rL 0) w.nL
def cR : E := commit P g H G (w.rR 0) (lin w.rR 0) w.nR

variable {P} in
/-- The inputs `V_i = v_i g + s_i H_0` of an honest prover. -/
def Honest.inputs (h : Honest F) (i : ℕ) : E := h.value P i • g + h.s i • H 0

variable (ch : Challenges F) (τ : Fˣ)

/-- Evaluation at `T = τ`. -/
noncomputable def evalAt : F[T;T⁻¹] →+* F := LaurentPolynomial.eval₂ (RingHom.id F) τ

/-- The combined commitment (25), `C(τ) = P(τ) + τ⁻¹C_S + δC_O + τC_L + τ²C_R + τ³V̂` with
`P(τ) = p_s(τ)g + ⟨p_n(τ), G⟩`, from public data and the messages alone. -/
noncomputable def combined (cS cO cL cR vHat : E) : E :=
  evalAt τ (ps P ch) • g + NormLinear.msm P.nm (fun k => evalAt τ (pn P ch k)) G +
    (τ : F) ^ (-1 : ℤ) • cS + ch.δ • cO + (τ : F) • cL + (τ : F) ^ 2 • cR + (τ : F) ^ 3 • vHat

/-- `V̂ = 2Σ_i λ^i V_i` (21). -/
noncomputable def vHat (V : ℕ → E) : E := (2 : F) • ∑ i ∈ range P.M, ch.lam ^ i • V i

end Bppp
