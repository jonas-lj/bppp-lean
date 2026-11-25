import Audit.RangeProof.Paper.Protocol

/-!
# The range-proof protocol: the honest prover

This file defines the honest prover of `Audit/RangeProof/Paper/Protocol.lean`. It is on the proof
side: the completeness theorem checks it, so it needs no review.

Why it exists:
- The completeness theorem needs a prover that makes the verifier accept.
- Soundness does not use it.

How it works:
1. The prover commits to the digits (`C_L`), the multiplicities (`C_O`) and the reciprocals
   (`C_R`), with the zeros of eq. 22 in the blindings.
2. It chooses the blinding of `C_S` (`openS`) so that the error polynomial `f(T)` (eq. 28) has
   no term other than `T³`.
3. It runs the honest NLA prover (`honestTranscript`) on the opening of `C(τ)` (eq. 26).

Assumptions:
- The blinding `r_{S,0}` (`openS`) follows the Rust code (`circuit.rs`, `solve_r_s`):
  `r_{S,0} = ⟨c_{ℓ,V}, h_S⟩ - f̄[T⁻¹]`. Eq. 31 as printed has the opposite sign on the `λ` terms.
  That sign is an error in the paper: solving `f(T)[T⁻¹] = 0` gives the Rust form.
- `openS` divides by `β`, but the verifier does not reject `β = 0`. The Rust prover fails when
  `β = 0`. So the completeness theorem assumes `β ≠ 0` and `v i < 2^b`.
-/

namespace Audit.RangeProtocol

open Audit.NLA LaurentPolynomial

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-! ## The honest prover: witness and openings (eq. 22) -/

section Prover

variable {P : Params}

variable (F P) in
/-- The prover's secret: the values `v i < 2^b` and the blindings `s i` of the inputs. -/
structure Witness where
  v : Fin P.M → ℕ
  s : Fin P.M → F

/-- The honest inputs `V i = v i • G + s i • H 0` (§5.1). -/
def honestInputs (key : Key E P) (w : Witness F P) : Fin P.M → E :=
  fun i => (w.v i : F) • key.G + w.s i • key.H 0

variable (F P) in
/-- The prover's random choices: the blindings of `C_O`, `C_L`, `C_R` (before the zeros of
eq. 22), and the masks `n_S`, `ℓ_S` of `C_S`. -/
structure Randomness where
  rO : Fin 8 → F
  rL : Fin 8 → F
  rR : Fin 8 → F
  nS : Fin P.nm → F
  ℓS : F

/-- `r` with the slots in `zeros` set to 0. -/
def withZeros (zeros : List ℕ) (r : Fin 8 → F) : Fin 8 → F :=
  fun j => if j.val ∈ zeros then 0 else r j

/-- The opening of a commitment `C_X = r_{X,0} G + ⟨r_{X,1:7} ‖ ℓ_X, H⟩ + ⟨n_X, Gs⟩` (eq. 22), as
`(σ, H-coordinates, Gs-coordinates)`. -/
def opening (r : Fin 8 → F) (ℓX : F) (n : Fin P.nm → F) : Opening F 8 P.nm where
  σ := r 0
  ℓ j := if h : j.val < 7 then r ⟨j.val + 1, by omega⟩ else ℓX
  n := n

/-- The commitment of an opening: `σ G + ⟨ℓ, H⟩ + ⟨n, Gs⟩`. -/
def Key.commit (key : Key E P) (o : Opening F 8 P.nm) : E :=
  o.σ • key.G + msm o.ℓ key.H + msm o.n key.Gs

/-- The digit in slot `k = D·i + t`: digit `t` of value `i` in base 16. Slots `k ≥ Nd` hold 0. -/
def digit (w : Witness F P) (k : ℕ) : ℕ :=
  if h : k < P.Nd then
    w.v ⟨k / P.D, Nat.div_lt_of_lt_mul (by simpa [Params.Nd, mul_comm] using h)⟩ /
      16 ^ (k % P.D) % 16
  else 0

/-- The multiplicity `m_j`: the number of digit slots that hold `j`. -/
def mult (w : Witness F P) (j : ℕ) : ℕ :=
  ((Finset.range P.Nd).filter fun k => digit w k = j).card

/-- `n_L`: the digits. -/
def nL (w : Witness F P) (k : Fin P.nm) : F := digit w k.val

/-- `n_O`: the multiplicities `m_1, …, m_15` in slots 0 to 14. `m_0` is implicit. -/
def nO (w : Witness F P) (k : Fin P.nm) : F := if k.val < 15 then mult w (k.val + 1) else 0

/-- `n_R`: the reciprocals `(α + d)⁻¹` of the digits. -/
def nR (w : Witness F P) (α : F) (k : Fin P.nm) : F :=
  if k.val < P.Nd then (α + digit w k.val)⁻¹ else 0

/-- The opening of `C_L`. The blindings of `C_L`, `C_O`, `C_R` get the zeros of eq. 22. -/
def openL (w : Witness F P) (rnd : Randomness F P) : Opening F 8 P.nm :=
  opening (withZeros [3, 6, 7] rnd.rL) 0 (nL w)

/-- The opening of `C_O`. -/
def openO (w : Witness F P) (rnd : Randomness F P) : Opening F 8 P.nm :=
  opening (withZeros [4, 7] rnd.rO) 0 (nO w)

/-- The opening of `C_R`. -/
def openR (w : Witness F P) (rnd : Randomness F P) (α : F) : Opening F 8 P.nm :=
  opening (withZeros [2, 5, 6, 7] rnd.rR) 0 (nR w α)

/-- The opening of `V̂ = 2 Σᵢ λ^i V i` for honest inputs: `G`-coordinate `2 Σᵢ λ^i v i`,
`H 0`-coordinate `2 Σᵢ λ^i s i`, and nothing else. -/
def openV (w : Witness F P) (lam : F) : Opening F 8 P.nm where
  σ := 2 * ∑ i, lam ^ i.val * w.v i
  ℓ j := if j.val = 0 then 2 * ∑ i, lam ^ i.val * w.s i else 0
  n := 0

/-! ## The honest prover: the blinding of `C_S` (eqs. 26 to 31) -/

/-- The monomial `x T^p`. -/
noncomputable def mono (p : ℤ) (x : F) : F[T;T⁻¹] := C x * T p

/-- An entry of a combined opening as a Laurent polynomial: the entries `xS`, `xO`, `xL`, `xR`,
`xV` of `C_S`, `C_O`, `C_L`, `C_R`, `V̂` at the powers of eq. 25. -/
noncomputable def place (δ xS xO xL xR xV : F) : F[T;T⁻¹] :=
  mono (-1) xS + mono 0 (δ * xO) + mono 1 xL + mono 2 xR + mono 3 xV

/-- `p_n(T)` (eq. 24). -/
noncomputable def pnPoly (ch : Challenges F) (k : Fin P.nm) : F[T;T⁻¹] :=
  mono 0 (cnV ch k) + mono 1 (cnR ch k) + mono 2 (cnL ch k) + mono 3 (ch.δ⁻¹ * cnO ch k)

/-- The weighted norm `‖v‖²_μ = Σ_k μ^(k+1) v_k²` of a vector of Laurent polynomials. -/
noncomputable def normPoly (μ : F) (v : Fin P.nm → F[T;T⁻¹]) : F[T;T⁻¹] :=
  ∑ k, C (μ ^ (k.val + 1)) * (v k * v k)

/-- `p_s(T) = ‖p_n(T)‖²_μ + 2(λ_al + μ_am) T³` (eq. 24). -/
noncomputable def psPoly (ch : Challenges F) : F[T;T⁻¹] :=
  normPoly ch.μ (pnPoly (P := P) ch) + mono 3 (2 * (lamAl (P := P) ch + muAm (P := P) ch))

/-- `c(T) = ĉ_r(T) + c_{ℓ,V}` (eq. 24). -/
noncomputable def cPoly (ch : Challenges F) (j : Fin 8) : F[T;T⁻¹] :=
  (if h : j.val < 7 then mono (cHatPower ⟨j.val, h⟩) ch.β else 0) + C (clV (P := P) ch j)

/-- The error polynomial `f(T) = σ(T) - ⟨c(T), ℓ(T)⟩ - ‖n(T)‖²_μ` (eqs. 26 and 28), for the
openings `oS`, `oO`, `oL`, `oR`, `oV` of `C_S`, `C_O`, `C_L`, `C_R`, `V̂`. -/
noncomputable def fPoly (ch : Challenges F) (oS oO oL oR oV : Opening F 8 P.nm) : F[T;T⁻¹] :=
  let σT := place ch.δ oS.σ oO.σ oL.σ oR.σ oV.σ + psPoly (P := P) ch
  let ℓT := fun j => place ch.δ (oS.ℓ j) (oO.ℓ j) (oL.ℓ j) (oR.ℓ j) (oV.ℓ j)
  let nT := fun k => place ch.δ (oS.n k) (oO.n k) (oL.n k) (oR.n k) (oV.n k) + pnPoly ch k
  σT - ∑ j, cPoly (P := P) ch j * ℓT j - normPoly ch.μ nT

/-- The opening of `C_S` (Rust `solve_r_s`). Let `f̄ = f(T)` with `r_S = 0` and `ℓ_S = 0`. The
`H`-coordinates `h` cancel the powers `T^(a - 1)` for each power `a` of `ĉ_r`, and `ℓ_S` stays
free. The `G`-coordinate `⟨c_{ℓ,V}, h⟩ - f̄[T⁻¹]` cancels `T⁻¹`. -/
noncomputable def openS (w : Witness F P) (rnd : Randomness F P) (ch : Challenges F) :
    Opening F 8 P.nm :=
  let fBar := fPoly ch (opening 0 0 rnd.nS) (openO w rnd) (openL w rnd) (openR w rnd ch.α)
    (openV w ch.lam)
  let h : Fin 8 → F := fun j =>
    if hj : j.val < 7 then fBar.coeff (cHatPower ⟨j.val, hj⟩ - 1) / ch.β else rnd.ℓS
  { σ := ip (clV (P := P) ch) h - fBar.coeff (-1), ℓ := h, n := rnd.nS }

/-! ## The honest prover: the run -/

/-- An entry of a combined opening at `τ`: `τ⁻¹ xS + δ xO + τ xL + τ² xR + τ³ xV` (eq. 25). -/
def placeAt (ch : Challenges F) (xS xO xL xR xV : F) : F :=
  ch.τ⁻¹ * xS + ch.δ * xO + ch.τ * xL + ch.τ ^ 2 * xR + ch.τ ^ 3 * xV

/-- The honest run: the commitments, then the honest NLA prover (`honestTranscript`) on the
opening `(ℓ(τ), n(τ))` of `C(τ)` (eq. 26). The NLA challenges are `γs`. -/
noncomputable def honestRun (key : Key E P) (w : Witness F P) (rnd : Randomness F P)
    (ch : Challenges F) (γs : ℕ → F) (hρ : ch.ρ ≠ 0) : Run F E P :=
  let oS := openS w rnd ch
  let oO := openO w rnd
  let oL := openL w rnd
  let oR := openR w rnd ch.α
  let oV := openV w ch.lam
  let msgs : Messages E :=
    { cL := key.commit oL, cO := key.commit oO, cR := key.commit oR, cS := key.commit oS }
  let nlaWit : NLA.Witness F 8 P.nm :=
    { ℓ := fun j => placeAt ch (oS.ℓ j) (oO.ℓ j) (oL.ℓ j) (oR.ℓ j) (oV.ℓ j)
      n := fun k => placeAt ch (oS.n k) (oO.n k) (oL.n k) (oR.n k) (oV.n k) + pn ch k }
  { msgs := msgs, ch := ch,
    nla := honestTranscript (nlaInstance key (honestInputs key w) msgs ch hρ) nlaWit γs }

end Prover

end Audit.RangeProtocol
