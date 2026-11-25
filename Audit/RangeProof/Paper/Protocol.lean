import Audit.NLAFull.Legacy

/-!
# The range-proof protocol

This file defines the verifier of the batched range proof of ePrint 2026/2648, §5, from the paper.
The honest prover is in `Audit/RangeProof/Paper/Prover.lean`. Soundness does not use it.

Why it exists:
- The soundness and completeness statements need a protocol that a reviewer can read and check
  against the paper.
- It does not depend on the Lean copy of the Rust code (`Bppp/Model/`). A later theorem shows that
  the Rust verifier computes this verifier. That theorem cross-checks the copy.

How it works:
1. The prover proves that `M` inputs `V i` are commitments to values below `2^b`.
2. The run has seven steps (§4.2): the prover sends `C_L`, `C_O`; the verifier draws `α`; the
   prover sends `C_R`; the verifier draws `ρ`, `λ`, `β`, `δ`; the prover sends `C_S`; the verifier
   draws `τ`; then both run the NLA.
3. The verifier checks no equation by itself. From the messages and challenges it computes one
   NLA instance (`nlaInstance`, eqs. 25 and 27), and it accepts when the NLA accepts.

How the verifier works (eqs. 24 to 30):
1. `cTauCommit` puts `C_S`, `C_O`, `C_L`, `C_R`, `V̂` at `τ⁻¹, τ⁰, τ, τ², τ³`. It opens to
   `σ(τ)` on `G`, `ℓ(τ)` on `H` and `n(τ)` on `Gs`.
2. The public data puts the weighted sum `E` of all rows into the `T³` coefficient of
   `f(T) = σ(T) - ⟪c(T), ℓ(T)⟫ - ‖n(T)‖²_μ`: `cnL` for the value links, `cnR`, `cnO`, `lamAl`,
   `muAm` for the reciprocal rows, and `cnV`, `clV` for the shape rows.
3. `C_S` cannot reach `T³`, because `cHatPower` skips 4. Other blinding reaches it only times `β`.
4. The NLA proves `f(τ) = 0`. Forks on `τ` (13) and `β` (2) then give `E = 0`.

Assumptions:
- Vectors are `Fin n → F`, as in `Audit/NLA/Round.lean`. Inputs count from 0, so the paper's
  `λ^(i-1)` is `λ^i` here.
- The paper's value base `G` is `G` here, and the paper's bold `𝐆` is `Gs`.
- Name trap: the paper writes `V = v • G + s • H₀`. The Rust Pedersen code writes
  `value • H + blinding • G`. So the paper's `G` is the Rust `H`, and `H₀` is the Rust `G`.
- The verifier rejects the challenges that it must invert (`Challenges.Ok`), as the Rust code does.
- `Params` does not require `1 ≤ M` or `4 ∣ b`, and `F` can be any field. The verifier needs
  neither. The theorems about this protocol add them: eq. 20 needs `1 ≤ M` and `4 ∣ b`, and §5.1
  needs that no integer in `1, …, max(Nd, 16)` is 0 in `F`.
- The verifier does not reject `β = 0`, as in the Rust code. Only the honest prover needs
  `β ≠ 0`.
-/

namespace Audit.RangeProtocol

open Audit.NLA

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E]

/-! ## Parameters (eq. 20) -/

/-- The batch size `M` and the bit width `b`. -/
structure Params where
  /-- The number of inputs. -/
  M : ℕ
  /-- The bit width. Each value is below `2^b`. -/
  b : ℕ

namespace Params

variable (P : Params)

/-- The digits per value: `D = b / 4`, in base 16. -/
def D : ℕ := P.b / 4

/-- The total digit count `Nd = M · D`. -/
def Nd : ℕ := P.M * P.D

/-- The norm length: the least power of two that is at least `max(Nd, 16)`. -/
def nm : ℕ := 2 ^ Nat.clog 2 (max P.Nd 16)

/-- The shape exponents `g_m = M(nm + m) + 1`. -/
def g (m : ℕ) : ℕ := P.M * (P.nm + m) + 1

end Params

/-! Tests: the norm length for one 64-bit value, one 8-bit value, and four 64-bit values. -/
example : (Params.mk 1 64).nm = 16 := by simp [Params.nm, Params.Nd, Params.D]; decide
example : (Params.mk 1 8).nm = 16 := by simp [Params.nm, Params.Nd, Params.D]; decide
example : (Params.mk 4 64).nm = 64 := by simp [Params.nm, Params.Nd, Params.D]; decide

/-! ## Key, messages, challenges and run -/

variable (E) in
/-- The commitment key: the value base `G`, the 8 generators `H`, and the `nm` generators `Gs`. -/
structure Key (P : Params) where
  G : E
  H : Fin 8 → E
  Gs : Fin P.nm → E

variable (E) in
/-- The prover's commitments: `C_L`, `C_O` (step 1), `C_R` (step 3) and `C_S` (step 5). -/
structure Messages where
  /-- The commitment to the digits. -/
  cL : E
  /-- The commitment to the multiplicities. -/
  cO : E
  /-- The commitment to the reciprocals. -/
  cR : E
  /-- The blinding commitment. -/
  cS : E

variable (F) in
/-- The verifier's challenges: `α` (step 2), `ρ`, `λ`, `β`, `δ` (step 4) and `τ` (step 6). -/
structure Challenges where
  α : F
  ρ : F
  lam : F
  β : F
  δ : F
  τ : F

variable (F E) in
/-- One run of the protocol: the commitments, the challenges, and the NLA transcript (step 7) on
the lengths 8 and `nm`. -/
structure Run (P : Params) where
  msgs : Messages E
  ch : Challenges F
  nla : NLA.Transcript F E 8 P.nm

/-! ## Public data (eq. 23)

These depend only on the challenges. `μ = ρ²` is the weight of the norm. -/

section PublicData

variable {P : Params} (ch : Challenges F)

/-- `μ = ρ²`. -/
def Challenges.μ : F := ch.ρ²

/-- `c_{n,L}`: slot `D·i + t` of digit `t` of input `i` gets `λ^i 16^t / μ^(k+1)`. -/
def cnL (k : Fin P.nm) : F :=
  if k.val < P.Nd then ch.lam ^ (k.val / P.D) * 16 ^ (k.val % P.D) / ch.μ ^ (k.val + 1) else 0

/-- `c_{n,R}`. -/
def cnR (k : Fin P.nm) : F :=
  if k.val < P.Nd then ch.lam ^ P.M / ch.μ ^ (k.val + 1) + ch.α else 0

/-- `c_{n,O}`. -/
def cnO (k : Fin P.nm) : F :=
  if k.val ≤ 14 then
    (k.val + 1) * ch.lam ^ P.M / (ch.α * (ch.α + (k.val + 1)) * ch.μ ^ (k.val + 1))
  else 0

/-- `c_{n,V}`. -/
def cnV (k : Fin P.nm) : F := ch.lam ^ (P.M * (k.val + 1) + 1) / ch.μ ^ (k.val + 1)

/-- `c_{ℓ,V} = (0, λ^g₁, …, λ^g₇)`. -/
def clV (s : Fin 8) : F := if s.val = 0 then 0 else ch.lam ^ P.g s.val

/-- `λ_al = Nd λ^M / α`. -/
def lamAl : F := P.Nd * ch.lam ^ P.M / ch.α

/-- `μ_am = μ¹ + … + μ^Nd`. -/
def muAm : F := ∑ k ∈ Finset.range P.Nd, ch.μ ^ (k + 1)

/-- The powers of `T` in `ĉ_r(T)`: `-1, 1, 2, 3, 5, 6, 7`. Slot `s` of `C_S` lands at
`T^(cHatPower s - 1)`. The power 4 is missing, so no slot of `C_S` reaches `T³`. -/
def cHatPower : Fin 7 → ℤ := ![-1, 1, 2, 3, 5, 6, 7]

/-! ## At `τ` (eq. 24) -/

/-- `p_n(τ) = c_{n,V} + τ c_{n,R} + τ² c_{n,L} + δ⁻¹ τ³ c_{n,O}`. -/
def pn (k : Fin P.nm) : F :=
  cnV ch k + ch.τ * cnR ch k + ch.τ² * cnL ch k + ch.δ⁻¹ * ch.τ³ * cnO ch k

/-- `p_s(τ) = ‖p_n(τ)‖²_μ + 2(λ_al + μ_am) τ³`. -/
def ps : F :=
  ‖pn (P := P) ch‖²_ch.μ + 2 * (lamAl (P := P) ch + muAm (P := P) ch) * ch.τ³

/-- `ĉ_r(τ)`: slot `s < 7` holds `β τ^(cHatPower s)`, and slot 7 holds 0. -/
def cHat (s : Fin 8) : F :=
  if h : s.val < 7 then ch.β * ch.τ ^ cHatPower ⟨s.val, h⟩ else 0

/-- `c(τ) = ĉ_r(τ) + c_{ℓ,V}`. -/
def cTau (s : Fin 8) : F := cHat ch s + clV (P := P) ch s

end PublicData

/-! ## The verifier (eqs. 25 and 27) -/

section Verifier

variable {P : Params} (key : Key E P) (V : Fin P.M → E) (msgs : Messages E) (ch : Challenges F)

/-- `V̂ = 2 Σᵢ λ^i V i`. -/
def vHat : E := (2 : F) • ∑ i, ch.lam ^ i.val • V i

/-- The combined commitment
`C(τ) = p_s(τ) G + ⟨p_n(τ), Gs⟩ + τ⁻¹ C_S + δ C_O + τ C_L + τ² C_R + τ³ V̂`. -/
def cTauCommit : E :=
  ps (P := P) ch • key.G + msm (pn ch) key.Gs + ch.τ⁻¹ • msgs.cS + ch.δ • msgs.cO +
    ch.τ • msgs.cL + ch.τ² • msgs.cR + ch.τ³ • vHat V ch

/-- The challenges must be nonzero where the verifier inverts them: `α(α + j)` for `j ≤ 15`,
`μ = ρ²`, `δ` and `τ`. -/
structure Challenges.Ok : Prop where
  hα : ∀ j : ℕ, j ≤ 15 → ch.α + j ≠ 0
  hρ : ch.ρ ≠ 0
  hδ : ch.δ ≠ 0
  hτ : ch.τ ≠ 0

/-- The NLA instance of step 7: the commitment `C(τ)`, the value base `G`, the public vector
`c(τ)`, the generators `H` and `Gs`, and the weight `ρ`. -/
def nlaInstance (hρ : ch.ρ ≠ 0) : NLA.Instance F E 8 P.nm where
  C := cTauCommit key V msgs ch
  g := key.G
  c := cTau (P := P) ch
  H := key.H
  G := key.Gs
  ρ := ch.ρ
  hρ := hρ

/-- The verifier accepts a run when the challenges are allowed and the NLA accepts. -/
def Accepts (r : Run F E P) : Prop :=
  ∃ h : r.ch.Ok, NLA.verify (nlaInstance key V r.msgs r.ch h.hρ) r.nla

end Verifier

end Audit.RangeProtocol
