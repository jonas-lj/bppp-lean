import Audit.«02-RangeProof»
import Audit.NLAFull.Legacy

/-!
# The nested fork tree of the range proof

This file keeps the old fork tree of the range proof, with one structure for each challenge.

Why it exists:
- The old soundness proof (`Audit/RangeProof/Proofs.lean`) uses it.
- The new proof will turn a `RangeForkTree` (`Audit/02-RangeProof.lean`) into this form, because
  Jonas's extraction lemmas use one indexed family for each challenge.
-/

namespace Audit.RangeProof

open Bppp

variable {F E : Type} [Field F] [DecidableEq F] [AddCommGroup E] [Module F E] [DecidableEq E]

/-! ## The fork tree -/

section ForkTree

variable (F E) (P : CircuitParams)

/-- After `C_S`: 13 distinct nonzero `τ`, each with an NLA fork tree. -/
structure TauFork where
  /-- The prover's message `C_S`. -/
  cS : E
  /-- The 13 challenges `τ`. -/
  τ : Fin 13 → F
  hDistinct : ∀ i j, i ≠ j → τ i ≠ τ j
  hNonzero : ∀ i, τ i ≠ 0
  /-- The NLA fork tree for each `τ`. -/
  next : Fin 13 → NLA.ForkTree F E H_LEN P.nm

/-- `M(nm + 8) + 1` distinct `λ`. -/
structure LamFork where
  /-- The challenges `λ`. -/
  lam : Fin (P.m * (P.nm + 8) + 1) → F
  hDistinct : ∀ i j, i ≠ j → lam i ≠ lam j
  next : Fin (P.m * (P.nm + 8) + 1) → TauFork F E P

/-- 2 distinct `β`. -/
structure BetaFork where
  /-- The challenges `β`. -/
  β : Fin 2 → F
  hDistinct : β 0 ≠ β 1
  next : Fin 2 → LamFork F E P

/-- After `C_R`: `nm + 1` nonzero `ρ` with distinct squares. Each `ρ` has one nonzero `δ`. -/
structure RhoFork where
  /-- The prover's message `C_R`. -/
  cR : E
  /-- The challenges `ρ`. -/
  ρ : Fin (P.nm + 1) → F
  hNonzero : ∀ i, ρ i ≠ 0
  hSqDistinct : ∀ i j, i ≠ j → ρ i ^ 2 ≠ ρ j ^ 2
  /-- The challenge `δ` for each `ρ`. It is not forked. -/
  δ : Fin (P.nm + 1) → F
  hδNonzero : ∀ i, δ i ≠ 0
  next : Fin (P.nm + 1) → BetaFork F E P

/-- The full fork tree: `C_L`, `C_O`, then `Nd + 16` distinct `α` with `α + j ≠ 0` for `j < 16`. -/
structure NestedTree where
  /-- The prover's message `C_L`. -/
  cL : E
  /-- The prover's message `C_O`. -/
  cO : E
  /-- The challenges `α`. -/
  α : Fin (Nd P + 16) → F
  hDistinct : ∀ i j, i ≠ j → α i ≠ α j
  hPole : ∀ i, ∀ j : ℕ, j < 16 → α i + j ≠ 0
  next : Fin (Nd P + 16) → RhoFork F E P

end ForkTree

/-! ## Runs -/

section Runs

variable {P : CircuitParams}

variable (F E P) in
/-- One run: the prover's messages, the challenges, and the NLA transcript. -/
structure Run where
  cL : E
  cO : E
  cR : E
  cS : E
  α : F
  ρ : F
  lam : F
  β : F
  δ : F
  τ : F
  nla : NLA.Transcript F E H_LEN P.nm

/-- The NLA fork tree under the branches `a` of `α`, `r` of `ρ`, `b` of `β`, `l` of `λ` and `i`
of `τ`. -/
def NestedTree.nla (t : NestedTree F E P) (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1))
    (b : Fin 2) (l : Fin (P.m * (P.nm + 8) + 1)) (i : Fin 13) :
    NLA.ForkTree F E H_LEN P.nm :=
  ((((t.next a).next r).next b).next l).next i

/-- The run on the branches `a, r, b, l, i`, with the NLA transcript `p`. -/
def NestedTree.run (t : NestedTree F E P) (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1))
    (b : Fin 2) (l : Fin (P.m * (P.nm + 8) + 1)) (i : Fin 13)
    (p : NLA.Transcript F E H_LEN P.nm) : Run F E P :=
  let ρf := t.next a
  let βf := ρf.next r
  let lf := βf.next b
  let τf := lf.next l
  { cL := t.cL, cO := t.cO, cR := ρf.cR, cS := τf.cS,
    α := t.α a, ρ := ρf.ρ r, lam := lf.lam l, β := βf.β b, δ := ρf.δ r, τ := τf.τ i, nla := p }

/-- The Rust NLA proof of an NLA transcript: `(X, R)` of each round, and the final opening. -/
def nlaProof {m k : ℕ} : NLA.Transcript F E m k → NormLinearProof F E
  | .done w _ => ⟨[], (List.ofFn w.ℓ).headD 0, List.ofFn w.n⟩
  | .round X R _ rest _ => { nlaProof rest with rounds := (X, R) :: (nlaProof rest).rounds }

/-- The NLA challenges `γ` of an NLA transcript, in order. -/
def gammas {m k : ℕ} : NLA.Transcript F E m k → List F
  | .done _ _ => []
  | .round _ _ γ rest _ => γ :: gammas rest

/-- The Rust proof of a run. -/
def Run.proof (r : Run F E P) : Bppp.RangeProof F E :=
  ⟨{ c_l := r.cL, c_o := r.cO, c_r := r.cR, c_s := r.cS, nl_proof := nlaProof r.nla }⟩

/-- Whether a transcript entry is an NLA challenge. -/
def isGamma : Entry F E → Bool
  | .challenge "gamma" => true
  | _ => false

/-- The hash of a run: it answers each challenge with the value in `r`. The `i`-th `gamma`
gets the `i`-th NLA challenge. -/
def Run.oracle (r : Run F E P) (log : List (Entry F E)) : F :=
  match log.getLast? with
  | some (.challenge "alpha") => r.α
  | some (.challenge "rho") => r.ρ
  | some (.challenge "lambda") => r.lam
  | some (.challenge "beta") => r.β
  | some (.challenge "delta") => r.δ
  | some (.challenge "tau") => r.τ
  | some (.challenge "gamma") => (gammas r.nla).getD (log.countP isGamma - 1) 0
  | _ => 0

/-- `verify_batch` accepts the proof of `r` with the hash of `r`. -/
def Accepted (generators : ℕ → Result (Generators E)) (commitments : List (PedersenCommitment E))
    (range : Range) (dst : List ℕ) (r : Run F E P) : Prop :=
  r.proof.verify_batch r.oracle generators commitments range dst = .ok ()

end Runs

end Audit.RangeProof
