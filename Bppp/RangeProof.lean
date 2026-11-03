import Bppp.Circuit

/-!
# `range_proof.rs`

`Generators::new` is the input `generators`, and `pedersen::G`, `pedersen::H` are the inputs `G`,
`H`. A byte string `dst` is a list of bytes. Serialization is not modelled.
-/

namespace Bppp

variable {F E : Type} [Field F] [DecidableEq F] [AddCommGroup E] [Module F E] [DecidableEq E]

variable (F E) in
/-- `RangeProof`. -/
structure RangeProof where
  proof : Circuit.CircuitProof F E

namespace RangeProof

open BpppTranscript

/-- `transcript`, with the hash `oracle` of the Merlin transcript. -/
def transcript (oracle : List (Entry F E) → F) (dst : List ℕ) (n_bits m : ℕ) :
    BpppTranscript F E :=
  let t := BpppTranscript.new oracle "fastcrypto-bppp-range-proof-01"
  { t with log := t.log ++ [.message "dst" dst, .message "n_bits" [n_bits], .message "m" [m]] }

/-- `RangeProof::prove_batch`, with the draws `rng`. -/
def prove_batch (oracle : List (Entry F E) → F) (generators : Range → ℕ → Result (Generators E))
    (G H : E) (values : List ℕ) (blindings : List F) (range : Range) (dst : List ℕ)
    (rng : Circuit.Randomness F) : Result (RangeProof F E) := do
  if values = [] ∨ values.length ≠ blindings.length ∨ values.any (fun v => !range.is_in_range v)
  then throw .InvalidInput
  let (n_bits, m) := (range.bits, values.length)
  let gens ← generators range m
  let params ← CircuitParams.new range m
  match (Circuit.prove G H gens params rng values blindings).run'
      (transcript oracle dst n_bits m) with
  | .ok (proof, _) => pure ⟨proof⟩
  | .error _ => throw .GeneralOpaqueError

/-- `RangeProof::verify_batch`. -/
def verify_batch (self : RangeProof F E) (oracle : List (Entry F E) → F)
    (generators : Range → ℕ → Result (Generators E)) (commitments : List (PedersenCommitment E))
    (range : Range) (dst : List ℕ) : Result Unit := do
  if commitments = [] then throw .InvalidInput
  let (n_bits, m) := (range.bits, commitments.length)
  let gens ← generators range m
  let params ← CircuitParams.new range m
  match (Circuit.verify gens params self.proof commitments).run'
      (transcript oracle dst n_bits m) with
  | .ok () => pure ()
  | .error _ => throw .InvalidProof

end RangeProof

end Bppp
