import Bppp.Constraints
import Bppp.NormLinear

/-!
# `circuit.rs`

The prover's random draws are an input (`Randomness`), and the test-only parameter
`bad_reciprocals` of `prove_witness` is not modelled. Serialization is not modelled.
-/

namespace Bppp

variable {F E : Type} [Field F] [DecidableEq F] [AddCommGroup E] [Module F E] [DecidableEq E]

namespace Circuit

/-- `CR_POWERS`. -/
def CR_POWERS : List ℤ := [-1, 1, 2, 3, 5, 6, 7]

variable (F E) in
/-- `CircuitProof`. -/
structure CircuitProof where
  c_l : E
  c_o : E
  c_r : E
  c_s : E
  nl_proof : NormLinearProof F E

/-- `c`. -/
def c (constraints : Constraints F) (beta : F) : Laurent (List F) :=
  Laurent.from_terms ((0, constraints.cl_v) ::
    CR_POWERS.zipIdx.map fun (a, j) => (a, (List.replicate H_LEN 0).set j beta))

/-- `h_coordinates`. -/
def h_coordinates (r : List F) : List F := r.drop 1 ++ [0]

/-- `commit`. -/
def commit (gens : Generators E) (r n : List F) : Result E :=
  gens.commit (r.headD 0) (h_coordinates r) n

/-- `blinding_vector`, with `rng i` the draw for slot `i`. -/
def blinding_vector (rng : ℕ → F) (zeros : List ℕ) : List F :=
  (List.range H_LEN).map fun i => if i ∈ zeros then 0 else rng i

/-- `reciprocals`. -/
def reciprocals (params : CircuitParams) (n_l : List F) (alpha : F) : Result (List F) := do
  let denominators := (n_l.take params.n_d).map (alpha + ·)
  pure (pad_to (← batch_invert denominators) params.nm)

variable (F) in
/-- `Witness`. -/
structure Witness where
  values : List F
  blindings : List F
  off_plane : List (List F × F)
  n_l : List F
  n_o : List F
  r_o : List F
  r_l : List F
  r_r : List F
  n_s : List F
  l_s : F

variable (F) in
/-- The draws of `Witness::new` from `rng`. -/
structure Randomness where
  r_o : ℕ → F
  r_l : ℕ → F
  r_r : ℕ → F
  n_s : ℕ → F
  l_s : F

namespace Witness

/-- `Witness::new`. -/
def new (params : CircuitParams) (rng : Randomness F) (values : List ℕ) (blindings : List F) :
    Witness F :=
  let digits := values.flatMap fun v => to_digits v params.d
  { values := to_scalars values
    blindings
    off_plane := []
    n_l := pad_to (to_scalars digits) params.nm
    n_o := pad_to (to_scalars (multiplicities digits)) params.nm
    r_o := blinding_vector rng.r_o [4, 7]
    r_l := blinding_vector rng.r_l [3, 6, 7]
    r_r := blinding_vector rng.r_r [2, 5, 6, 7]
    n_s := (List.range params.nm).map rng.n_s
    l_s := rng.l_s }

/-- `Witness::input_commitments`, under the Pedersen bases `G`, `H`. -/
def input_commitments (self : Witness F) (G H : E) (gens : Generators E) :
    Result (List (PedersenCommitment E)) :=
  (List.zip self.values self.blindings).zipIdx.mapM fun ((v, s), i) => do
    let commitment := PedersenCommitment.new G H v s
    match self.off_plane[i]? with
    | some (n, l) =>
      let p ← multi_scalar_mul (n ++ [l]) (gens.g_vec ++ [gens.h_vec.getD (H_LEN - 1) 0])
      pure ⟨commitment.point + p⟩
    | none => pure commitment

end Witness

/-- `error_polynomial`. -/
def error_polynomial (sigma : Laurent F) (c l n : Laurent (List F)) (bar_mu : List F) :
    Laurent F :=
  sigma - c.inner_product l - n.weighted_inner_product n bar_mu

/-- `solve_r_s`. -/
def solve_r_s (constraints : Constraints F) (rest : Laurent F) (l_s beta : F) :
    Result (F × List F) := do
  let beta_inv ← inverse beta
  let h := CR_POWERS.map (fun a => rest.coeff (a - 1) * beta_inv) ++ [l_s]
  pure (inner_product constraints.cl_v h - rest.coeff (-1), h)

/-- `coordinates_without_c_s`. -/
def coordinates_without_c_s (params : CircuitParams) (constraints : Constraints F)
    (witness : Witness F) (n_r : List F) (delta delta_inv : F) :
    Laurent F × Laurent (List F) × Laurent (List F) :=
  let two : F := 2
  let weights := (constraints.lambdas.take params.m).map (two * ·)
  let v_hat := inner_product weights witness.values
  let (n_v_hat, l_v_hat) := (List.zip witness.off_plane weights).foldl
    (fun (n_v_hat, l_v_hat) ((n_i, l_i), w) =>
      (vec_add n_v_hat (vec_scalar_mul w n_i), l_v_hat + w * l_i))
    (List.replicate params.nm 0, 0)
  let v_hat_h := ((List.replicate H_LEN 0).set 0 (inner_product weights witness.blindings)).set
    (H_LEN - 1) l_v_hat
  let p_n := constraints.p_n delta_inv
  let n := Laurent.new (-1) [witness.n_s, vec_scalar_mul delta witness.n_o, witness.n_l, n_r,
    n_v_hat] + p_n
  let sigma := Laurent.new 0 [delta * witness.r_o.headD 0, witness.r_l.headD 0,
      witness.r_r.headD 0] + p_n.weighted_inner_product p_n constraints.norm_weights +
    Laurent.monomial 3 (v_hat + two * (constraints.lambda_al + constraints.mu_am))
  let l := Laurent.new 0 [vec_scalar_mul delta (h_coordinates witness.r_o),
    h_coordinates witness.r_l, h_coordinates witness.r_r, v_hat_h]
  (sigma, l, n)

open BpppTranscript

/-- `prove_witness`, without the test-only `bad_reciprocals`; `G`, `H` are the Pedersen bases. -/
def prove_witness (G H : E) (gens : Generators E) (params : CircuitParams)
    (witness : Witness F) : TranscriptM F E (CircuitProof F E × List (PedersenCommitment E)) := do
  let v_commitments ← witness.input_commitments G H gens
  domain_sep "bppp_circuit"
  append_commits "V" v_commitments
  -- Step 1
  let c_l ← commit gens witness.r_l witness.n_l
  let c_o ← commit gens witness.r_o witness.n_o
  append_point "C_L" c_l
  append_point "C_O" c_o
  -- Step 2
  let alpha ← challenge_scalar "alpha"
  -- Step 3
  let n_r ← reciprocals params witness.n_l alpha
  let c_r ← commit gens witness.r_r n_r
  append_point "C_R" c_r
  -- Step 4
  let rho ← challenge_scalar "rho"
  let lambda ← challenge_scalar "lambda"
  let beta ← challenge_scalar "beta"
  let delta ← challenge_scalar "delta"
  let mu := rho * rho
  let delta_inv ← inverse delta
  let constraints ← Constraints.new params alpha mu lambda
  -- Step 5
  let (sigma, l, n) := coordinates_without_c_s params constraints witness n_r delta delta_inv
  let c := c constraints beta
  let rest := error_polynomial sigma c l n constraints.norm_weights
  let (g_s, h_s) ← solve_r_s constraints rest witness.l_s beta
  let c_s ← gens.commit g_s h_s witness.n_s
  append_point "C_S" c_s
  -- Step 6
  let tau ← challenge_scalar "tau"
  -- Step 7
  let l := l + Laurent.monomial (-1) h_s
  let c_tau ← c.eval tau
  let l_tau ← l.eval tau
  let n_tau ← n.eval tau
  let nl_proof ← NormLinear.prove gens c_tau rho l_tau n_tau
  pure ({ c_l, c_o, c_r, c_s, nl_proof }, v_commitments)

/-- `prove`, with the draws `rng`; `G`, `H` are the Pedersen bases. -/
def prove (G H : E) (gens : Generators E) (params : CircuitParams) (rng : Randomness F)
    (values : List ℕ) (blindings : List F) :
    TranscriptM F E (CircuitProof F E × List (PedersenCommitment E)) := do
  if values.length ≠ params.m ∨ blindings.length ≠ params.m ∨
      gens.g_vec.length ≠ params.nm ∨ values.any (fun v => !params.range.is_in_range v) then
    throw .InvalidInput
  let witness : Witness F := .new params rng values blindings
  prove_witness G H gens params witness

/-- `verify`. -/
def verify (gens : Generators E) (params : CircuitParams) (proof : CircuitProof F E)
    (v_commitments : List (PedersenCommitment E)) : TranscriptM F E Unit := do
  if v_commitments.length ≠ params.m ∨ gens.g_vec.length ≠ params.nm then
    throw .InvalidInput
  domain_sep "bppp_circuit"
  append_commits "V" v_commitments
  append_point "C_L" proof.c_l
  append_point "C_O" proof.c_o
  let alpha ← challenge_scalar "alpha"
  append_point "C_R" proof.c_r
  let rho ← challenge_scalar "rho"
  let lambda ← challenge_scalar "lambda"
  let beta ← challenge_scalar "beta"
  let delta ← challenge_scalar "delta"
  let mu := rho * rho
  let delta_inv ← inverse delta
  append_point "C_S" proof.c_s
  let tau ← challenge_scalar "tau"
  let tau_inv ← inverse tau
  let t2 := tau * tau
  let t3 := t2 * tau
  let constraints ← Constraints.new params alpha mu lambda
  let pn_tau ← (constraints.p_n delta_inv).eval tau
  let ps_tau := weighted_norm pn_tau mu + 2 * (constraints.lambda_al + constraints.mu_am) * t3
  let c_tau ← (c constraints beta).eval tau
  let two_t3 := 2 * t3
  let extra := [(tau_inv, proof.c_s), (delta, proof.c_o), (tau, proof.c_l), (t2, proof.c_r)] ++
    v_commitments.zipIdx.map fun (v_i, i) =>
      (two_t3 * constraints.lambdas.getD i 0, v_i.point)
  NormLinear.verify gens c_tau ps_tau pn_tau extra rho proof.nl_proof

end Circuit

end Bppp
