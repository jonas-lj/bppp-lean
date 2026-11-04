import Bppp.Correctness
import Bppp.Proofs.ZeroKnowledge
import Bppp.Spec.ZeroKnowledge

/-!
# Zero-knowledge of `range_proof.rs`

Against an honest verifier, `RangeProof::prove_batch` under uniform randomness has the
distribution of a simulator that sees only the commitments, `range`, `dst`, the generators and the
challenges. It is stated in VCVio's terms, as its `PerfectHVZK`: `$ᵗ X` samples `X` uniformly
and `=ᵈ` is equality in distribution.
-/

open Finset

namespace Bppp

variable {F E : Type} [Field F] [DecidableEq F] [AddCommGroup E] [Module F E] [DecidableEq E]

set_option linter.unusedSectionVars false

namespace RangeProof

open BpppTranscript Circuit

/-- `prove_batch`'s result from the result of `circuit::prove`. -/
def batchOf (r : Except Error ((CircuitProof F E × List (PedersenCommitment E)) ×
    BpppTranscript F E)) : Result (RangeProof F E) :=
  match r with
  | .ok ((proof, _), _) => .ok ⟨proof⟩
  | .error _ => .error .GeneralOpaqueError

/-- **The simulator** of `prove_batch`: `Spec.simView` on the commitments, then `finish`. -/
noncomputable def simBatch (o' : List String → F) (gens : Generators E) (params : CircuitParams)
    (hv : params.Valid) (commitments : List (PedersenCommitment E)) (range : Range)
    (dst : List ℕ) (alpha rho lambda beta delta : F) (τ : Fˣ)
    (y : ((Fin params.nm → F) × F) × (Fin 10 → F)) : Result (RangeProof F E) :=
  batchOf (finish gens (params.toSpec hv) (specCh alpha rho lambda beta delta) rho τ
    (transcript (fun l => o' (chalLabels l)) dst range.bits commitments.length) commitments
    (Spec.simView (params.toSpec hv) (specCh alpha rho lambda beta delta) τ gens.g
      (fun k => gens.h_vec.getD k 0) (fun k => gens.g_vec.getD k 0)
      (fun i => (commitments.getD i ⟨0⟩).point) y))

/-- **Honest-verifier zero-knowledge of `prove_batch`.** Take a transcript hash whose challenges
depend only on which challenges came before (an honest verifier's), with challenges `α` not in
`{0, -1, ..., -15}` and `ρ, β, δ, τ ≠ 0`. Take values in `range`, generators of the right shape
with `g = pedersen::H` and `h_vec[0] = pedersen::G`, all in the span of `g`, with
`h_vec[j] = h_j g`, `h_0 ≠ 0` and `β² ≠ h_0 (h_1 + λ^{g_1})`. Then `prove_batch`, with its masks
and blindings uniform, has the distribution of `simBatch`, which sees only the commitments, `range`,
`dst`, the generators and the challenges. -/
theorem zero_knowledge [Fintype F] [SampleableType F] (o' : List String → F)
    (generators : Range → ℕ → Result (Generators E)) (G H : E) (values : List ℕ)
    (blindings : List F) (range : Range) (dst : List ℕ) (gens : Generators E)
    (params : CircuitParams) (hgens : generators range values.length = .ok gens)
    (hparams : CircuitParams.new range values.length = .ok params) (hv : params.Valid)
    (hh : gens.h_vec.length = H_LEN) (hg : gens.g_vec.length = params.nm) (hgH : gens.g = H)
    (hhG : gens.h_vec.getD 0 0 = G) (hvals : values ≠ []) (hb : blindings.length = values.length)
    (hrange : ∀ v ∈ values, range.is_in_range v) (h gg : ℕ → F)
    (hH : ∀ j, gens.h_vec.getD j 0 = h j • gens.g) (hG : ∀ k, gens.g_vec.getD k 0 = gg k • gens.g)
    (alpha rho lambda beta delta : F) (τ : Fˣ)
    (hα : o' ["alpha"] = alpha) (hρ : o' ["alpha", "rho"] = rho)
    (hlam : o' ["alpha", "rho", "lambda"] = lambda)
    (hβ : o' ["alpha", "rho", "lambda", "beta"] = beta)
    (hδ : o' ["alpha", "rho", "lambda", "beta", "delta"] = delta)
    (hτ : o' ["alpha", "rho", "lambda", "beta", "delta", "tau"] = τ)
    (halpha : ∀ j : ℕ, j < 16 → alpha + j ≠ 0) (hrho0 : rho ≠ 0) (hbeta0 : beta ≠ 0)
    (hdelta0 : delta ≠ 0) (hh0 : h 0 ≠ 0)
    (hD : beta ^ 2 - h 0 * (h 1 + lambda ^ (params.toSpec hv).g 1) ≠ 0) :
    (fun x => prove_batch (fun l => o' (chalLabels l)) generators G H values blindings range dst
        (rngOf params hv x)) <$> ($ᵗ (Spec.Masks F (params.toSpec hv) × (Fin 15 → F))) =ᵈ
      simBatch o' gens params hv (commitments G H values blindings) range dst alpha rho lambda
        beta delta τ <$> ($ᵗ (((Fin params.nm → F) × F) × (Fin 10 → F))) := by
  have hm : values.length ≠ 0 := by simpa using hvals
  obtain ⟨params', hpn, -, hpr, hpm, -, h16⟩ := params_new range values.length hm
  obtain rfl : params = params' := by rw [hparams] at hpn; exact Except.ok.inj hpn
  have hd : ∀ v ∈ values, v < 16 ^ params.d := fun v hv' => by
    have := hrange v hv'
    simp only [Range.is_in_range, decide_eq_true_eq] at this
    rw [h16]; have := Nat.one_le_two_pow (n := range.bits); omega
  set P := params.toSpec hv
  set ch := specCh alpha rho lambda beta delta
  set t := transcript (fun l => o' (chalLabels l)) dst range.bits values.length (F := F) (E := E)
  set Hf : ℕ → E := fun k => gens.h_vec.getD k 0
  set Gf : ℕ → E := fun k => gens.g_vec.getD k 0
  set d : ℕ → ℕ → ℕ := fun i t => values.getD i 0 / 16 ^ t % 16
  set sb : ℕ → F := fun i => blindings.getD i 0
  have hvcs : commitments (F := F) G H (blindings := blindings) values =
      (List.zip (to_scalars values : List F) blindings).map fun (v, s) =>
        PedersenCommitment.new G H v s := rfl
  have ht : chalLabels t.log = [] := by simp [t, transcript, BpppTranscript.new]
  -- Each run of `prove_batch` is `finish` of the honest view.
  have hrun : ∀ x, prove_batch (fun l => o' (chalLabels l)) generators G H values blindings range
      dst (rngOf params hv x) = batchOf (finish gens P ch rho τ t (commitments G H values blindings)
        (Spec.realView P ch d sb τ gens.g Hf Gf x)) := fun x => by
    have hc : ¬(values = [] ∨ values.length ≠ blindings.length ∨
        values.any (fun v => !range.is_in_range v)) := by
      simp [hvals, hb]; intro v hv'; simpa using hrange v hv'
    have hp := prove_view params hv (rngOf params hv x) values blindings G H gens t o'
      (fun _ => rfl) ht hh hg hpm.symm (by rw [hb, hpm]) (by rw [hpr]; exact hrange) hd
      alpha rho lambda beta delta τ hα hρ hlam hβ hδ hτ halpha hrho0 hbeta0 hdelta0
    rw [specHonest_rngOf params hv values blindings x] at hp
    simp only [prove_batch, hc, if_false, hgens, hparams, bind, Except.bind, StateT.run']
    have hp' : (Circuit.prove G H gens params (rngOf params hv x) values blindings).run t =
        finish gens P ch rho τ t (commitments G H values blindings)
          (Spec.realView P ch d sb τ gens.g Hf Gf x) := hp
    rw [show (Circuit.prove G H gens params (rngOf params hv x) values blindings) t =
      (Circuit.prove G H gens params (rngOf params hv x) values blindings).run t from rfl, hp']
    generalize finish gens P ch rho τ t (commitments G H values blindings) (Spec.realView P ch d sb τ gens.g Hf Gf x) = r
    rcases r with e | ⟨⟨proof, _⟩, _⟩ <;> rfl
  -- The inputs, as the simulator sees them.
  have hV : ∀ y, Spec.simView P ch τ gens.g Hf Gf
      (Spec.Honest.inputs (P := P) gens.g Hf (Spec.zkHonest P d sb 0 0)) y =
      Spec.simView P ch τ gens.g Hf Gf (fun i => ((commitments G H values blindings).getD i ⟨0⟩).point) y := fun y => by
    have hvh : Spec.vHat P ch (Spec.Honest.inputs (P := P) gens.g Hf (Spec.zkHonest P d sb 0 0)) =
        Spec.vHat P ch (fun i => ((commitments G H values blindings).getD i ⟨0⟩).point) := by
      simp only [Spec.vHat]
      congr 1
      refine sum_congr rfl fun i hi => ?_
      have hi : i < values.length := by rw [← hpm]; simpa [P] using hi
      have hvl : (commitments (F := F) G H values blindings).length = values.length := by
        simp [hvcs, length_to_scalars, hb]
      rw [← getElem_eq_getD' _ (by rw [hvl]; exact hi)]
      simp only [hvcs, List.getElem_map, List.getElem_zip]
      simp only [PedersenCommitment.new, Spec.Honest.inputs, Spec.zkHonest, hgH]
      rw [show Hf 0 = G from hhG, getElem_eq_getD' _ _ 0, getD_to_scalars,
        value_eq params hv (rngOf params hv 0) values blindings hd i hi,
        getElem_eq_getD' _ _ 0]
      rfl
    simp only [Spec.simView, hvh]
  have hzk := Spec.zero_knowledge P ch d sb τ h gg gens.g Hf Gf hH hG halpha
    (mul_ne_zero hrho0 hrho0) hbeta0 hdelta0 hh0 hD
    (fun i _ t _ => Nat.mod_lt _ (by norm_num))
  rw [show (fun x => prove_batch (fun l => o' (chalLabels l)) generators G H values blindings
      range dst (rngOf params hv x)) = (fun v => batchOf (finish gens P ch rho τ t (commitments G H values blindings) v)) ∘
      Spec.realView P ch d sb τ gens.g Hf Gf from funext hrun, LawfulFunctor.comp_map]
  refine (hzk.map _).trans ?_
  rw [Functor.map_map]
  have key : ∀ {α β : Type} (f g : α → β) (x : ProbComp α), f = g → f <$> x =ᵈ g <$> x := by
    rintro _ _ f g x rfl; rfl
  refine key _ _ _ (funext fun y => ?_)
  have hvl : (commitments (F := F) G H values blindings).length = values.length := by
    simp [hvcs, length_to_scalars, hb]
  simp only [Function.comp, simBatch, hV, hvl]
  rfl

end RangeProof

end Bppp
