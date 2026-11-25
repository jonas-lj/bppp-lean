import Audit.RangeProof.Statement
import Bppp.Correctness
import Bppp.Proofs.NormLinearSoundness
import Bppp.Soundness

/-!
# Completeness of the range proof

This file proves `RangeCompleteness` (`Audit/02-RangeProof.lean`). You do not need to review it.

How it works:
1. Locality: each part of the Rust proof depends only on the challenges that Rust asks for
   before it computes that part. `prove_loop_local` shows this for the NLA rounds, and
   `prove_witness_local` for the circuit messages.
2. `prove_verify_ok`: Jonas's completeness (`Bppp.RangeProof.completeness`), with a hash
   `hashOf A` whose answers make the Rust prover succeed (`AnswersOk`).
3. `range_complete`: the honest prover reads each message from a run with a prefix of the
   challenges. By 1, the message is the same as in the run with all challenges. By 2, the
   verifier accepts that run.
-/

namespace Audit.RangeProof

open Bppp BpppTranscript Circuit NormLinear Audit.TreeSoundness

variable {F E : Type} [Field F] [DecidableEq F] [AddCommGroup E] [Module F E] [DecidableEq E]

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## Runs as equations -/

theorem except_bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem run_liftM {σ ε α : Type} (r : Except ε α) (t : σ) :
    (liftM r : StateT σ (Except ε) α).run t = r >>= fun a => .ok (a, t) := by
  cases r <;> rfl

theorem pure_eq_ok {σ ε α : Type} {a b : α} {s t : σ} :
    (pure (a, s) : Except ε (α × σ)) = .ok (b, t) ↔ a = b ∧ s = t := by
  simp [pure, Except.pure]

theorem hashOf_challenge (A : List F) (log : List (Entry F E)) (label : String) :
    hashOf A (log ++ [Entry.challenge label]) = A.getD (log.countP isChallenge) 1 := by
  simp [hashOf, List.countP_append, isChallenge]

theorem prove_loop_local (A B : List F) : ∀ (N : ℕ) (lb : LazyBases F E) (c : List F) (rho : F)
    (l n : List F) (T₁ T₂ T₁' T₂' : BpppTranscript F E) (p₁ p₂ : NormLinearProof F E) (c₀ : ℕ),
    l.length + n.length = N → T₁.oracle = hashOf A → T₂.oracle = hashOf B →
    T₁.log.countP isChallenge = c₀ → T₂.log.countP isChallenge = c₀ →
    (prove_loop lb c rho l n).run T₁ = .ok (p₁, T₁') →
    (prove_loop lb c rho l n).run T₂ = .ok (p₂, T₂') →
    (∀ k, (∀ i < k, A.getD (c₀ + i) 1 = B.getD (c₀ + i) 1) →
      p₁.rounds.getD k (0, 0) = p₂.rounds.getD k (0, 0)) ∧
    ((∀ i < p₁.rounds.length, A.getD (c₀ + i) 1 = B.getD (c₀ + i) 1) →
      p₁.l_final = p₂.l_final ∧ p₁.n_final = p₂.n_final) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro lb c rho l n T₁ T₂ T₁' T₂' p₁ p₂ c₀ hN ho₁ ho₂ hc₁ hc₂ h₁ h₂
  rw [prove_loop] at h₁ h₂
  by_cases hb : is_base_case l.length n.length
  · simp only [dif_pos hb, StateT.run_bind, run_append_scalars, except_bind_eq_ok,
      Except.ok.injEq, exists_eq_left, exists_eq_left', Prod.exists, StateT.run_pure,
      pure_eq_ok] at h₁ h₂
    obtain ⟨rfl, -⟩ := h₁
    obtain ⟨rfl, -⟩ := h₂
    exact ⟨fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩⟩
  · simp only [dif_neg hb, StateT.run_bind, run_liftM, run_append_point, run_challenge_scalar,
      except_bind_eq_ok, bind_assoc, Except.ok.injEq, exists_eq_left, exists_eq_left',
      Prod.exists, StateT.run_pure, pure_bind, extend_extend, extend_oracle, extend_log,
      pure_eq_ok] at h₁ h₂
    obtain ⟨ri, hri, x, b, hx, r, b', hr, q₁, U₁, hq₁, hp₁, -⟩ := h₁
    obtain ⟨ri', hri', x', b2, hx', r', b2', hr', q₂, U₂, hq₂, hp₂, -⟩ := h₂
    rw [hri] at hri'; cases hri'
    rw [hx] at hx'; cases hx'
    rw [hr] at hr'; cases hr'
    subst hp₁ hp₂
    rw [ho₁, hashOf_challenge] at hq₁
    rw [ho₂, hashOf_challenge] at hq₂
    have hcX : (T₁.log ++ [Entry.point "X" x] ++ [Entry.point "R" r]).countP isChallenge = c₀ := by
      simp [hc₁, isChallenge]
    have hcX' : (T₂.log ++ [Entry.point "X" x] ++ [Entry.point "R" r]).countP isChallenge = c₀ := by
      simp [hc₂, isChallenge]
    rw [hcX] at hq₁
    rw [hcX'] at hq₂
    have hlen : ∀ γ : F,
        (vec_add (split_even_odd l).1 (vec_scalar_mul γ (split_even_odd l).2)).length +
        (vec_add (vec_scalar_mul ri (split_even_odd n).1)
          (vec_scalar_mul γ (split_even_odd n).2)).length < N := by
      intro γ
      have := split_even_odd_length l
      have := split_even_odd_length n
      rw [is_base_case_iff] at hb
      simp only [vec_add, vec_scalar_mul, List.length_zipWith, List.length_map]
      omega
    have ho₁' : (T₁.extend [Entry.point "X" x, Entry.point "R" r, Entry.challenge "gamma"]).oracle =
        hashOf A := ho₁
    have ho₂' : (T₂.extend [Entry.point "X" x, Entry.point "R" r, Entry.challenge "gamma"]).oracle =
        hashOf B := ho₂
    have hc₁' : (T₁.extend [Entry.point "X" x, Entry.point "R" r,
        Entry.challenge "gamma"]).log.countP isChallenge = c₀ + 1 := by
      simp [hc₁, isChallenge]
    have hc₂' : (T₂.extend [Entry.point "X" x, Entry.point "R" r,
        Entry.challenge "gamma"]).log.countP isChallenge = c₀ + 1 := by
      simp [hc₂, isChallenge]
    simp only [List.cons_append, List.nil_append] at hq₁ hq₂
    refine ⟨fun k hk => ?_, fun hk => ?_⟩
    · cases k with
      | zero => rfl
      | succ k =>
        have hγ : A.getD c₀ 1 = B.getD c₀ 1 := by simpa using hk 0 (by omega)
        rw [← hγ] at hq₂
        have := (ih _ (hlen _) _ _ _ _ _ _ _ _ _ _ _ (c₀ + 1) rfl ho₁' ho₂' hc₁' hc₂' hq₁ hq₂).1 k
          (fun i hi => by simpa [Nat.add_assoc, Nat.add_comm 1] using hk (i + 1) (by omega))
        simpa using this
    · have hγ : A.getD c₀ 1 = B.getD c₀ 1 := by simpa using hk 0 (by simp)
      rw [← hγ] at hq₂
      exact (ih _ (hlen _) _ _ _ _ _ _ _ _ _ _ _ (c₀ + 1) rfl ho₁' ho₂' hc₁' hc₂' hq₁ hq₂).2
        (fun i hi => by simpa [Nat.add_assoc, Nat.add_comm 1] using hk (i + 1) (by simp; omega))

/-- `NormLinear.prove` has the same locality as `prove_loop`. -/
theorem nla_prove_local (A B : List F) (gens : Generators E) (c : List F) (rho : F)
    (o : Opening F) (T₁ T₂ T₁' T₂' : BpppTranscript F E) (p₁ p₂ : NormLinearProof F E) (c₀ : ℕ)
    (ho₁ : T₁.oracle = hashOf A) (ho₂ : T₂.oracle = hashOf B)
    (hc₁ : T₁.log.countP isChallenge = c₀) (hc₂ : T₂.log.countP isChallenge = c₀)
    (h₁ : (NormLinear.prove gens c rho o).run T₁ = .ok (p₁, T₁'))
    (h₂ : (NormLinear.prove gens c rho o).run T₂ = .ok (p₂, T₂')) :
    (∀ k, (∀ i < k, A.getD (c₀ + i) 1 = B.getD (c₀ + i) 1) →
      p₁.rounds.getD k (0, 0) = p₂.rounds.getD k (0, 0)) ∧
    ((∀ i < p₁.rounds.length, A.getD (c₀ + i) 1 = B.getD (c₀ + i) 1) →
      p₁.l_final = p₂.l_final ∧ p₁.n_final = p₂.n_final) := by
  simp only [NormLinear.prove, StateT.run_bind, run_domain_sep, except_bind_eq_ok,
    Except.ok.injEq, exists_eq_left'] at h₁ h₂
  exact prove_loop_local A B _ _ _ _ _ _ _ _ _ _ _ _ c₀ rfl (by simpa using ho₁)
    (by simpa using ho₂) (by simp [hc₁, isChallenge]) (by simp [hc₂, isChallenge]) h₁ h₂

/-- The parts of the circuit proof depend only on the challenges before them. -/
theorem prove_witness_local (A B : List F) (G H : E) (gens : Generators E) (params : CircuitParams)
    (W : Witness F) (rec : F → Result (List F)) (t₁ t₂ t₁' t₂' : BpppTranscript F E)
    (p₁ p₂ : CircuitProof F E × List (PedersenCommitment E))
    (ho₁ : t₁.oracle = hashOf A) (ho₂ : t₂.oracle = hashOf B)
    (hc₁ : t₁.log.countP isChallenge = 0) (hc₂ : t₂.log.countP isChallenge = 0)
    (h₁ : (prove_witness G H gens params W rec).run t₁ = .ok (p₁, t₁'))
    (h₂ : (prove_witness G H gens params W rec).run t₂ = .ok (p₂, t₂')) :
    p₁.1.c_l = p₂.1.c_l ∧ p₁.1.c_o = p₂.1.c_o ∧
    (A.getD 0 1 = B.getD 0 1 → p₁.1.c_r = p₂.1.c_r) ∧
    ((∀ i < 5, A.getD i 1 = B.getD i 1) → p₁.1.c_s = p₂.1.c_s) ∧
    ((∀ i < 6, A.getD i 1 = B.getD i 1) →
      (∀ k, (∀ i < k, A.getD (6 + i) 1 = B.getD (6 + i) 1) →
        p₁.1.nl_proof.rounds.getD k (0, 0) = p₂.1.nl_proof.rounds.getD k (0, 0)) ∧
      ((∀ i < p₁.1.nl_proof.rounds.length, A.getD (6 + i) 1 = B.getD (6 + i) 1) →
        p₁.1.nl_proof.l_final = p₂.1.nl_proof.l_final ∧
          p₁.1.nl_proof.n_final = p₂.1.nl_proof.n_final)) := by
  simp only [prove_witness, StateT.run_bind, run_liftM, run_domain_sep, run_append_commits,
    run_append_point, run_challenge_scalar, except_bind_eq_ok, bind_assoc, Except.ok.injEq,
    exists_eq_left, exists_eq_left', Prod.exists, StateT.run_pure, pure_eq_ok, extend_extend,
    extend_oracle, extend_log, ho₁, ho₂, hashOf_challenge, List.countP_append, List.countP_cons,
    List.countP_nil, List.countP_map, Function.comp_def, isChallenge, hc₁, hc₂, Bool.false_eq_true,
    ↓reduceIte, List.countP_false, zero_add, add_zero, Nat.reduceAdd, Function.const_apply]
    at h₁ h₂
  obtain ⟨v, hv, cl, hcl, co, hco, nr, hnr, cr, hcr, di, hdi, C, hC, cs, o, hcs, cτ, hcτ, oτ, hoτ,
    nl, U, hnl, rfl, -⟩ := h₁
  obtain ⟨v', hv', cl', hcl', co', hco', nr', hnr', cr', hcr', di', hdi', C', hC', cs', o', hcs',
    cτ', hcτ', oτ', hoτ', nl', U', hnl', rfl, -⟩ := h₂
  rw [hcl] at hcl'; cases hcl'
  rw [hco] at hco'; cases hco'
  rw [hv] at hv'; cases hv'
  refine ⟨rfl, rfl, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [← h, hnr] at hnr'; cases hnr'
    rw [hcr] at hcr'; cases hcr'
    rfl
  · rw [← h 0 (by norm_num), hnr] at hnr'; cases hnr'
    rw [hcr] at hcr'; cases hcr'
    rw [← h 0 (by norm_num), ← h 1 (by norm_num), ← h 2 (by norm_num), hC] at hC'; cases hC'
    rw [← h 4 (by norm_num), hdi] at hdi'; cases hdi'
    rw [← h 3 (by norm_num), ← h 4 (by norm_num), hcs] at hcs'; cases hcs'
    rfl
  · rw [← h 0 (by norm_num), hnr] at hnr'; cases hnr'
    rw [hcr] at hcr'; cases hcr'
    rw [← h 0 (by norm_num), ← h 1 (by norm_num), ← h 2 (by norm_num), hC] at hC'; cases hC'
    rw [← h 4 (by norm_num), hdi] at hdi'; cases hdi'
    rw [← h 3 (by norm_num), ← h 4 (by norm_num), hcs] at hcs'; cases hcs'
    rw [← h 3 (by norm_num), ← h 5 (by norm_num), hcτ] at hcτ'; cases hcτ'
    rw [← h 5 (by norm_num), hoτ] at hoτ'; cases hoτ'
    rw [← h 1 (by norm_num)] at hnl'
    exact nla_prove_local A B _ _ _ _ _ _ _ _ _ _ 6 (by simpa using ho₁) (by simpa using ho₂)
      (by rw [extend_log, List.countP_append, hc₁]
          simp [isChallenge, Function.comp_def, List.countP_cons])
      (by rw [extend_log, List.countP_append, hc₂]
          simp [isChallenge, Function.comp_def, List.countP_cons]) hnl hnl'


/-! ## The Rust prover and verifier with the hash `hashOf A` -/

/-- The challenges in `A` that the Rust prover inverts are allowed: `α + j ≠ 0` for `j < 16`,
and `ρ`, `β`, `δ`, `τ` are not 0. After the end of `A`, the hash answers 1. -/
def AnswersOk (A : List F) : Prop :=
  (∀ j : ℕ, j < 16 → A.getD 0 1 + j ≠ 0) ∧ A.getD 1 1 ≠ 0 ∧ A.getD 3 1 ≠ 0 ∧
    A.getD 4 1 ≠ 0 ∧ A.getD 5 1 ≠ 0

theorem isChallenge_eq : (isChallenge : Entry F E → Bool) = Entry.isChallenge := by
  funext e; cases e <;> rfl

theorem transcript_count (o : List (Entry F E) → F) (dst : List ℕ) (bits m : ℕ) :
    (Bppp.RangeProof.transcript o dst bits m).log.countP isChallenge = 0 := by
  simp [Bppp.RangeProof.transcript, BpppTranscript.new, isChallenge]

/-- A run of `prove_batch` is a run of `prove_witness` on the Rust setup. -/
theorem prove_batch_run (o : List (Entry F E) → F) (generators : ℕ → Result (Generators E))
    (G H : E) (values : List ℕ) (blindings : List F) (range : Range) (dst : List ℕ)
    (rng : Circuit.Randomness F) (rp : Bppp.RangeProof F E)
    (h : Bppp.RangeProof.prove_batch o generators G H values blindings range dst rng = .ok rp) :
    ∃ params gens vcs t', CircuitParams.new range values.length = .ok params ∧
      generators params.nm = .ok gens ∧
      (prove_witness G H gens params (Witness.new params rng values blindings)
        (fun α => reciprocals params (Witness.new params rng values blindings).n_l α)).run
          (Bppp.RangeProof.transcript o dst range.bits values.length) =
        .ok ((rp.proof, vcs), t') := by
  unfold Bppp.RangeProof.prove_batch at h
  split_ifs at h with hc
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  simp only [Bppp.RangeProof.setup, except_bind_eq_ok, Except.ok.injEq, exists_eq_left',
    Prod.exists, pure, Except.pure] at h
  obtain ⟨p0, g0, t, ⟨params, hp, gens, hg, he⟩, h⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  split at h
  · rename_i proof v heq
    simp only [Except.ok.injEq] at h
    subst h
    simp only [StateT.run'] at heq
    rcases hr : Circuit.prove G H gens params rng values blindings
      (Bppp.RangeProof.transcript o dst range.bits values.length) with e | ⟨⟨q, vcs⟩, t'⟩
    · simp [hr] at heq
    · simp only [hr, Except.ok.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      refine ⟨params, gens, v, t', hp, hg, ?_⟩
      unfold Circuit.prove at hr
      split_ifs at hr
      · simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, StateT.bind,
          Except.bind] at hr
      · exact hr
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- Locality for `prove_batch`: the statement of `prove_witness_local`, for two runs of the Rust
prover with the hashes `hashOf A` and `hashOf B`. -/
theorem prove_batch_local (A B : List F) (generators : ℕ → Result (Generators E)) (G H : E)
    (values : List ℕ) (blindings : List F) (range : Range) (dst : List ℕ)
    (rng : Circuit.Randomness F) (rp₁ rp₂ : Bppp.RangeProof F E)
    (h₁ : Bppp.RangeProof.prove_batch (hashOf A) generators G H values blindings range dst rng =
      .ok rp₁)
    (h₂ : Bppp.RangeProof.prove_batch (hashOf B) generators G H values blindings range dst rng =
      .ok rp₂) :
    rp₁.proof.c_l = rp₂.proof.c_l ∧ rp₁.proof.c_o = rp₂.proof.c_o ∧
    (A.getD 0 1 = B.getD 0 1 → rp₁.proof.c_r = rp₂.proof.c_r) ∧
    ((∀ i < 5, A.getD i 1 = B.getD i 1) → rp₁.proof.c_s = rp₂.proof.c_s) ∧
    ((∀ i < 6, A.getD i 1 = B.getD i 1) →
      (∀ k, (∀ i < k, A.getD (6 + i) 1 = B.getD (6 + i) 1) →
        rp₁.proof.nl_proof.rounds.getD k (0, 0) = rp₂.proof.nl_proof.rounds.getD k (0, 0)) ∧
      ((∀ i < rp₁.proof.nl_proof.rounds.length, A.getD (6 + i) 1 = B.getD (6 + i) 1) →
        rp₁.proof.nl_proof.l_final = rp₂.proof.nl_proof.l_final ∧
          rp₁.proof.nl_proof.n_final = rp₂.proof.nl_proof.n_final)) := by
  obtain ⟨params, gens, vcs, t', hp, hg, hr⟩ := prove_batch_run _ _ _ _ _ _ _ _ _ _ h₁
  obtain ⟨params', gens', vcs', t'', hp', hg', hr'⟩ := prove_batch_run _ _ _ _ _ _ _ _ _ _ h₂
  rw [hp] at hp'; cases hp'
  rw [hg] at hg'; cases hg'
  exact prove_witness_local A B G H gens params _ _ _ _ _ _ _ _ rfl rfl (transcript_count _ _ _ _)
    (transcript_count _ _ _ _) hr hr'

/-- Jonas's `Bppp.RangeProof.completeness`, with the hash `hashOf A` for answers `A` that make
the Rust prover succeed. -/
theorem prove_verify_ok (A : List F) (hA : AnswersOk A) (generators : ℕ → Result (Generators E))
    (G H : E) (values : List ℕ) (blindings : List F) (range : Range) (dst : List ℕ)
    (rng : Circuit.Randomness F) (gens : Generators E) (params : CircuitParams)
    (hvals : values ≠ []) (hb : blindings.length = values.length)
    (hrange : ∀ v ∈ values, range.is_in_range v)
    (hparams : CircuitParams.new range values.length = .ok params)
    (hgens : generators params.nm = .ok gens) (hh : gens.h_vec.length = H_LEN)
    (hg : gens.g_vec.length = params.nm) (hgH : gens.g = H) (hhG : gens.h_vec.getD 0 0 = G) :
    ∃ proof, Bppp.RangeProof.prove_batch (hashOf A) generators G H values blindings range dst rng =
        .ok proof ∧
      proof.verify_batch (hashOf A) generators (Bppp.RangeProof.commitments G H values blindings)
        range dst = .ok () := by
  open Bppp.RangeProof in
  have hm : values.length ≠ 0 := by simpa using hvals
  obtain ⟨params', hpn, hv, hpr, hpm, h16⟩ := params_new range values.length hm
  obtain rfl : params = params' := by rw [hparams] at hpn; exact Except.ok.inj hpn
  have hd : ∀ v ∈ values, v < 16 ^ params.d := fun v hv' => by
    have := hrange v hv'
    simp only [Range.is_in_range, decide_eq_true_eq] at this
    rw [h16]; have := Nat.one_le_two_pow (n := range.bits); omega
  set t := transcript (hashOf A) dst range.bits values.length with ht
  have hidx : ∀ l : List (Entry F E),
      t.oracle (t.log ++ l) = A.getD (l.countP Entry.isChallenge - 1) 1 := by
    intro l
    simp only [ht, transcript, BpppTranscript.new, hashOf, List.countP_append, ← isChallenge_eq]
    simp [isChallenge]
  obtain ⟨proof, t', hprove, hverify⟩ := Circuit.completeness params hv rng values blindings G H
    gens t hh hg hgH hhG hpm.symm (by rw [hb, hpm]) (by rw [hpr]; exact hrange) hd
    (fun l hl j hj => by rw [hidx, hl]; exact hA.1 j hj)
    (fun l hl => by
      rw [hidx]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with h | h | h | h <;> rw [h]
      exacts [hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2])
  refine ⟨⟨proof⟩, ?_, ?_⟩
  · have hc : ¬(values = [] ∨ values.length ≠ blindings.length ∨
        values.any (fun v => !range.is_in_range v)) := by
      simp [hvals, hb]; intro v hv'; simpa using hrange v hv'
    have hp : Circuit.prove G H gens params rng values blindings t =
          .ok ((proof, commitments G H values blindings), t') := hprove
    simp only [prove_batch, hc, if_false, setup, hparams, hgens, bind, Except.bind, pure,
      Except.pure, StateT.run', ← ht, hp]
    rfl
  · have hlen : (commitments G H values blindings : List (PedersenCommitment E)).length =
        values.length := by simp [commitments, length_to_scalars, hb]
    have hc : ¬(commitments G H values blindings : List (PedersenCommitment E)) = [] := by
      intro h0; rw [h0] at hlen; exact hm hlen.symm
    have hv' : Circuit.verify gens params proof (commitments G H values blindings) t =
        .ok ((), t') := hverify
    simp only [verify_batch, hc, if_false, setup, hlen, hparams, hgens, bind, Except.bind, pure,
      Except.pure, StateT.run', ← ht, hv']
    rfl

/-- An accepting run of the circuit verifier has the NLA round count of `proof_shape`. -/
theorem rounds_length_of_verify (gens : Generators E) (params : CircuitParams)
    (proof : CircuitProof F E) (vcs : List (PedersenCommitment E)) (t t' : BpppTranscript F E)
    (h : (Circuit.verify gens params proof vcs).run t = .ok ((), t')) :
    proof.nl_proof.rounds.length = (proof_shape gens.h_vec.length gens.g_vec.length).1 := by
  unfold Circuit.verify at h
  split_ifs at h
  · simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, StateT.run, bind, StateT.bind,
      Except.bind] at h
  simp only [StateT.run_bind, run_liftM, run_domain_sep, run_append_commits,
    run_append_point, run_challenge_scalar, except_bind_eq_ok, bind_assoc, Except.ok.injEq,
    exists_eq_left, exists_eq_left', Prod.exists, StateT.run_pure, pure_eq_ok] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnl⟩ := h
  exact (NormLinear.verify_shape gens _ _ _ _ _ _ _ _ hnl).2

/-! ## The honest prover -/

/-- One round of `RoundTypes.run`. -/
theorem run_round {C Ch : Type} {rest : RoundTypes} {Last : Type} (a : C)
    (next : Ch → rest.Strategy Last) (c : Ch) (cs : rest.Challenges) :
    (RoundTypes.round C Ch rest).run (a, next) (c, cs) =
      ((a, c, (rest.run (next c) cs).1), (rest.run (next c) cs).2) := rfl

/-- The challenges of the NLA rounds, as a list. -/
def nlaList : {n : ℕ} → (nlaRounds F E n).Challenges → List F
  | 0, () => []
  | _ + 1, (γ, rest) => γ :: nlaList rest

/-- The NLA rounds of the honest prover: round `i` sends the pair `i` of the proof after the
first `i` challenges, and the response is the final opening after all challenges. -/
theorem run_nlaStrategy (proof : List F → NormLinearProof F E) : ∀ (n : ℕ) (γs : List F)
    (cs : (nlaRounds F E n).Challenges),
    nlaParts ((nlaRounds F E n).run (nlaStrategy proof n γs) cs).1 =
      ((List.range n).map fun i =>
        (proof (γs ++ (nlaList cs).take i)).rounds.getD (γs.length + i) (0, 0), nlaList cs) ∧
    ((nlaRounds F E n).run (nlaStrategy proof n γs) cs).2 =
      ((proof (γs ++ nlaList cs)).l_final, (proof (γs ++ nlaList cs)).n_final)
  | 0, γs, () => by simp [nlaRounds, RoundTypes.run, nlaStrategy, nlaParts, nlaList]
  | n + 1, γs, (γ, cs) => by
    obtain ⟨h1, h2⟩ := run_nlaStrategy proof n (γs ++ [γ]) cs
    simp only [nlaRounds, nlaStrategy, nlaParts, nlaList, run_round] at h1 h2 ⊢
    rw [h1, h2]
    refine ⟨?_, by simp⟩
    simp only [Prod.mk.injEq, and_true, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · simp
    · refine List.map_congr_left fun i _ => ?_
      simp [Nat.add_assoc, Nat.add_comm 1]

section Statement

variable {P : CircuitParams} (x : RangeStatement F E P) (w : RangeWitness F P)

/-- The Pedersen commitments that the honest prover computes are the input commitments. -/
theorem commitments_eq (hw : OpensInRange x w.value w.blinding) :
    Bppp.RangeProof.commitments x.G x.H ((List.range P.m).map w.value)
      ((List.range P.m).map w.blinding) = x.commitments := by
  have hw' := (opensInRange_iff x _ _).1 hw
  apply List.ext_getElem
  · simp [Bppp.RangeProof.commitments, length_to_scalars, x.length_commitments]
  · intro i h1 h2
    obtain ⟨-, hpt⟩ := hw' i h2
    simp only [Bppp.RangeProof.commitments, to_scalars, List.getElem_map, List.getElem_zip,
      List.getElem_range, PedersenCommitment.new]
    rw [show x.commitments[i] = ⟨x.commitments[i].point⟩ from rfl, hpt]

/-- For allowed answers `A`, the Rust prover succeeds, the verifier accepts, and `proveWith`
gives that proof. -/
theorem proveWith_spec (hw : OpensInRange x w.value w.blinding) (coins : Circuit.Randomness F)
    (A : List F) (hA : AnswersOk A) :
    ∃ rp, Bppp.RangeProof.prove_batch (hashOf A) x.generators x.G x.H
        ((List.range P.m).map w.value) ((List.range P.m).map w.blinding) x.range x.dst coins =
        .ok rp ∧
      rp.verify_batch (hashOf A) x.generators x.commitments x.range x.dst = .ok () ∧
      proveWith x w coins A = rp.proof := by
  have hS := x.setup
  have hm : P.m ≠ 0 := by
    intro h0
    have := x.hParams
    rw [h0] at this
    simp [CircuitParams.new] at this
  obtain ⟨rp, hp, hv⟩ := prove_verify_ok A hA x.generators x.G x.H
    ((List.range P.m).map w.value) ((List.range P.m).map w.blinding) x.range x.dst coins x.gens P
    (by simpa using hm) (by simp)
    (fun v hv => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
      have := ((opensInRange_iff x _ _).1 hw i
        (by rw [x.length_commitments]; exact List.mem_range.1 hi)).1
      simp only [Range.is_in_range, decide_eq_true_eq]
      omega)
    (by simpa using x.hParams) hS.hGens hS.hHLen hS.hGLen hS.hValueBase hS.hBlindingBase
  rw [commitments_eq x w hw] at hv
  exact ⟨rp, hp, hv, by simp [proveWith, hp]⟩

end Statement

/-- The honest prover convinces the verifier. -/
theorem honest_accepted {P : CircuitParams} (x : RangeStatement F E P) (w : RangeWitness F P)
    (hw : OpensInRange x w.value w.blinding) (coins : Circuit.Randomness F)
    (α : {α : F // ∀ j : ℕ, j < 16 → α + j ≠ 0}) (ρ δ β : {a : F // a ≠ 0}) (lam : F)
    (τ : {τ : F // τ ≠ 0}) (γcs : (nlaRounds F E (numNlaRounds P)).Challenges) :
    let run := (rangeProtocol F E P).run (honestStrategy x w coins) (α, ρ, δ, β, lam, τ, γcs)
    rangeVerify x run.1 run.2 := by
  intro run
  set five := [α.val, ρ.val, lam, β.val, δ.val] with hfive
  set pw := proveWith x w coins with hpw
  set N := (nlaRounds F E (numNlaRounds P)).run
    (nlaStrategy (fun γs => (pw (five ++ [τ.val] ++ γs)).nl_proof) (numNlaRounds P) []) γcs
    with hN
  have hrun : run = ((((pw []).c_l, (pw []).c_o), α, (pw [α.val]).c_r, ρ, (), δ, (), β, (), lam,
      (pw five).c_s, τ, N.1), N.2) := rfl
  rw [hrun]
  obtain ⟨hparts, hfinal⟩ := run_nlaStrategy (fun γs => (pw (five ++ [τ.val] ++ γs)).nl_proof)
    (numNlaRounds P) [] γcs
  rw [← hN] at hparts hfinal
  simp only [rangeVerify, hparts, hfinal, List.nil_append, List.length_nil, zero_add]
  set L := five ++ [τ.val] ++ nlaList γcs with hL
  rw [show [α.val, ρ.val, lam, β.val, δ.val, τ.val] ++ nlaList γcs = L by simp [hL, hfive]]
  -- The answer `1` is allowed in every slot.
  have hone : ∀ j : ℕ, j < 16 → (1 : F) + j ≠ 0 := fun j hj => by
    have := x.largeChar.cast_ne_zero (1 + j) (by omega) (by omega)
    push_cast at this
    exact this
  have hτ6 : ∀ γs : List F, AnswersOk (five ++ [τ.val] ++ γs) := fun γs =>
    ⟨by simpa [hfive] using α.2, by simpa [hfive] using ρ.2, by simpa [hfive] using β.2,
      by simpa [hfive] using δ.2, by simpa [hfive] using τ.2⟩
  obtain ⟨rpF, hpF, hvF, hqF⟩ := proveWith_spec x w hw coins L (hτ6 _)
  obtain ⟨rp0, hp0, -, hq0⟩ := proveWith_spec x w hw coins [] ⟨by simpa using hone,
    by simp, by simp, by simp, by simp⟩
  obtain ⟨rp1, hp1, -, hq1⟩ := proveWith_spec x w hw coins [α.val] ⟨by simpa using α.2,
    by simp, by simp, by simp, by simp⟩
  obtain ⟨rp5, hp5, -, hq5⟩ := proveWith_spec x w hw coins five ⟨by simpa [hfive] using α.2,
    by simpa [hfive] using ρ.2, by simpa [hfive] using β.2, by simpa [hfive] using δ.2,
    by simp [hfive]⟩
  have loc0 := prove_batch_local _ _ _ _ _ _ _ _ _ _ _ _ hp0 hpF
  have loc1 := prove_batch_local _ _ _ _ _ _ _ _ _ _ _ _ hp1 hpF
  have loc5 := prove_batch_local _ _ _ _ _ _ _ _ _ _ _ _ hp5 hpF
  -- The NLA rounds.
  have hround : ∀ i, (pw (five ++ [τ.val] ++ (nlaList γcs).take i)).nl_proof.rounds.getD i (0, 0) =
      rpF.proof.nl_proof.rounds.getD i (0, 0) := by
    intro i
    obtain ⟨rpi, hpi, -, hqi⟩ := proveWith_spec x w hw coins _ (hτ6 ((nlaList γcs).take i))
    have loci := prove_batch_local _ _ _ _ _ _ _ _ _ _ _ _ hpi hpF
    rw [hpw, hqi]
    refine (loci.2.2.2.2 (fun j hj => ?_)).1 i (fun j hj => ?_)
    · interval_cases j <;> simp [hL, hfive]
    · rw [Nat.add_comm 6 j]
      simp [hL, hfive, List.getD_eq_getElem?_getD, List.getElem?_take, hj]
  -- An accepted proof has `numNlaRounds P` rounds.
  have hlen : rpF.proof.nl_proof.rounds.length = numNlaRounds P := by
    have hS := x.setup
    obtain ⟨t', hrun⟩ := Bppp.RangeProof.verify_batch_run rpF _ _ _ _ _ x.gens P hS.hGens
      hS.hParams hvF
    rw [rounds_length_of_verify _ _ _ _ _ _ hrun, hS.hHLen, hS.hGLen]
  have hrounds : (List.range (numNlaRounds P)).map (fun i =>
      (pw (five ++ [τ.val] ++ (nlaList γcs).take i)).nl_proof.rounds.getD i (0, 0)) =
      rpF.proof.nl_proof.rounds := by
    simp only [hround]
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  rw [hrounds]
  have e0 := loc0.1
  have e1 := loc0.2.1
  have e2 := loc1.2.2.1 (by simp [hL, hfive])
  have e3 := loc5.2.2.2.1 (fun i hi => by interval_cases i <;> simp [hL, hfive])
  rw [← hq0] at e0 e1
  rw [← hq1] at e2
  rw [← hq5] at e3
  rw [e0, e1, e2, e3, hpw, hqF]
  exact hvF

/-- The completeness of the range proof. -/
theorem range_complete : RangeCompleteness F E :=
  fun _ x w hw coins ⟨α, ρ, δ, β, lam, τ, γcs⟩ => honest_accepted x w hw coins α ρ δ β lam τ γcs

end Audit.RangeProof
