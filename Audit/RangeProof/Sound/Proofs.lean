import Audit.RangeProof.Sound.Lift
import Audit.RangeProof.Sound.Digits

/-!
# Soundness of the range proof

This file proves `range_sound : RangeSoundness F E rangeExtract` (`Audit/02-RangeProof.lean`).

Why it exists:
- It is the soundness theorem of the range proof, for the extractor of
  `Audit/RangeProof/Sound/Extractor.lean`.

How it works:
1. If a leaf gives a nonzero NLA link, `rangeLink` is that link (`leaf_facts`).
2. Else, if a check is nonzero, `rangeLink` is that check (`LiftHyp.chk`).
3. Else, every leaf satisfies Jonas's NLA relation in the coordinate space, with the lifted
   commitments (`LiftHyp.rel`).
4. The unit generators have no relation, so `circuit_extract_digits` applies. It gives the
   digits in the coordinates of `C_L`, and the form `u g + s H_0` of each lifted input.
5. `combMap` maps this form to the real input (`LiftHyp.opens`).

Assumptions:
- None beyond the hypotheses of `RangeSoundness`.
-/

namespace Audit.RangeProof.Sound

open Finset Bppp BpppTranscript Circuit Audit.TreeSoundness

variable {F E : Type} [Field F] [DecidableEq F] [AddCommGroup E] [Module F E] [DecidableEq E]

set_option linter.unusedSectionVars false

/-! ## Helpers -/

omit [DecidableEq F] in
/-- Over the unit generators, the point of an opening is its vector of coordinates. -/
theorem point_unit {P : CircuitParams} (o : NLA.Opening F H_LEN P.nm) :
    o.σ • eg P + NLA.msm o.ℓ (fun i => eH P i) + NLA.msm o.n (fun j => eG P j) =
      toComb P o := by
  simp only [NLA.msm, toComb]
  ext i
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Fin.val_eq_val, eq_comm]
  · simp [Prod.snd_sum, Finset.sum_apply, Fin.val_eq_val, eq_comm]

/-- The digit search finds a digit if there is one. -/
theorem digitOf_spec (c : F) (h : ∃ d : ℕ, d < 16 ∧ c = d) :
    digitOf c < 16 ∧ (digitOf c : F) = c := by
  obtain ⟨d, hd, e⟩ := h
  have hs : ((List.range 16).find? fun j : ℕ => ((j : ℕ) : F) = c).isSome := by
    rw [List.find?_isSome]
    exact ⟨d, List.mem_range.2 hd, by simp [e]⟩
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 hs
  have hjm := List.mem_of_find?_eq_some hj
  have hjp := List.find?_some hj
  simp only [digitOf, hj, Option.getD_some]
  exact ⟨List.mem_range.1 hjm, by simpa using hjp⟩

theorem mem_allIdx (P : CircuitParams) (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) (b : Fin 2)
    (l : Fin (P.m * (P.nm + 8) + 1)) (i : Fin 13) : (a, r, b, l, i) ∈ allIdx P := by
  simp [allIdx]

/-! ## The relation in the coordinate space -/

section Lift

variable {P : CircuitParams} {x : RangeStatement F E P} {t : RangeForkTree F E P} {hv : P.Valid}
  {C : Fin (Nd P + 16) → Fin (P.nm + 1) → Fin 2 → Fin (P.m * (P.nm + 8) + 1) → Constraints F}

/-- **The leaves in the coordinate space.** If every check is 0, each leaf satisfies Jonas's
NLA relation over the unit generators, with the lifted commitments. -/
theorem LiftHyp.rel (H : LiftHyp P x t hv C) (hchk : ∀ a r b l i, leafChk P x t a r b l i = 0)
    (a : Fin (Nd P + 16)) (r : Fin (P.nm + 1)) (b : Fin 2) (l : Fin (P.m * (P.nm + 8) + 1))
    (i : Fin 13) :
    Spec.NormLinear.Rel (eg P) (Spec.tauInst (P.toSpec hv)
      (specCh (tα t a).val (tρ t a r).val (tLam t a r b l)
      (tβ t a r b).val (tδ t a r).val)
      (eg P) (eH P) (eG P) (liftCS P x t a r b l) (liftCO P x t) (liftCL P x t) (liftCR P x t a)
      (Spec.vHat (P.toSpec hv)
        (specCh (tα t a).val (tρ t a r).val (tLam t a r b l)
      (tβ t a r b).val (tδ t a r).val)
        (liftV P x t)) (tρ t a r).val (tτu t a r b l i))
      (leafWit P x.gens x.commitments (tCS t a r b l) (tCO t) (tCL t) (tCR t a)
        (tα t a).val (tρ t a r) (tLam t a r b l) (tβ t a r b).val (tδ t a r).val
        (tτ t a r b l i) (tNla t a r b l i)) := by
  obtain ⟨-, w, hrel, hY, hwit⟩ := (leaf_facts x t hv H.hacc H.hrounds H.heven a r b l i
    (C a r b l) (H.hCnew a r b l) (H.hC a r b l)).2 (H.hall a r b l i)
  have hdata := leafInputs_eq P hv (tα t a).val (tρ t a r).val (tLam t a r b l)
    (tβ t a r b).val (tδ t a r).val (tτu t a r b l i) (C a r b l) (tδ t a r).property
    (H.hCnew a r b l) (H.hC a r b l)
  simp only [tτu, Units.val_mk0] at hdata
  have hk := hchk a r b l i
  simp only [leafChk, hdata, sub_eq_zero] at hk
  -- The instances of `norm_linear::verify` over the real and the unit generators.
  set ps := psTau P (C a r b l) (tρ t a r).val (tδ t a r).val (tτu t a r b l i)
  set pn := pnTau P (C a r b l) (tδ t a r).val (tτu t a r b l i)
  set cv := cTau (C a r b l) (tβ t a r b).val (tτu t a r b l i)
  set xE := leafInst P x.gens x.commitments (tCS t a r b l) (tCO t) (tCL t) (tCR t a) cv ps pn
    (C a r b l) (tδ t a r).val (tρ t a r).val (tτu t a r b l i) (tρ t a r).property
  set xS' := leafSpecInst (unitGens P) (liftVcs P x t) (liftCS P x t a r b l) (liftCO P x t)
    (liftCL P x t) (liftCR P x t a) cv ps pn (C a r b l) (tδ t a r).val (tρ t a r).val
    (tτu t a r b l i)
  obtain ⟨hm', hk', hμ', -, hH', hG', hC'⟩ := leafSpecInst_facts P (unitGens P) (liftVcs P x t)
    (liftCS P x t a r b l) (liftCO P x t) (liftCL P x t) (liftCR P x t a) cv ps pn (C a r b l)
    (tδ t a r).val (tρ t a r).val (tτu t a r b l i)
    (by simp [unitGens])
  have hcv : cv.length = H_LEN := by simp [cv, cTau, H_LEN]
  -- The relation of the full NLA over the unit generators.
  have hrel' : NLA.Rel (toInstAt (eg P) H_LEN P.nm xS' (tρ t a r).property) w := by
    show xS'.C = _
    have hpt : (toInstAt (eg P) H_LEN P.nm xS' (tρ t a r).property).point
        ((toInstAt (eg P) H_LEN P.nm xS' (tρ t a r).property).opening w) =
        toComb P (xE.opening w) := by
      have hop : (toInstAt (eg P) H_LEN P.nm xS' (tρ t a r).property).opening w =
          xE.opening w := rfl
      rw [hop, ← point_unit]
      simp only [NLA.Instance.point, toInstAt, xS', leafSpecInst, NormLinear.vInst,
        NormLinear.LazyBases.new_w, NormLinear.contract'_one, unitGens_h, unitGens_g]
    rw [hpt, hC']
    change pubPart P ps pn + _ = _
    rw [← hk, hY]
    abel
  -- Jonas's relation over the unit generators, with Rust's inputs.
  have hw : Spec.NormLinear.Rel (eg P) xS' (NLA.Bridge.ofWit w) := by
    refine (rel_iff_at (eg P) xS' (tρ t a r).property hμ' (hm'.trans hcv) hk' _).2 ?_
    convert hrel' using 2 <;> funext i <;> simp [NLA.Bridge.ofWit]
  rw [hwit]
  -- Jonas's relation with `tauInst`, as in his `leaf_extract`.
  obtain ⟨-, hcp⟩ := c_spec P hv (tα t a).val (tρ t a r).val (tLam t a r b l)
    (tβ t a r b).val (tδ t a r).val (C a r b l) (H.hC a r b l)
  have hvh : Spec.vHat (P.toSpec hv) (specCh (tα t a).val (tρ t a r).val (tLam t a r b l)
      (tβ t a r b).val (tδ t a r).val) (liftV P x t) =
      Spec.vHat (P.toSpec hv) (specCh (tα t a).val (tρ t a r).val (tLam t a r b l)
        (tβ t a r b).val (tδ t a r).val)
        fun q => ((liftVcs P x t).getD q ⟨0⟩).point := by
    simp only [Spec.vHat, CircuitParams.M_toSpec]
    congr 1
    exact sum_congr rfl fun q hq => by rw [liftVcs_getD P x t q (mem_range.1 hq)]
  have heH : (fun k => (unitGens (F := F) P).h_vec.getD k 0) = eH P := funext (unitGens_h P)
  have heG : (fun k => (unitGens (F := F) P).g_vec.getD k 0) = eG P := funext (unitGens_g P)
  have hcomb := combined_eq (unitGens P) P hv (by simp [unitGens])
    (tα t a).val (tρ t a r).val (tLam t a r b l) (tβ t a r b).val (tδ t a r).val
    (tτu t a r b l i) (C a r b l)
    (H.hC a r b l) (liftVcs P x t) (liftVcs_length P x t) (liftCS P x t a r b l) (liftCO P x t)
    (liftCL P x t) (liftCR P x t a)
  rw [heG] at hcomb
  rw [hvh]
  refine rel_congr (h := hw) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hC']; exact hcomb
  · exact hm'.trans hcv
  · exact hk'
  · rfl
  · intro k hk
    have hk : k < H_LEN := by rw [hm', hcv] at hk; exact hk
    simp only [xS', leafSpecInst, NormLinear.vInst, Spec.tauInst]
    exact (getD_map_range _ hk).trans (by rw [hcp k hk])
  · intro k _; exact (hH' k).trans (unitGens_h P k)
  · intro k _; exact (hG' k).trans (unitGens_g P k)

/-- The slots of the digits of input `i` are below `N_d`. -/
theorem slot_lt (P : CircuitParams) (i : ℕ) (hi : i < P.m) (s : ℕ) (hs : s < P.d) :
    i * P.d + s < Nd P := by
  have := Nat.mul_le_mul_right P.d (show i + 1 ≤ P.m by omega)
  have : (i + 1) * P.d = i * P.d + P.d := by ring
  simp only [Nd]
  omega

/-- **The inputs open in the range.** If every check is 0, the values and the blindings of
`rangeExtract` open every input. -/
theorem LiftHyp.opens (H : LiftHyp P x t hv C) (hchk : ∀ a r b l i, leafChk P x t a r b l i = 0)
    (hM : 0 < P.m) (h16 : 16 ^ P.d = 2 ^ x.range.bits) :
    OpensInRange x (rangeExtract P x t).value (rangeExtract P x t).blinding := by
  set S := P.toSpec hv
  set n0 := liftN P x t
  set h0 : ℕ → F := fun k => if h : k < H_LEN then (liftCL P x t).2.1 ⟨k, h⟩ else 0
  have hcL : liftCL P x t = Spec.commit S (eg P) (eH P) (eG P) (liftCL P x t).1 h0 n0 := by
    rw [commit_unit]
    ext k
    · rfl
    · simp [h0, k.isLt]
    · simp [n0, liftN, k.isLt]
  have hchar : ∀ m : ℕ, 0 < m → m ≤ S.Nd → (m : F) ≠ 0 := fun m hm hle =>
    x.largeChar.cast_ne_zero m hm (by simp only [S, Spec.Params.Nd, CircuitParams.M_toSpec,
      CircuitParams.D_toSpec] at hle; unfold Nd; omega)
  obtain ⟨hd, hV⟩ := Spec.circuit_extract_digits S (eg P) (eH P) (eG P) (not_relation_unit hv)
    H.h2 hchar hM (liftV P x t) (liftCO P x t) (liftCL P x t) (liftCR P x t) (liftCS P x t)
    (fun a => (tα t a).val) (fun a r => (tρ t a r).val * (tρ t a r).val)
    (fun a r => (tδ t a r).val) (fun a r => (tρ t a r).val) (fun a r b => (tβ t a r b).val)
    (tLam t) (tτu t)
    (fun a a' e => by
      by_contra hne
      exact t.challenges.property a a' hne (Subtype.ext e))
    (fun a r r' e => by
      by_contra hne
      exact (t.children a).challenges.property r r' hne (by rw [sq, sq]; exact e))
    (fun a r b b' e => by
      by_contra hne
      exact (((t.children a).children r).children 0).challenges.property b b' hne
        (Subtype.ext e))
    (fun a r b l l' e => by
      by_contra hne
      exact ((((t.children a).children r).children 0).children b).challenges.property l l' hne e)
    (fun a r b l i i' e => by
      by_contra hne
      exact (((((t.children a).children r).children 0).children b).children l).challenges.property
        i i' hne (Subtype.ext (congrArg Units.val e)))
    (fun a => (tα t a).property)
    (fun a r => mul_ne_zero (tρ t a r).property (tρ t a r).property)
    (fun a r => (tδ t a r).property)
    (fun a r b l i => leafWit P x.gens x.commitments (tCS t a r b l) (tCO t) (tCL t) (tCR t a)
      (tα t a).val (tρ t a r) (tLam t a r b l) (tβ t a r b).val (tδ t a r).val
      (tτ t a r b l i) (tNla t a r b l i))
    (fun a r b l i => H.rel hchk a r b l i) (liftCL P x t).1 h0 n0 hcL
  obtain ⟨-, -, -, -, hlift⟩ := H.lift
  rw [opensInRange_iff]
  intro i hi
  have hi' : i < P.m := H.hpm ▸ hi
  obtain ⟨s, hs⟩ := hV i hi'
  have hdig : ∀ q < P.d, digitOf (n0 (i * P.d + q)) < 16 ∧
      (digitOf (n0 (i * P.d + q)) : F) = n0 (i * P.d + q) := fun q hq =>
    digitOf_spec _ (hd _ (slot_lt P i hi' q hq))
  -- The value is the sum of the digits.
  have hval : ((rangeExtract P x t).value i : F) =
      ∑ q ∈ range S.D, 16 ^ q * n0 (i * S.D + q) := by
    simp only [rangeExtract, S, CircuitParams.D_toSpec]
    push_cast
    exact sum_congr rfl fun q hq => by rw [(hdig q (mem_range.1 hq)).2]
  -- The blinding is the `h_vec[0]` coordinate.
  have hbl : (rangeExtract P x t).blinding i = s := by
    simp only [rangeExtract, hs]
    simp [eg, eH_h]
  refine ⟨?_, ?_⟩
  · rw [← h16]
    exact Spec.digits_lt _ _ fun q hq => (hdig q hq).1
  · rw [← List.getD_eq_getElem _ ⟨0⟩ hi, ← hlift i hi', hs, hval, hbl, map_add, map_smul,
      map_smul, combMap_eg, combMap_eH x.gens x.setup.hHLen, x.setup.hValueBase,
      x.setup.hBlindingBase]

end Lift

/-! ## The theorem -/

/-- **Soundness of the range proof.** -/
theorem range_sound : RangeSoundness (F := F) (E := E) (fun P => rangeExtract P) := by
  intro P x t hacc
  change OpensInRange x _ _ ∨ IsGeneratorLink x (rangeLink P x t)
  -- No input: nothing to open.
  by_cases hm0 : x.commitments.length = 0
  · exact Or.inl ((opensInRange_iff x _ _).2 fun i hi => absurd hi (by omega))
  obtain ⟨P', hpn, hv, -, hpm, h16⟩ := Bppp.RangeProof.params_new x.range x.commitments.length hm0
  obtain rfl : P = P' := by
    have h := x.setup.hParams
    rw [hpn] at h
    exact (Except.ok.inj h).symm
  have hshape : P.nm = next_power_of_two (max P.n_d BASE) := by
    have hparams := x.setup.hParams
    unfold CircuitParams.new at hparams
    split_ifs at hparams
    rw [← Except.ok.inj hparams]
  have hrounds : NLA.numRounds H_LEN P.nm = numNlaRounds P := NLA.numRounds_eq_proof_shape _ _
  have heven : NLA.EvenNorms H_LEN P.nm := by rw [hshape]; exact NLA.evenNorms_nm _
  have h2 : (2 : F) ≠ 0 := by
    exact_mod_cast x.largeChar.cast_ne_zero 2 (by norm_num) (by unfold Nd; omega)
  choose C hCnew hC using fun a r b l =>
    Constraints.new_correct P (tα t a).val ((tρ t a r).val * (tρ t a r).val) (tLam t a r b l) hv
      (mul_ne_zero (tρ t a r).property (tρ t a r).property) (tα t a).property
  have hleaf := fun a r b l i => leaf_facts x t hv hacc hrounds heven a r b l i (C a r b l)
    (hCnew a r b l) (hC a r b l)
  -- 1. A nonzero NLA link.
  by_cases hL : firstNZ (nlaLinks P x t) ≠ 0
  · right
    unfold rangeLink
    refine (isGeneratorLink_iff (x : RangeStatement F E P) _).2 ?_
    rw [ite_cond_eq_true _ _ (eq_true hL)]
    refine ⟨hL, ?_⟩
    obtain ⟨⟨a, r, b, l, i⟩, -, e⟩ := List.mem_map.1 (firstNZ_mem _ hL)
    rw [show firstNZ (nlaLinks P x t) = (leafV P x t a r b l i).1 from e.symm]
    exact (hleaf a r b l i).1
  have hall : ∀ a r b l i, (leafV P x t a r b l i).1 = 0 := fun a r b l i =>
    (firstNZ_eq_zero _).1 (not_not.1 hL) _
      (List.mem_map.2 ⟨(a, r, b, l, i), mem_allIdx P a r b l i, rfl⟩)
  have H : LiftHyp P x t hv C := ⟨hacc, hrounds, heven, hpm.symm, h2, hCnew, hC, hall⟩
  -- 2. A nonzero check.
  by_cases hK : firstNZ (leafChks P x t) ≠ 0
  · right
    unfold rangeLink
    refine (isGeneratorLink_iff (x : RangeStatement F E P) _).2 ?_
    rw [ite_cond_eq_false _ _ (eq_false hL)]
    refine ⟨hK, ?_⟩
    obtain ⟨⟨a, r, b, l, i⟩, -, e⟩ := List.mem_map.1 (firstNZ_mem _ hK)
    rw [show firstNZ (leafChks P x t) = leafChk P x t a r b l i from e.symm]
    exact H.chk a r b l i
  -- 3. All checks are 0: the inputs open in the range.
  have hchk : ∀ a r b l i, leafChk P x t a r b l i = 0 := fun a r b l i =>
    (firstNZ_eq_zero _).1 (not_not.1 hK) _
      (List.mem_map.2 ⟨(a, r, b, l, i), mem_allIdx P a r b l i, rfl⟩)
  exact Or.inl (H.opens hchk (by omega) h16)

end Audit.RangeProof.Sound
