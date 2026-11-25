import Audit.RangeProof.Extract

/-!
# The `τ` level of the range extractor

This file names the opening and the candidate link of a `τ` node, and proves the invariant of
the level (see `Audit/RangeProof/Extract.lean`).

Why it exists:
- Jonas's `extract_tau` (`Bppp/Spec/CircuitSoundness.lean`) ends in `(∃ wo, …) ∨ Relation`.
  Both parts are `∃`, so his lemma does not give an extractor.
- `tau_spec` has the same hypotheses. Its conclusion names `tauOpening` and `tauLink`.

How it works:
1. `tauCoeffs`: at each of the 13 `τ`, the NLA witness gives an opening of `τ • Y(τ)`, with
   `Y(τ) = τ⁻¹ C_S + δ C_O + τ C_L + τ² C_R + τ³ V̂`. This is Jonas's `(ys, yh, yn)`.
2. `tauZ`: interpolation at the first 5 `τ` gives openings of `C_S`, `δ C_O`, `C_L`, `C_R`, `V̂`.
   This is Jonas's `(zs, zh, zn)`, with `vinv` in place of his `∃ W`.
3. `tauCurve x`: the opening of `x • Y(x)` that these 5 openings give.
4. `tauLink`: the first nonzero difference `tauCurve (τ k) - y k`. Each difference opens zero.
5. `tauOpening`: Jonas's `wo`, read from `tauZ`.
6. If `tauLink` is 0, then the curve agrees with all 13 openings. Then Jonas's argument shows
   `f(T) = 0` for `tauOpening`.

Assumptions:
- The level takes the scalars `y` as an argument, with `hy : y k = tauCoeffs …`. `tauCoeffs`
  uses Laurent polynomials, so it is noncomputable. The extractor must compute `y` in another
  way, for example from the scalars of the Rust verifier.
- The proof is Jonas's proof of `extract_tau`, with the named parts in place of `∃`.
-/

namespace Audit.RangeProof

open Finset Bppp Bppp.Spec LaurentPolynomial

variable {F : Type} [Field F]

variable (F) in
/-- The coordinates of an opening, indexed by `ℕ`: on `g`, on `H` and on `G`. -/
structure Coeffs where
  s : F
  h : ℕ → F
  n : ℕ → F

section Defs

/-- Jonas's opening `(ys, yh, yn)` of `τ • Y(τ)`, from an NLA witness `w` at `τ`. -/
noncomputable def tauCoeffs (P : Params) (ch : Challenges F) (τ : Fˣ)
    (w : NormLinear.Witness F) : Coeffs F where
  s := (τ : F) * (NormLinear.ip 8 (fun s => evalAt τ (Spec.c P ch s)) w.ℓ +
    NormLinear.wip P.nm ch.μ w.n w.n - evalAt τ (ps P ch))
  h j := (τ : F) * w.ℓ j
  n j := (τ : F) * (w.n j - evalAt τ (pn P ch j))

/-- The indices of the first five `τ`. -/
def tauFirst : Fin 5 → Fin 13 := Fin.castLE (by norm_num)

/-- The openings of `C_S`, `δ C_O`, `C_L`, `C_R`, `V̂`: interpolation at the first five `τ`. -/
def tauZ (τ : Fin 13 → F) (y : Fin 13 → Coeffs F) (b : Fin 5) : Coeffs F where
  s := ∑ k, vinv (fun k => τ (tauFirst k)) b k * (y (tauFirst k)).s
  h j := ∑ k, vinv (fun k => τ (tauFirst k)) b k * (y (tauFirst k)).h j
  n j := ∑ k, vinv (fun k => τ (tauFirst k)) b k * (y (tauFirst k)).n j

/-- The opening of `x • Y(x)` that `tauZ` gives. -/
def tauCurve (τ : Fin 13 → F) (y : Fin 13 → Coeffs F) (x : F) : Coeffs F where
  s := ∑ b : Fin 5, x ^ (b : ℕ) * (tauZ τ y b).s
  h j := ∑ b : Fin 5, x ^ (b : ℕ) * (tauZ τ y b).h j
  n j := ∑ b : Fin 5, x ^ (b : ℕ) * (tauZ τ y b).n j

/-- The candidate links of the level: at each `τ`, the curve minus the given opening. -/
def tauCandidates (nm : ℕ) (τ : Fin 13 → F) (y : Fin 13 → Coeffs F) :
    List (NLA.Opening F H_LEN nm) :=
  (List.finRange 13).map fun k =>
    toLink nm ((tauCurve τ y (τ k)).s - (y k).s) (fun j => (tauCurve τ y (τ k)).h j - (y k).h j)
      (fun j => (tauCurve τ y (τ k)).n j - (y k).n j)

/-- The link of the level: the first nonzero candidate, or 0. -/
def tauLink [DecidableEq F] (nm : ℕ) (τ : Fin 13 → F) (y : Fin 13 → Coeffs F) :
    NLA.Opening F H_LEN nm :=
  firstLink (tauCandidates nm τ y)

/-- Jonas's `op`: the `H`-coordinates of an opening, with `σ` moved into slot 0, scaled. -/
def tauOp (z : Fin 5 → Coeffs F) (c : F) (b : Fin 5) (j : ℕ) : F :=
  c * if j = 0 then (z b).s else (z b).h (j - 1)

/-- Jonas's `wo`: the opening of `C_S`, `C_O`, `C_L`, `C_R`, `V̂` that `tauZ` gives. -/
def tauOpening (δ : F) (τ : Fin 13 → F) (y : Fin 13 → Coeffs F) : Opening F :=
  let z := tauZ τ y
  let d := δ⁻¹
  { nS := fun j => 1 * (z 0).n j, nO := fun j => d * (z 1).n j, nL := fun j => 1 * (z 2).n j,
    nR := fun j => 1 * (z 3).n j, ℓS := 1 * (z 0).h 7, rS := tauOp z 1 0, rO := tauOp z d 1,
    rL := tauOp z 1 2, rR := tauOp z 1 3, vhat := tauOp z 1 4 0, rV := tauOp z 1 4,
    ℓV := 1 * (z 4).h 7, ℓO := d * (z 1).h 7, ℓL := 1 * (z 2).h 7, ℓR := 1 * (z 3).h 7,
    nV := fun j => 1 * (z 4).n j }

end Defs

section Tau

variable {E : Type} [AddCommGroup E] [Module F E] (P : Params) (ch : Challenges F) (g : E)
  (H G : ℕ → E)

/-- The conclusion of Jonas's `extract_tau` for the opening `wo`. -/
def TauOpens (cS cO cL cR V : E) (wo : Opening F) : Prop :=
  f P ch wo = 0 ∧ cS = Spec.cS P g H G wo ∧ cO = Spec.cO P g H G wo ∧
    cL = Spec.cL P g H G wo ∧ cR = Spec.cR P g H G wo ∧
    V = commit P g H G wo.vhat (lin wo.rV wo.ℓV) wo.nV

variable [DecidableEq F]

/-- **The `τ` level.** The hypotheses of Jonas's `extract_tau`. `tauLink` opens zero. If it is
0, then `tauOpening` satisfies the conclusion of `extract_tau`. -/
theorem tau_spec (cS cO cL cR V : E) (rho : F) (τ : Fin 13 → Fˣ) (hτ : Function.Injective τ)
    (hδ : ch.δ ≠ 0) (w : Fin 13 → NormLinear.Witness F)
    (h : ∀ k, NormLinear.Rel g (tauInst P ch g H G cS cO cL cR V rho (τ k)) (w k))
    (y : Fin 13 → Coeffs F) (hy : ∀ k, y k = tauCoeffs P ch (τ k) (w k)) :
    linkPoint g H G (tauLink P.nm (fun k => (τ k : F)) y) = 0 ∧
      (tauLink P.nm (fun k => (τ k : F)) y = 0 →
        TauOpens P ch g H G cS cO cL cR V (tauOpening ch.δ (fun k => (τ k : F)) y)) := by
  set t13 : Fin 13 → F := fun k => (τ k : F)
  -- The openings `y k` of `τ • Y(τ)`.
  set Zp : Fin 5 → E := ![cS, ch.δ • cO, cL, cR, V]
  have hpoly : ∀ t : Fˣ, (t : F) • ((t : F) ^ (-1 : ℤ) • cS + ch.δ • cO + (t : F) • cL +
      (t : F) ^ 2 • cR + (t : F) ^ 3 • V) = ∑ j : Fin 5, (t : F) ^ (j : ℕ) • Zp j := fun t => by
    have e : (t : F) * (t : F) ^ (-1 : ℤ) = 1 := by
      rw [zpow_neg_one]; exact mul_inv_cancel₀ t.ne_zero
    simp only [Fin.sum_univ_five, Zp, smul_add, smul_smul, e, one_smul]
    simp
    module
  have hY : ∀ k, commit P g H G (y k).s (y k).h (y k).n =
      ∑ j : Fin 5, (τ k : F) ^ (j : ℕ) • Zp j := by
    intro k
    rw [hy k, ← hpoly]
    have hk := h k
    simp only [NormLinear.Rel, tauInst, combined] at hk
    have hun : commit P g H G (NormLinear.ip 8 (fun s => evalAt (τ k) (Spec.c P ch s)) (w k).ℓ +
        NormLinear.wip P.nm ch.μ (w k).n (w k).n - evalAt (τ k) (ps P ch)) (w k).ℓ
        (fun j => (w k).n j - evalAt (τ k) (pn P ch j)) =
        (τ k : F) ^ (-1 : ℤ) • cS + ch.δ • cO + (τ k : F) • cL + (τ k : F) ^ 2 • cR +
          (τ k : F) ^ 3 • V := by
      have e : commit P g H G (NormLinear.ip 8 (fun s => evalAt (τ k) (Spec.c P ch s)) (w k).ℓ +
          NormLinear.wip P.nm ch.μ (w k).n (w k).n - evalAt (τ k) (ps P ch)) (w k).ℓ
          (fun j => (w k).n j - evalAt (τ k) (pn P ch j)) =
          ((NormLinear.ip 8 (fun s => evalAt (τ k) (Spec.c P ch s)) (w k).ℓ +
            NormLinear.wip P.nm ch.μ (w k).n (w k).n) • g + NormLinear.msm 8 (w k).ℓ H +
            NormLinear.msm P.nm (w k).n G) -
          (evalAt (τ k) (ps P ch) • g +
            NormLinear.msm P.nm (fun j => evalAt (τ k) (pn P ch j)) G) := by
        simp only [commit, NormLinear.msm, sub_smul, sum_sub_distrib]; abel
      rw [e, ← hk]; abel
    exact (commit_smul P g H G (τ k : F) _ _ _).trans (by rw [hun])
  -- `tauZ` opens `C_S, δC_O, C_L, C_R, V̂`.
  set ι : Fin 5 → Fin 13 := tauFirst
  have hι : Function.Injective ι := Fin.castLE_injective _
  set t : Fin 5 → F := fun k => (τ (ι k) : F)
  have ht : Function.Injective t := fun a b e => hι (hτ (Units.ext e))
  obtain ⟨hW1, -⟩ := vinv_spec t ht
  set W := vinv t
  set zs : Fin 5 → F := fun b => ∑ k, W b k * (y (ι k)).s
  set zh : Fin 5 → ℕ → F := fun b j => ∑ k, W b k * (y (ι k)).h j
  set zn : Fin 5 → ℕ → F := fun b j => ∑ k, W b k * (y (ι k)).n j
  have hZ : ∀ b, commit P g H G (zs b) (zh b) (zn b) = Zp b := fun b => by
    rw [commit_sum]
    simp only [hY, smul_sum, smul_smul]
    rw [sum_comm]
    simp only [← sum_smul]
    have : ∀ j : Fin 5, ∑ k, W b k * (τ (ι k) : F) ^ (j : ℕ) = if b = j then 1 else 0 :=
      fun j => hW1 b j
    simp only [this, ite_smul, one_smul, zero_smul, sum_ite_eq, mem_univ, ite_true]
  -- `tauCurve x` opens `x • Y(x)`.
  set us : F → F := fun x => ∑ b : Fin 5, x ^ (b : ℕ) * zs b
  set uh : F → ℕ → F := fun x j => ∑ b : Fin 5, x ^ (b : ℕ) * zh b j
  set un : F → ℕ → F := fun x j => ∑ b : Fin 5, x ^ (b : ℕ) * zn b j
  have hu : ∀ x : F, commit P g H G (us x) (uh x) (un x) = ∑ j : Fin 5, x ^ (j : ℕ) • Zp j :=
    fun x => by rw [commit_sum]; simp only [hZ]
  -- Each candidate opens zero, so `tauLink` opens zero.
  have hL : ∀ o ∈ tauCandidates P.nm t13 y, linkPoint g H G o = 0 := by
    intro o ho
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 ho
    rw [linkPoint_toLink]
    exact (commit_sub P g H G _ _ _ _ _ _).trans (by
      show commit P g H G (us (τ k)) (uh (τ k)) (un (τ k)) - _ = 0
      rw [hu, hY, sub_self])
  obtain ⟨hp, hz⟩ := firstLink_spec (fun o => linkPoint g H G o = 0) _
    (by change (0 : F) • g + NLA.msm 0 _ + NLA.msm 0 _ = 0; simp [NLA.msm]) hL
  refine ⟨hp, fun h0 => ?_⟩
  -- If `tauLink` is 0, then the curve agrees with the openings at all 13 `τ`.
  have hall : ∀ k, us (τ k) = (y k).s ∧ (∀ j < 8, uh (τ k) j = (y k).h j) ∧
      (∀ j < P.nm, un (τ k) j = (y k).n j) := fun k => by
    have := toLink_eq_zero.1 (hz h0 _ (List.mem_map.2 ⟨k, List.mem_finRange k, rfl⟩))
    exact ⟨sub_eq_zero.1 this.1, fun j hj => sub_eq_zero.1 (this.2.1 j hj),
      fun j hj => sub_eq_zero.1 (this.2.2 j hj)⟩
  -- The rest is Jonas's proof of `extract_tau`, with `wo = tauOpening`.
  set op : F → Fin 5 → ℕ → F := fun c b j => c * if j = 0 then zs b else zh b (j - 1)
  have hop : ∀ c b, commit P g H G (op c b 0) (lin (op c b) (c * zh b 7)) (fun j => c * zn b j) =
      c • Zp b := fun c b => by
    rw [← hZ, ← commit_smul]
    exact commit_congr P g H G _ (fun j hj => lin_shift c _ _ j hj) (fun _ _ => rfl)
  set d := ch.δ⁻¹
  set wo : Opening F := {
    nS := fun j => 1 * zn 0 j, nO := fun j => d * zn 1 j, nL := fun j => 1 * zn 2 j,
    nR := fun j => 1 * zn 3 j, ℓS := 1 * zh 0 7, rS := op 1 0, rO := op d 1, rL := op 1 2,
    rR := op 1 3, vhat := op 1 4 0, rV := op 1 4, ℓV := 1 * zh 4 7, ℓO := d * zh 1 7,
    ℓL := 1 * zh 2 7, ℓR := 1 * zh 3 7, nV := fun j => 1 * zn 4 j } with hwo
  have hwo' : tauOpening ch.δ t13 y = wo := rfl
  rw [hwo']
  have hd : ch.δ * d = 1 := mul_inv_cancel₀ hδ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · exact ((hop 1 0).trans (one_smul _ _)).symm
  · show cO = commit P g H G (op d 1 0) (lin (op d 1) (d * zh 1 7)) (fun j => d * zn 1 j)
    rw [hop]; show cO = d • (ch.δ • cO); rw [smul_smul, mul_comm, hd, one_smul]
  · exact ((hop 1 2).trans (one_smul _ _)).symm
  · exact ((hop 1 3).trans (one_smul _ _)).symm
  · exact ((hop 1 4).trans (one_smul _ _)).symm
  -- `f` vanishes at all 13 challenges, so it is zero.
  refine laurent_zero (n := 12) (a := -2) (supp_f P ch wo) τ hτ fun k => ?_
  obtain ⟨hs, hh, hn⟩ := hall k
  rw [hy k] at hs hh hn
  have tk := (τ k).ne_zero
  have ti : (τ k : F) ^ (-1 : ℤ) * (τ k : F) = 1 := by
    rw [zpow_neg_one]; exact inv_mul_cancel₀ tk
  have e5 : ∀ y : Fin 5 → F, ∑ b : Fin 5, (τ k : F) ^ (b : ℕ) * y b =
      (τ k : F) * ((τ k : F) ^ (-1 : ℤ) * y 0 + ch.δ * (d * y 1) + (τ k : F) * y 2 +
        (τ k : F) ^ 2 * y 3 + (τ k : F) ^ 3 * y 4) := fun y => by
    simp only [Fin.sum_univ_five, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
    have : ((3 : Fin 5) : ℕ) = 3 := rfl
    have : ((4 : Fin 5) : ℕ) = 4 := rfl
    simp only [*]
    linear_combination -(y 0) * ti - (τ k : F) * y 1 * hd
  have hσ : evalAt (τ k) (σ P ch wo) = NormLinear.ip 8 (fun s => evalAt (τ k) (Spec.c P ch s))
      (w k).ℓ + NormLinear.wip P.nm ch.μ (w k).n (w k).n := by
    have h1 : (τ k : F) * _ = (τ k : F) * _ := (e5 zs).symm.trans hs
    have h2 := mul_left_cancel₀ tk h1
    rw [eval_σ]
    simp only [wo, op, ite_true, one_mul]
    linear_combination h2
  have hℓ : ∀ s < 8, evalAt (τ k) (ℓ ch wo s) = (w k).ℓ s := fun s hs8 => by
    have hl : ∀ c b, lin (op c b) (c * zh b 7) s = c * zh b s := fun c b => lin_shift c _ _ s hs8
    have h1 : (τ k : F) * _ = (τ k : F) * _ := (e5 fun b => zh b s).symm.trans (hh s hs8)
    have h2 := mul_left_cancel₀ tk h1
    rw [eval_ℓ _ _ _ _ hs8]
    simp only [wo]
    rw [hl, hl, hl, hl, hl]
    linear_combination h2
  have hnk : ∀ j < P.nm, evalAt (τ k) (n P ch wo j) = (w k).n j := fun j hj => by
    have h1 : (τ k : F) * _ = (τ k : F) * _ := (e5 fun b => zn b j).symm.trans (hn j hj)
    have h2 := mul_left_cancel₀ tk h1
    rw [eval_n]
    simp only [wo, one_mul]
    linear_combination h2
  have s1 : ∑ s ∈ range 8, evalAt (τ k) (c P ch s) * evalAt (τ k) (ℓ ch wo s) =
      NormLinear.ip 8 (fun s => evalAt (τ k) (Spec.c P ch s)) (w k).ℓ :=
    sum_congr rfl fun s hs8 => by rw [hℓ s (mem_range.1 hs8)]
  have s2 : ∑ j ∈ range P.nm, ch.μ ^ (j + 1) * (evalAt (τ k) (n P ch wo j) *
      evalAt (τ k) (n P ch wo j)) = NormLinear.wip P.nm ch.μ (w k).n (w k).n :=
    sum_congr rfl fun j hj => by rw [hnk j (mem_range.1 hj)]
  rw [eval_f, hσ, s1, s2]
  ring

/-- The `τ` level in the form of `RangeSoundness`: `tauOpening` satisfies the conclusion of
`extract_tau`, or `tauLink` is a link between the generators. -/
theorem tau_sound (cS cO cL cR V : E) (rho : F) (τ : Fin 13 → Fˣ) (hτ : Function.Injective τ)
    (hδ : ch.δ ≠ 0) (w : Fin 13 → NormLinear.Witness F)
    (h : ∀ k, NormLinear.Rel g (tauInst P ch g H G cS cO cL cR V rho (τ k)) (w k))
    (y : Fin 13 → Coeffs F) (hy : ∀ k, y k = tauCoeffs P ch (τ k) (w k)) :
    TauOpens P ch g H G cS cO cL cR V (tauOpening ch.δ (fun k => (τ k : F)) y) ∨
      NLA.IsGeneratorLink g (fun i => H i) (fun j => G j)
        (tauLink P.nm (fun k => (τ k : F)) y) := by
  obtain ⟨hp, himp⟩ := tau_spec P ch g H G cS cO cL cR V rho τ hτ hδ w h y hy
  by_cases h0 : tauLink P.nm (fun k => (τ k : F)) y = 0
  · exact Or.inl (himp h0)
  · exact Or.inr ⟨h0, hp⟩

end Tau

end Audit.RangeProof
