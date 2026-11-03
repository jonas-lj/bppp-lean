import Bppp.Proofs.Witness
import Bppp.Proofs.Laurent
import Bppp.Spec.Commitment
import Bppp.Spec.Completeness

/-!
# The Laurent polynomials of `circuit.rs`

`coordinates_without_c_s`, `c` and `error_polynomial` compute the Laurent vectors (26) and the
error polynomial (28) of `Spec`, for the honest prover `specHonest`.
-/

open Finset LaurentPolynomial

namespace Bppp

variable {F : Type} [Field F] [DecidableEq F]

set_option linter.unusedSectionVars false

namespace Circuit

open Laurent

variable (params : CircuitParams) (hv : params.Valid) (rng : Randomness F) (values : List ℕ)
  (blindings : List F) (alpha rho lambda beta delta : F)

/-- The challenges of `Spec`. -/
def specCh : Spec.Challenges F := ⟨alpha, rho * rho, lambda, beta, delta⟩

theorem getD_vec_eq {L : ℕ} {v : List F} (hl : v.length = L) {f : ℕ → F} (hf : ∀ k < L, v.getD k 0 = f k)
    (k : ℕ) (hk : k < L) : v.getD k 0 = f k := hf k hk

/-! ## `h_coordinates` -/

theorem length_h_coordinates {r : List F} (h : r.length = H_LEN) : (h_coordinates r).length = H_LEN := by
  simp [h_coordinates, h, H_LEN]

theorem getD_h_coordinates {r : List F} (h : r.length = H_LEN) (s : ℕ) :
    (h_coordinates r).getD s 0 = Spec.lin (fun j => r.getD j 0) 0 s := by
  unfold h_coordinates Spec.lin
  split_ifs with hs
  · rw [NormLinear.getD_append_lt _ _ (by simp [h, H_LEN]; omega), NormLinear.getD_drop', add_comm]
  · rcases (show s = 7 ∨ 8 ≤ s by omega) with rfl | hs8
    · rw [NormLinear.getD_append_ge _ _ (by simp [h, H_LEN])]; simp [h, H_LEN]
    · rw [getD_eq_zero_of_le (by simp [h, H_LEN]; omega)]

theorem length_blinding_vector (rng' : ℕ → F) (zeros : List ℕ) :
    (blinding_vector rng' zeros).length = H_LEN := by simp [blinding_vector]

/-! ## The public part `p_n` -/

variable (C : Constraints F) (hC : Constraints.Correct params alpha (rho * rho) lambda C hv)

include hC in
theorem uniform_p_n : Uniform params.nm (C.p_n delta⁻¹) := by
  refine uniform_new (by simp [Constraints.p_n]) fun c hc => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp [hC.cn_v, hC.cn_r, hC.cn_l, hC.cn_o, length_vec_scalar_mul]

theorem getD_map_range (f : ℕ → F) {N k : ℕ} (hk : k < N) : ((List.range N).map f).getD k 0 = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl

include hC in
theorem toPolys_p_n (k : ℕ) (hk : k < params.nm) :
    (C.p_n delta⁻¹).toPolys k = Spec.pn (params.toSpec hv) (specCh alpha rho lambda beta delta) k := by
  simp only [Constraints.p_n, toPolys_new, List.length_cons, List.length_nil, sum_range_succ,
    sum_range_zero, zero_add, List.getD_cons_zero, List.getD_cons_succ, getD_vec_scalar_mul,
    hC.cn_v, hC.cn_r, hC.cn_l, hC.cn_o, getD_map_range _ hk, Spec.pn]
  push_cast
  rfl

/-! ## `n(T)` -/

variable (r : ℕ → F) (n_r : List F)

/-- The opening of `Spec` for the blinding `r` of `C_S`. -/
noncomputable abbrev specOpening : Spec.Opening F :=
  (specHonest rng values blindings).opening (params.toSpec hv) (specCh alpha rho lambda beta delta) r

include hC in
theorem n_spec (hlen : values.length = params.m) (hnr_len : n_r.length = params.nm)
    (hnr : ∀ k, n_r.getD k 0 =
      (specOpening params hv rng values blindings alpha rho lambda beta delta r).nR k) :
    let n := (coordinates_without_c_s params C (Witness.new params rng values blindings) n_r delta
      delta⁻¹).2.2
    Uniform params.nm n ∧ ∀ k < params.nm, n.toPolys k =
      Spec.n (params.toSpec hv) (specCh alpha rho lambda beta delta)
        (specOpening params hv rng values blindings alpha rho lambda beta delta r) k := by
  intro n
  have hn : n = Laurent.new (-1) [(List.range params.nm).map rng.n_s,
      vec_scalar_mul delta (Witness.new params rng values blindings : Witness F).n_o,
      (Witness.new params rng values blindings : Witness F).n_l, n_r,
      List.replicate params.nm 0] + C.p_n delta⁻¹ := rfl
  have hW : Uniform params.nm (Laurent.new (-1) [(List.range params.nm).map rng.n_s,
      vec_scalar_mul delta (Witness.new params rng values blindings : Witness F).n_o,
      (Witness.new params rng values blindings : Witness F).n_l, n_r,
      List.replicate params.nm 0]) := by
    refine uniform_new (by simp) fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      simp [Witness.new, length_vec_scalar_mul, length_pad_to, hnr_len]
  rw [hn]
  refine ⟨uniform_add hW (uniform_p_n params hv alpha rho lambda delta C hC), fun k hk => ?_⟩
  rw [toPolys_add hW (uniform_p_n params hv alpha rho lambda delta C hC),
    toPolys_p_n params hv alpha rho lambda beta delta C hC k hk]
  simp only [toPolys_new, List.length_cons, List.length_nil, sum_range_succ, sum_range_zero,
    zero_add, List.getD_cons_zero, List.getD_cons_succ, getD_vec_scalar_mul, getD_map_range _ hk,
    getD_n_l params hv rng values blindings hlen, getD_n_o params hv rng values blindings hlen,
    hnr, Spec.n]
  rw [show (List.replicate params.nm (0 : F)).getD k 0 = 0 by
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split_ifs <;> rfl]
  simp only [specOpening, Spec.Honest.opening, specHonest, specCh]
  push_cast
  ring_nf

/-! ## `ℓ(T)` and `σ(T)` -/

include hC in
theorem input_weights_eq : C.input_weights = (List.range params.m).map (lambda ^ ·) := by
  rw [Constraints.input_weights, hC.lambdas, List.length_map, List.length_range,
    Nat.add_sub_cancel, ← List.map_take, List.take_range, min_eq_left (by omega)]

include hC in
/-- `2 Σ_i λ^i x_i`, the input aggregation of `coordinates_without_c_s`. -/
theorem inner_product_weights (xs : List F) (hxs : xs.length = params.m) :
    inner_product (C.input_weights.map (2 * ·)) xs =
      2 * ∑ i ∈ range params.m, lambda ^ i * xs.getD i 0 := by
  rw [input_weights_eq params hv alpha rho lambda C hC, inner_product_eq, List.map_map]
  simp only [List.length_map, List.length_range, hxs, min_self, mul_sum]
  exact sum_congr rfl fun i hi => by
    rw [getD_map_range _ (mem_range.1 hi)]; simp only [Function.comp_apply]; ring

theorem getD_v_hat_h (x y : F) (s : ℕ) :
    (((List.replicate H_LEN (0 : F)).set 0 x).set (H_LEN - 1) y).getD s 0 =
      if s = 0 then x else if s = 7 then y else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getElem?_set, List.getElem?_replicate]
  simp only [H_LEN, List.length_set, List.length_replicate]
  by_cases h0 : s = 0
  · subst h0; simp
  · by_cases h7 : s = 7
    · subst h7; simp
    · by_cases h8 : s < 8 <;> simp [h0, h7, h8, Ne.symm h0, Ne.symm h7]

include hC in
/-- `ℓ(T)` without the term `T⁻¹(r_{S,1:7} ‖ ℓ_S)` of `C_S`. -/
theorem l_base (hb : blindings.length = params.m) :
    let l := (coordinates_without_c_s params C (Witness.new params rng values blindings) n_r delta
      delta⁻¹).2.1
    Uniform H_LEN l ∧ ∀ s < H_LEN, l.toPolys s =
      Spec.ℓ (specCh alpha rho lambda beta delta)
        (specOpening params hv rng values blindings alpha rho lambda beta delta r) s -
      mono (-1) (if s < 7 then r (s + 1) else rng.l_s) := by
  intro l
  have hr : ∀ zeros : List ℕ, ∀ rng' : ℕ → F, (blinding_vector rng' zeros).length = H_LEN :=
    fun _ _ => length_blinding_vector _ _
  refine ⟨uniform_new (by simp) fun c hc => ?_, fun s hs => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;>
      simp [Witness.new, length_vec_scalar_mul, length_h_coordinates, hr, H_LEN]
  · simp only [l, coordinates_without_c_s, Witness.new, toPolys_new, List.length_cons,
      List.length_nil, sum_range_succ, sum_range_zero, zero_add, List.getD_cons_zero,
      List.getD_cons_succ, getD_vec_scalar_mul, getD_h_coordinates (hr _ _), getD_v_hat_h,
      List.zip_nil_left, List.foldl_nil,
      inner_product_weights params hv alpha rho lambda C hC blindings hb]
    simp only [specOpening, Spec.ℓ, Spec.Honest.opening, specHonest, specCh, Spec.lin]
    simp only [H_LEN] at hs
    rcases (show s < 7 ∨ s = 7 by omega) with hs7 | rfl
    · simp only [hs7, if_true, show ¬ s = 7 by omega, if_false]
      by_cases h0 : s = 0
      · subst h0; simp; ring
      · simp [h0]; ring
    · simp

theorem value_eq (hrange : ∀ v ∈ values, v < 16 ^ params.d) (i : ℕ) (hi : i < values.length) :
    ((values.getD i 0 : ℕ) : F) =
      (specHonest rng values blindings).value (params.toSpec hv) i := by
  simp only [Spec.Honest.value, specHonest, CircuitParams.D_toSpec]
  conv_lhs => rw [← sum_digits params.d (values.getD i 0) (hrange _ (getD_mem' hi 0))]
  push_cast; rfl

theorem mono_add' (p : ℤ) (x y : F) : mono p (x + y) = mono p x + mono p y := by
  simp [mono, map_add, add_mul]

theorem headD_eq_getD (v : List F) : v.headD 0 = v.getD 0 0 := by cases v <;> rfl

include hC in
/-- `σ(T)` without the term `T⁻¹ r_{S,0}` of `C_S`. -/
theorem sigma_base (hlen : values.length = params.m) (hrange : ∀ v ∈ values, v < 16 ^ params.d) :
    (coordinates_without_c_s params C (Witness.new params rng values blindings) n_r delta
      delta⁻¹).1.toPoly =
      Spec.σ (params.toSpec hv) (specCh alpha rho lambda beta delta)
        (specOpening params hv rng values blindings alpha rho lambda beta delta r) - mono (-1) (r 0) := by
  have hwip := toPoly_weighted_inner_product (uniform_p_n params hv alpha rho lambda delta C hC)
    (uniform_p_n params hv alpha rho lambda delta C hC) C.norm_weights
    (by simp [Constraints.norm_weights, hC.bar_mu])
  simp only [coordinates_without_c_s, Witness.new, toPoly_add, toPoly_new, toPoly_monomial, hwip,
    List.length_cons, List.length_nil, sum_range_succ, sum_range_zero, zero_add,
    List.getD_cons_zero, List.getD_cons_succ,
    inner_product_weights params hv alpha rho lambda C hC _ (by rw [length_to_scalars, hlen])]
  simp only [Spec.σ, Spec.ps, Spec.normμ, Constraints.p_s_constant, hC.lambda_al, hC.mu_am,
    specOpening, Spec.Honest.opening, specHonest, specCh, headD_eq_getD]
  have hpn : ∀ k ∈ range params.nm, mono 0 (C.norm_weights.getD k 0) *
      ((C.p_n delta⁻¹).toPolys k * (C.p_n delta⁻¹).toPolys k) =
      mono 0 ((rho * rho) ^ (k + 1)) * (Spec.pn (params.toSpec hv)
        (specCh alpha rho lambda beta delta) k * Spec.pn (params.toSpec hv)
        (specCh alpha rho lambda beta delta) k) := fun k hk => by
    rw [toPolys_p_n params hv alpha rho lambda beta delta C hC k (mem_range.1 hk),
      Constraints.norm_weights, hC.bar_mu, getD_map_range _ (mem_range.1 hk)]
  rw [sum_congr rfl hpn]
  have hv' : ∀ i ∈ range params.m, lambda ^ i * (to_scalars values : List F).getD i 0 =
      lambda ^ i * (specHonest rng values blindings).value (params.toSpec hv) i := fun i hi => by
    rw [getD_to_scalars, value_eq params hv rng values blindings hrange i
      (by rw [hlen]; exact mem_range.1 hi)]
  rw [sum_congr rfl hv']
  rw [show Spec.lamAl (params.toSpec hv) (Constraints.challenges alpha (rho * rho) lambda 0 0) =
      Spec.lamAl (params.toSpec hv) (specCh alpha rho lambda beta delta) from rfl,
    show Spec.muAm (params.toSpec hv) (Constraints.challenges alpha (rho * rho) lambda 0 0) =
      Spec.muAm (params.toSpec hv) (specCh alpha rho lambda beta delta) from rfl]
  simp only [CircuitParams.M_toSpec, CircuitParams.nm_toSpec, mono_add', specCh, specHonest]
  push_cast
  ring

theorem getD_set_replicate (j s : ℕ) (b : F) (hs : s < H_LEN) :
    ((List.replicate H_LEN (0 : F)).set j b).getD s 0 = if j = s then b else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getElem?_replicate]
  simp only [List.length_replicate, hs, if_true]
  split_ifs with h1 h2 <;> first | rfl | (subst h1; simp_all)

include hC in
/-- `c(T)` (24). -/
theorem c_spec : Uniform H_LEN (Circuit.c C beta) ∧ ∀ s < H_LEN, (Circuit.c C beta).toPolys s =
    Spec.c (params.toSpec hv) (specCh alpha rho lambda beta delta) s := by
  have hterms : ∀ x ∈ ((0, C.shape_h) :: CR_POWERS.zipIdx.map fun (a, j) =>
      (a, (List.replicate H_LEN (0 : F)).set j beta)), x.2.length = H_LEN := by
    intro x hx
    simp only [List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨⟨a, j⟩, _, rfl⟩
    · simp [Constraints.shape_h, hC.cl_v]
    · simp
  obtain ⟨hu, hpol⟩ := from_terms_spec _ _ hterms
  refine ⟨hu, fun s hs => ?_⟩
  rw [Circuit.c, hpol]
  simp only [CR_POWERS, List.zipIdx, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  simp only [getD_set_replicate _ s beta hs, Constraints.shape_h, hC.cl_v, getD_map_range _ hs]
  simp only [H_LEN] at hs
  simp only [Spec.c, specCh, Spec.clV, Constraints.challenges]
  interval_cases s <;> simp [Spec.e] <;> ring

/-! ## The error polynomial -/

include hC in
/-- The error polynomial before `C_S` is `f(T)` of `Spec` at `r_S = 0`, plus the term `ℓ_S` of
`C_S` adds through `c_{ℓ,V}`. -/
theorem rest_eq (hlen : values.length = params.m) (hb : blindings.length = params.m)
    (hrange : ∀ v ∈ values, v < 16 ^ params.d) (hnr_len : n_r.length = params.nm)
    (hnr : ∀ k, n_r.getD k 0 =
      (specOpening params hv rng values blindings alpha rho lambda beta delta 0).nR k) :
    (error_polynomial
      (coordinates_without_c_s params C (Witness.new params rng values blindings) n_r delta delta⁻¹).1
      (Circuit.c C beta)
      (coordinates_without_c_s params C (Witness.new params rng values blindings) n_r delta
        delta⁻¹).2.1
      (coordinates_without_c_s params C (Witness.new params rng values blindings) n_r delta
        delta⁻¹).2.2 C.norm_weights).toPoly =
      Spec.f (params.toSpec hv) (specCh alpha rho lambda beta delta)
        (specOpening params hv rng values blindings alpha rho lambda beta delta 0) +
      mono (-1) (Spec.clV (params.toSpec hv) (specCh alpha rho lambda beta delta) 7 * rng.l_s) := by
  obtain ⟨hcu, hcp⟩ := c_spec params hv alpha rho lambda beta delta C hC
  obtain ⟨hlu, hlp⟩ := l_base params hv rng values blindings alpha rho lambda beta delta C hC 0 n_r hb
  obtain ⟨hnu, hnp⟩ := n_spec params hv rng values blindings alpha rho lambda beta delta C hC 0 n_r
    hlen hnr_len hnr
  have hsig := sigma_base params hv rng values blindings alpha rho lambda beta delta C hC 0 n_r hlen
    hrange
  simp only [error_polynomial, toPoly_sub, toPoly_inner_product hcu hlu,
    toPoly_weighted_inner_product hnu hnu C.norm_weights
      (by simp [Constraints.norm_weights, hC.bar_mu])]
  rw [hsig]
  set p := coordinates_without_c_s params C (Witness.new params rng values blindings) n_r delta
    delta⁻¹
  have h1 : ∑ s ∈ range H_LEN, (Circuit.c C beta).toPolys s * p.2.1.toPolys s =
      ∑ s ∈ range H_LEN, Spec.c (params.toSpec hv) (specCh alpha rho lambda beta delta) s *
        (Spec.ℓ (specCh alpha rho lambda beta delta)
          (specOpening params hv rng values blindings alpha rho lambda beta delta 0) s -
          mono (-1) (if s < 7 then (0 : ℕ → F) (s + 1) else rng.l_s)) :=
    sum_congr rfl fun s hs => by rw [hcp s (mem_range.1 hs), hlp s (mem_range.1 hs)]
  have h2 : ∑ k ∈ range params.nm, mono 0 (C.norm_weights.getD k 0) *
      (p.2.2.toPolys k * p.2.2.toPolys k) =
      ∑ k ∈ range params.nm, mono 0 ((rho * rho) ^ (k + 1)) *
        (Spec.n (params.toSpec hv) (specCh alpha rho lambda beta delta)
          (specOpening params hv rng values blindings alpha rho lambda beta delta 0) k *
         Spec.n (params.toSpec hv) (specCh alpha rho lambda beta delta)
          (specOpening params hv rng values blindings alpha rho lambda beta delta 0) k) :=
    sum_congr rfl fun k hk => by
      rw [hnp k (mem_range.1 hk), Constraints.norm_weights, hC.bar_mu,
        getD_map_range (fun k => (rho * rho) ^ (k + 1)) (mem_range.1 hk)]
  rw [h1, h2]
  simp only [Pi.zero_apply, mono_zero, sub_zero]
  rw [show mono (-1) (Spec.clV (params.toSpec hv) (specCh alpha rho lambda beta delta) 7 * rng.l_s) =
      mono 0 (Spec.clV (params.toSpec hv) (specCh alpha rho lambda beta delta) 7) * mono (-1) rng.l_s by
      rw [mono_mul]; norm_num]
  have hc7 : Spec.c (params.toSpec hv) (specCh alpha rho lambda beta delta) 7 =
      mono 0 (Spec.clV (params.toSpec hv) (specCh alpha rho lambda beta delta) 7) := by
    simp [Spec.c]
  simp only [Spec.f, Spec.normμ, H_LEN, sum_range_succ, sum_range_zero, zero_add,
    CircuitParams.nm_toSpec, hc7, show (0 : ℕ) < 7 from by norm_num,
    show (1 : ℕ) < 7 from by norm_num, show (2 : ℕ) < 7 from by norm_num,
    show (3 : ℕ) < 7 from by norm_num, show (4 : ℕ) < 7 from by norm_num,
    show (5 : ℕ) < 7 from by norm_num, show (6 : ℕ) < 7 from by norm_num,
    show ¬ (7 : ℕ) < 7 from by norm_num, if_true, if_false, mono_zero, sub_zero]
  simp only [specCh]
  ring

/-! ## `solve_r_s` -/

/-- The blinding of `C_S` as `Spec` indexes it: `r_{S,0} = g_s` and `r_{S,j} = h_{j-1}`. -/
def rSOf (g_s : F) (h_s : List F) : ℕ → F := fun j => if j = 0 then g_s else h_s.getD (j - 1) 0

theorem e_eq (j : ℕ) (hj : j < 7) : CR_POWERS.getD j 0 = Spec.e j := by
  interval_cases j <;> rfl

include hC in
/-- `solve_r_s` solves the blinding of `C_S` as `Spec.Honest.rS` does. -/
theorem solve_r_s_eq (rest : Laurent F) (hbeta : beta ≠ 0)
    (hrest : rest.toPoly = Spec.f (params.toSpec hv) (specCh alpha rho lambda beta delta)
        (specOpening params hv rng values blindings alpha rho lambda beta delta 0) +
      mono (-1) (Spec.clV (params.toSpec hv) (specCh alpha rho lambda beta delta) 7 * rng.l_s)) :
    ∃ g_s h_s, solve_r_s C rest rng.l_s beta = .ok (g_s, h_s) ∧ h_s.length = H_LEN ∧
      h_s.getD 7 0 = rng.l_s ∧ ∀ j ≤ 7, rSOf g_s h_s j =
        (specHonest rng values blindings).rS (params.toSpec hv) (specCh alpha rho lambda beta delta) j := by
  have hinv : inverse beta = .ok beta⁻¹ := by simp [inverse, hbeta]
  obtain ⟨g, hg⟩ : ∃ g, g = Spec.f (params.toSpec hv) (specCh alpha rho lambda beta delta)
      ((specHonest rng values blindings).opening (params.toSpec hv)
        (specCh alpha rho lambda beta delta) 0) := ⟨_, rfl⟩
  rw [show specOpening params hv rng values blindings alpha rho lambda beta delta 0 =
    (specHonest rng values blindings).opening (params.toSpec hv)
      (specCh alpha rho lambda beta delta) 0 from rfl, ← hg] at hrest
  have hcoeff : ∀ p : ℤ, rest.coeff p = Bppp.coeff p g +
      if p = -1 then Spec.clV (params.toSpec hv) (specCh alpha rho lambda beta delta) 7 * rng.l_s
      else 0 := fun p => by
    rw [coeff_eq, hrest, map_add, coeff_mono]
    by_cases hp : p = -1 <;> simp [hp, eq_comm]
  refine ⟨_, _, by simp only [solve_r_s, hinv]; rfl, by simp [CR_POWERS, H_LEN],
    by simp [CR_POWERS], fun j hj => ?_⟩
  have hh : ∀ s < 7, (CR_POWERS.map (fun a => rest.coeff (a - 1) * beta⁻¹) ++ [rng.l_s]).getD s 0 =
      Bppp.coeff (Spec.e s - 1) g / beta := fun s hs => by
    rw [NormLinear.getD_append_lt _ _ (by simp [CR_POWERS]; omega), List.getD_eq_getElem?_getD,
      List.getElem?_map, ← e_eq s hs, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simp [CR_POWERS]; omega)]
    simp only [Option.map_some, Option.getD_some, hcoeff, div_eq_mul_inv]
    rw [if_neg (by interval_cases s <;> simp [CR_POWERS, Spec.e]), add_zero]
  simp only [rSOf, Spec.Honest.rS, ← hg]
  have hb : (specCh alpha rho lambda beta delta).β = beta := rfl
  rw [hb]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [if_true]
    have hCR : CR_POWERS.length = 7 := rfl
    rw [inner_product_eq, Constraints.shape_h, hC.cl_v, List.length_map, List.length_range,
      List.length_append, List.length_map, hCR, List.length_singleton,
      show min H_LEN (7 + 1) = 7 + 1 from rfl, sum_range_succ, hcoeff, if_pos rfl,
      getD_map_range _ (show 7 < H_LEN by decide),
      NormLinear.getD_append_ge _ _ (by rw [List.length_map, hCR]), List.length_map, hCR,
      Nat.sub_self, List.getD_cons_zero]
    rw [sum_congr rfl fun s hs => by
      rw [getD_map_range _ (show s < H_LEN by simp only [mem_range] at hs; simp only [H_LEN]; omega),
        hh s (mem_range.1 hs)]]
    simp only [specCh, Constraints.challenges, Spec.clV]
    ring
  · rw [if_neg (by omega), if_neg (by omega), hh (j - 1) (by omega)]

/-! ## The error polynomial vanishes -/

/-- With `r_S` from `solve_r_s`, the error polynomial vanishes. -/
theorem f_zero (halpha : ∀ j : ℕ, j < 16 → alpha + j ≠ 0) (hbeta : beta ≠ 0) (hdelta : delta ≠ 0)
    (hrho : rho ≠ 0) (g_s : F) (h_s : List F)
    (hr : ∀ j ≤ 7, rSOf g_s h_s j =
      (specHonest rng values blindings).rS (params.toSpec hv) (specCh alpha rho lambda beta delta) j) :
    Spec.f (params.toSpec hv) (specCh alpha rho lambda beta delta)
      (specOpening params hv rng values blindings alpha rho lambda beta delta (rSOf g_s h_s)) = 0 := by
  have h0 := Spec.completeness (params.toSpec hv) (specCh alpha rho lambda beta delta)
    (specHonest rng values blindings) halpha hbeta hdelta (mul_ne_zero hrho hrho)
    (digits_lt params rng values blindings) (zero_pattern rng values blindings)
  rw [Spec.f_opening] at h0 ⊢
  rw [← h0]
  congr 2
  · rw [hr 0 (by norm_num)]
  · exact sum_congr rfl fun s hs => by rw [hr (s + 1) (by simp at hs; omega)]

/-- The norm-linear relation (27) at `τ`, for an opening with `f(T) = 0`. -/
theorem relation_of_f_zero (P : Spec.Params) (ch : Spec.Challenges F) (w : Spec.Opening F)
    (hf : Spec.f P ch w = 0) (τ : Fˣ) :
    evalAt τ (Spec.σ P ch w) = ∑ s ∈ range 8, evalAt τ (Spec.c P ch s) * evalAt τ (Spec.ℓ ch w s) +
      ∑ k ∈ range P.nm, ch.μ ^ (k + 1) * (evalAt τ (Spec.n P ch w k) * evalAt τ (Spec.n P ch w k)) := by
  have := congrArg (evalAt τ) hf
  simp only [Spec.f, Spec.normμ, map_sub, map_sum, map_mul, map_zero, evalAt_mono, zpow_zero,
    mul_one] at this
  linear_combination this

end Circuit

end Bppp
