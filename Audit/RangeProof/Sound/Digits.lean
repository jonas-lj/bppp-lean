import Bppp.Spec.CircuitExtract

/-!
# Jonas's circuit extractor, with the value read off `C_L`

This file restates Jonas's `circuit_extract` (`Bppp/Spec/CircuitExtract.lean`) for a computable
extractor.

Why it exists:
- Jonas's conclusion is `∃ v s`. The extractor must compute `v`. A search over all values below
  `2^bits` is too slow.
- Here the generators have no relation, and the caller gives an opening `(s0, h0, n0)` of `C_L`.
  The conclusion names the value: `Σ_t 16^t n0 (i D + t)`, with digits `n0 k < 16`.

How it works:
- The proof is Jonas's proof, with the same steps. Only the last step changes: `binding` shows
  that his opening of `C_L` agrees with `(s0, h0, n0)` on the first `nm` coordinates.
-/

open Finset

namespace Bppp.Spec

variable {F : Type*} [Field F] [DecidableEq F] (P : Params)
variable {E : Type*} [AddCommGroup E] [Module F E] (g : E) (H G : ℕ → E)

/-- **The circuit extractor, with the value off `C_L`.** The hypotheses of `circuit_extract`, no
relation among the generators, and an opening `(s0, h0, n0)` of `C_L`. Then each `n0 k` with
`k < N_d` is a digit below 16, and each input is `(Σ_t 16^t n0 (i D + t)) g + s H_0`. -/
theorem circuit_extract_digits (hrel : ¬ Relation F P g H G) (h2 : (2 : F) ≠ 0)
    (hchar : ∀ m : ℕ, 0 < m → m ≤ P.Nd → (m : F) ≠ 0)
    (hM : 0 < P.M) (V : ℕ → E) (cO cL : E) (cR : Fin (P.Nd + 16) → E)
    (cS : Fin (P.Nd + 16) → Fin (P.nm + 1) → Fin 2 → Fin (P.M * (P.nm + 8) + 1) → E)
    (α : Fin (P.Nd + 16) → F) (μ δ rho : Fin (P.Nd + 16) → Fin (P.nm + 1) → F)
    (β : Fin (P.Nd + 16) → Fin (P.nm + 1) → Fin 2 → F)
    (lam : Fin (P.Nd + 16) → Fin (P.nm + 1) → Fin 2 → Fin (P.M * (P.nm + 8) + 1) → F)
    (τ : Fin (P.Nd + 16) → Fin (P.nm + 1) → Fin 2 → Fin (P.M * (P.nm + 8) + 1) → Fin 13 → Fˣ)
    (hα : Function.Injective α) (hμ : ∀ a, Function.Injective (μ a))
    (hβ : ∀ a r, Function.Injective (β a r)) (hlam : ∀ a r b, Function.Injective (lam a r b))
    (hτ : ∀ a r b l, Function.Injective (τ a r b l))
    (hpole : ∀ a, ∀ j : ℕ, j < 16 → α a + j ≠ 0) (hμ0 : ∀ a r, μ a r ≠ 0)
    (hδ0 : ∀ a r, δ a r ≠ 0)
    (w : Fin (P.Nd + 16) → Fin (P.nm + 1) → Fin 2 → Fin (P.M * (P.nm + 8) + 1) → Fin 13 →
      NormLinear.Witness F)
    (hw : ∀ a r b l t, NormLinear.Rel g (tauInst P (treeCh α μ δ β lam a r b l) g H G
      (cS a r b l) cO cL (cR a) (vHat P (treeCh α μ δ β lam a r b l) V) (rho a r) (τ a r b l t))
      (w a r b l t))
    (s0 : F) (h0 n0 : ℕ → F) (hcL : cL = commit P g H G s0 h0 n0) :
    (∀ k < P.Nd, ∃ d : ℕ, d < 16 ∧ n0 k = d) ∧
      ∀ i < P.M, ∃ s : F, V i = (∑ t ∈ range P.D, 16 ^ t * n0 (i * P.D + t)) • g + s • H 0 := by
  set ch := treeCh α μ δ β lam
  -- `τ`: every node above the leaves opens its commitments with `f ≡ 0`.
  have tau := fun a r b l => (extract_tau P (ch a r b l) g H G (cS a r b l) cO cL (cR a)
    (vHat P (ch a r b l) V) (rho a r) (τ a r b l) (hτ a r b l) (hδ0 a r) (w a r b l)
    (hw a r b l)).resolve_right fun h => hrel (relation_of_tau P g H G h)
  choose wo hf hS hO hL hR hV using tau
  -- `λ`: the inputs open in the plane, with set membership and the value links `i ≥ 1`.
  have lamL := fun a r b => (extract_lam P (ch a r b 0) g H G h2 hM (hδ0 a r) (hμ0 a r) cO cL
    (cR a) V (lam a r b) (hlam a r b) (wo a r b) (hf a r b) (hO a r b) (hL a r b) (hR a r b)
    (hV a r b)).resolve_right hrel
  choose u hh nn hVu hn0 hh0 hSrow hlink hres using lamL
  -- `β`: (36).
  have betaL := fun a r => (extract_beta P (ch a r 0 0) g H G hM cO cL (cR a) (V 0) (β a r)
    (hβ a r) (fun b => wo a r b 0) (u a r) (hh a r) (nn a r) (fun b => hO a r b 0)
    (fun b => hL a r b 0) (fun b => hR a r b 0) (fun b => hVu a r b 0 hM)
    (fun b => hn0 a r b 0 hM) (fun b => hres a r b)).resolve_right hrel
  -- `ρ`: the first value link and the Hadamard rows.
  have rhoL := fun a => (extract_rho P (ch a 0 0 0) g H G h2 hM cL (cR a) (V 0) (μ a) (hμ a)
    (fun r => wo a r 0 0) (fun r => u a r 0 0) (fun r => hh a r 0 0) (fun r => nn a r 0 0)
    (fun r => hL a r 0 0) (fun r => hR a r 0 0) (fun r => hVu a r 0 0 hM)
    (fun r => betaL a r)).resolve_right hrel
  -- `α`: the digits are in the table.
  have dig := (extract_alpha P (ch 0 0 0 0) g H G h2 hchar cO cL α hα hpole
    (fun a => wo a 0 0 0) (fun a => hO a 0 0 0) (fun a => hL a 0 0 0)
    (fun a => hSrow a 0 0) (fun a => (rhoL a).2.1)).resolve_right hrel
  -- His opening of `C_L` agrees with `(s0, h0, n0)` below `nm`.
  have hn : ∀ k < P.nm, (wo 0 0 0 0).nL k = n0 k :=
    ((binding P g H G ((hL 0 0 0 0).symm.trans hcL)).resolve_right hrel).2.2
  have hNd : P.Nd ≤ P.nm := P.hnm
  have hslot : ∀ i < P.M, ∀ t < P.D, i * P.D + t < P.Nd := fun i hi t ht => by
    have := Nat.mul_le_mul_right P.D (show i + 1 ≤ P.M by omega)
    have : (i + 1) * P.D = i * P.D + P.D := by ring
    simp only [Params.Nd]
    omega
  refine ⟨fun k hk => ?_, fun i hi => ⟨hh 0 0 0 i 0, ?_⟩⟩
  · obtain ⟨d, hd, e⟩ := dig k hk
    exact ⟨d, hd, (hn k (by omega)).symm.trans e⟩
  rw [hVu 0 0 0 i hi, commit_plane P g H G _ _ _ (hh0 0 0 0 i hi) (hn0 0 0 0 i hi)]
  congr 2
  have hu : u 0 0 0 i = ∑ t ∈ range P.D, 16 ^ t * (wo 0 0 0 0).nL (i * P.D + t) := by
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · simpa using (rhoL 0).1
    · exact hlink 0 0 0 i hi1 hi
  rw [hu]
  exact sum_congr rfl fun t ht => by rw [hn _ (by have := hslot i hi t (mem_range.1 ht); omega)]

end Bppp.Spec
