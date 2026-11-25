import Audit.NLAFull.Full
import Audit.NLAFull.Lemmas
import Audit.Reductions.Compose

/-!
# The extractor of the full NLA

This file defines `nlaExtract`, the extractor that `nla_sound` names. You do not need to review
the code. Check it with the extractor checklist: it is generic over `F` and `E`, computable,
and it uses only field operations.

How it works:
1. `roundExtract`: one round. If a child gives a link, lift it with `liftLink`. Else each child
   gives a witness: `extractGeneratorLink` gives a candidate link. If it is 0, then
   `extractWitness` gives the witness. Else the candidate is the link.
2. `nlaExtractN n`: at the base case, the leaf is the witness. Before it, `compExtract` runs the
   extractor of the rest at each leaf, then `roundExtract`.
3. `nlaExtract`: `nlaExtractN` with `numRounds m k` rounds.
-/

namespace Audit.NLA

open Audit.TreeSoundness

variable {F E : Type} [Field F] [AddCommGroup E] [Module F E] [DecidableEq F]

variable (F E) in
/-- The fork rule of one round: 4 distinct challenges. -/
def roundRules (m k : ℕ) : (roundReduction F E m k).roundTypes.ForkRules := (⟨4, (· ≠ ·)⟩, ())

omit [Field F] [DecidableEq F] in
/-- The witness part of a relaxed witness. A link gives 0s. -/
def witnessPart {m k : ℕ} [Zero F] : Witness F m k ⊕ Opening F m k → Witness F m k
  | .inl w => w
  | .inr _ => ⟨0, 0⟩

omit [Field F] [DecidableEq F] in
/-- The link part of a relaxed witness, if it has one. -/
def linkPart? {m k : ℕ} : Witness F m k ⊕ Opening F m k → Option (Opening F m k)
  | .inl _ => none
  | .inr o => some o

/-- The extractor of one round. -/
def roundExtract {m k : ℕ} (x : Instance F E m k)
    (t : (roundReduction F E m k).roundTypes.ForkTree (roundRules F E m k)
      (Witness F (half m) (half k) ⊕ Opening F (half m) (half k))) :
    Witness F m k ⊕ Opening F m k :=
  let γ := t.challenges.val
  let ws := t.children
  -- A child that gives a link: lift it.
  match (List.finRange 4).findSome? (fun i => (linkPart? (ws i)).map (liftLink x.ρ (γ i))) with
  | some l => .inr l
  | none =>
    -- Each child gives a witness.
    let w := fun i => witnessPart (ws i)
    let l := extractGeneratorLink x γ w
    if l = 0 then .inl (extractWitness x γ w) else .inr l

/-- The extractor of `n` rounds, then the base case. -/
def nlaExtractN : (n : ℕ) → {m k : ℕ} → Instance F E m k →
    (nlaSystem F E n m k).roundTypes.ForkTree (nlaForkRules F E n m k)
      (nlaSystem F E n m k).ResponseType →
    Witness F m k ⊕ Opening F m k
  | 0, _, _, _, w => .inl w
  | n + 1, m, k, x, t =>
      (roundReduction F E m k).compExtract (nlaSystem F E n (half m) (half k))
        (fs := roundRules F E m k) (gs := nlaForkRules F E n _ _) roundExtract (nlaExtractN n) x t

/-- The extractor of the full NLA. -/
def nlaExtract {m k : ℕ} (x : Instance F E m k)
    (t : (fullSystem F E m k).ForkTree (fullForkRules F E m k)) :
    Witness F m k ⊕ Opening F m k :=
  nlaExtractN (numRounds m k) x t

end Audit.NLA
