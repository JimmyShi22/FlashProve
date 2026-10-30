-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ladder/PackageBits.lean: what the goals with a security level (Ladder/Bits.lean) give of the goals
of Ladder/Package.lean: `Sound`, `SoundAndBinding` and `SoundOpened` of `D`'s own verifier, in their
nearest forms, AT A WRITTEN ERROR. Theorems with proofs. General in `D`.

Why. The ties of Ladder/PackageTies.lean from G7, G8 and G9 end in "there is an error of at most 1/4
(1/2) up to 2^64 queries": a bar, no security level. Here the error is a term.

What this file states.
  `within_mono`: a parser within n queries is within every larger number.
  `soundAndBinding_of_record_within`: as `soundAndBinding_of_record` (Ladder/PackageTies.lean), with
    the bound on `D`'s own parser a letter n: the error is max (epsS t n) (epsB t).
  `parserWithin_of_verifierWithin`: `VerifierWithin` bounds `D`'s own parser by `verifierQueryAllowance`.
  `levelError t` := max (`soundnessErrorInQueries` t `verifierQueryAllowance`) (`bindingErrorInQueries` t).
  **`nearestSound_of_g7bits`**: G7bits gives `NearestSound` at `soundnessErrorInQueries` t `verifierQueryAllowance`.
  **`nearestSoundAndBinding_of_bits`**: G8bits and G9bits give `NearestSoundAndBinding` at
    `levelError`.
  **`nearestSoundOpened_of_bits`**: and `NearestSoundOpened` at twice `levelError`.
  `sound_everyOlder_of_g7'bits`: G7'bits gives `Sound` at `soundnessErrorInQueries` t `verifierQueryAllowance` at every function in
    the second hash function's place.

How the parser's count comes down. `SoundAt` and `SoundUnderPolicyAt` allow `D`'s own parser
`honestBudget` (2^48) queries; `VerifierWithin`, which G7bits, G7'bits and G8bits ask too, bounds it
by `verifierQueryAllowance` (2^23). So the error of `D`'s own verifier is `soundnessErrorInQueries` t `verifierQueryAllowance`, not `soundnessErrorInQueries` t
`honestBudget`.

In figures (by the definitions of Ladder/Bits.lean; no theorem here evaluates them): `soundnessErrorInQueries` t
`verifierQueryAllowance` is 16 (t + 2^24) / 2^128 + (t + 2^24 + 2)² / 2^256: 16 / 2^128, that is 124 bits, for
each query, and about 2^-100 at no query.

What it does not show. That any goal of Ladder/Bits.lean holds of any description: these are
conditionals. The limits of Ladder/PackageTies.lean hold here too: exact match alone; the arrows run
downhill (none of the three forms reached here bounds an honest party's queries, and
`VerifierWithin` is dropped); the
public files are fixed before the hash function is drawn; a verifier that refuses everything meets
every goal on soundness. On units see the head of Ladder/Bits.lean: `verifierQueryAllowance` counts mostly typed
queries. The numbers are choices of this project.

-/
import Ladder.Bits
import Ladder.PackageTies
import Johnson.Top.Seam.ReaderWith

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals
open VerifiableInference Inst.Model
open scoped ENNReal

/-- A parser within n queries is within every larger number. -/
theorem within_mono {D : Description} {Z : PublicFiles} {Form : Type} (parse : Parser D Z Form) {n n' : ℕ}
    (le : n ≤ n') (h : parse.Within n) : parse.Within n' :=
  fun prompt output form => queryBound_mono_det _ _ _ le (h prompt output form)

/-- **At exact match: `SoundAndBinding` of `D`'s own verifier**, where `D`'s own parser stays within
n queries: at the larger of epsS t n and epsB t. -/
theorem soundAndBinding_of_record_within (D : Description) (epsS : ℕ → ℕ → ℝ≥0∞) (epsB : ℕ → ℝ≥0∞)
    (sound : SoundUnderPolicyAt D epsS) (binds : BindsAt D epsB) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (n : ℕ) (hn : Parser.Within (D.parse Z) n) :
    SoundAndBinding (systemOfRecord D Z (settingsOfRead pp)) fun t => max (epsS t n) (epsB t) := by
  have h1 := (sound Z pp scope read).2 D.Form (D.prove Z (settingsOfRead pp)) (D.parse Z) n hn
  have hb := (binds Z pp scope read).2
  rw [exact] at h1
  have h2 := SoundForWith.mapWeights _ _ _ _ h1 (ModelWeights (settingsOfRead pp)) D.Shown
    (D.shown (settingsOfRead pp)) (modelNextToken (settingsOfRead pp))
    (D.commit Z (settingsOfRead pp)) (D.prove Z (settingsOfRead pp)) id
    (systemOfRecord D Z (settingsOfRead pp)).IsModelOutput
    (fun w p o hm => ((Policy.meetsPolicy_exact_iff w p o).1 hm).2)
  have e : (fun c q => (D.extractor Z (settingsOfRead pp) c q).map id) =
      D.extractor Z (settingsOfRead pp) := by
    funext c q
    simp
  have h3 : SoundForWith (systemOfRecord D Z (settingsOfRead pp))
      (D.extractor Z (settingsOfRead pp))
      (systemOfRecord D Z (settingsOfRead pp)).IsModelOutput (fun t => epsS t n) :=
    e ▸ h2
  exact soundAndBinding_of_le _ _ _ _ _ h3 hb (fun _ => le_max_left _ _) (fun _ => le_max_right _ _)

/-- `VerifierWithin` bounds `D`'s own parser by `verifierQueryAllowance`. -/
theorem parserWithin_of_verifierWithin {D : Description} (h : VerifierWithin D) (Z : PublicFiles)
    (scope : InScope Z = true) : Parser.Within (D.parse Z) verifierQueryAllowance := by
  obtain ⟨qMore, qParse, -, hp, hle⟩ := h Z scope
  have c₀ : Digest := fun _ => false
  refine within_mono _ ?_ hp
  by_contra hlt
  exact hlt (le_trans (by omega) (hle c₀ ((D.readMore Z c₀).evaluate fun _ => c₀)))

/-- The larger of the soundness error at 2^23 parser queries (`verifierQueryAllowance`, the bound on `D`'s own
parser) and the binding error `bindingErrorInQueries`. -/
def levelError (t : ℕ) : ℝ≥0∞ := max (soundnessErrorInQueries t verifierQueryAllowance) (bindingErrorInQueries t)

/-- **G7bits gives `Sound` of `D`'s own verifier, in its nearest form, at `soundnessErrorInQueries` t `verifierQueryAllowance`.** -/
theorem nearestSound_of_g7bits (D : SecondHashFunctionType → Description) (h : G7bits D) :
    NearestSound D fun t => soundnessErrorInQueries t verifierQueryAllowance :=
  fun Z pp scope read exact =>
    (h.2 Z pp scope read exact).2 _ _ _ verifierQueryAllowance (parserWithin_of_verifierWithin h.1 Z scope)

/-- **G8bits and G9bits give `SoundAndBinding` of `D`'s own verifier, in its nearest form, at
`levelError`.** -/
theorem nearestSoundAndBinding_of_bits (D : SecondHashFunctionType → Description) (h8 : G8bits D) (h9 : G9bits D) :
    NearestSoundAndBinding D levelError :=
  fun Z pp scope read exact =>
    soundAndBinding_of_record_within _ soundnessErrorInQueries bindingErrorInQueries h8.2 h9 Z pp scope read exact verifierQueryAllowance
      (parserWithin_of_verifierWithin h8.1 Z scope)

/-- **And `SoundOpened`, at twice `levelError`.** -/
theorem nearestSoundOpened_of_bits (D : SecondHashFunctionType → Description) (h8 : G8bits D) (h9 : G9bits D) :
    NearestSoundOpened D fun t => 2 * levelError t :=
  nearestSoundOpened_of_nearestSoundAndBinding D levelError (nearestSoundAndBinding_of_bits D h8 h9)

/-- **G7'bits gives `Sound` at `soundnessErrorInQueries` t `verifierQueryAllowance` at every function o in the second hash
function's place**, at all public files in scope that state exact match. -/
theorem sound_everyOlder_of_g7'bits (D : SecondHashFunctionType → Description) (h : G7'bits D) (o : SecondHashFunctionType) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    Sound (systemOfRecord (D o) Z (settingsOfRead pp)) fun t => soundnessErrorInQueries t verifierQueryAllowance :=
  ((h o).2 Z pp scope read exact).2 _ _ _ verifierQueryAllowance
    (parserWithin_of_verifierWithin (h o).1 Z scope)

end VerifierAndGoals

#print axioms VerifierAndGoals.within_mono
#print axioms VerifierAndGoals.soundAndBinding_of_record_within
#print axioms VerifierAndGoals.parserWithin_of_verifierWithin
#print axioms VerifierAndGoals.nearestSound_of_g7bits
#print axioms VerifierAndGoals.nearestSoundAndBinding_of_bits
#print axioms VerifierAndGoals.nearestSoundOpened_of_bits
#print axioms VerifierAndGoals.sound_everyOlder_of_g7'bits
