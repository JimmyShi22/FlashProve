-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ladder/NonEmptyTies.lean: the goals of Ladder.lean against the statements without the empty list of
output tokens (VerifiableInference/StatementsNonEmpty.lean).

Main statement. `soundNonEmpty_of_soundUnderPolicyAt`: soundness under the files' policy gives, at
the files of exact match, `SoundNonEmpty` of the system of `verify`: the stronger form, in which an
accepted empty list counts as a failure. The reason: at exact match the policy's claim is "there is
an output token, and the output tokens are the model's" (`Policy.meetsPolicy_exact_iff`).
`nearestSoundNonEmpty_of_g8`: so `G8` gives it at an error under the ceiling. ("Nearest" as in
`NearestSound`, Ladder/Package.lean: of `D`'s own system, at the files in scope whose policy is
exact match.)
-/
import Ladder.Ties
import VerifiableInference.StatementsNonEmpty

set_option autoImplicit false

namespace VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat
open scoped ENNReal

/-- Soundness under the files' policy gives `SoundNonEmpty` at the files of exact match. -/
theorem soundNonEmpty_of_soundUnderPolicyAt (D : Description) (eps : ℕ → ℕ → ℝ≥0∞)
    (h : SoundUnderPolicyAt D eps) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (ht : InScope Z = true)
    (hr : readFiles Z = .ok pp) (hx : pp.pol = Inst.Model.AcceptancePolicy.exact) (Form : Type)
    (prove : ModelWeights (settingsOfRead pp) → D.Rand → List Token → List Token →
      RandomizedAlgorithm Form)
    (parse : Parser D Z Form) (n : ℕ) (hn : parse.Within n) :
    SoundNonEmpty (system D Z (settingsOfRead pp) Form prove parse) fun t => eps t n := by
  have h1 := (h Z pp ht hr).2 Form prove parse n hn
  rw [hx] at h1
  have h2 := SoundForWith.mapWeights _ _ _ _ h1 (ModelWeights (settingsOfRead pp)) D.Shown
    (D.shown (settingsOfRead pp)) (modelNextToken (settingsOfRead pp))
    (D.commit Z (settingsOfRead pp)) prove id
    (system D Z (settingsOfRead pp) Form prove parse).IsModelOutputNonEmpty
    (fun w p o hm => (Policy.meetsPolicy_exact_iff w p o).1 hm)
  have h3 : SoundForWith (system D Z (settingsOfRead pp) Form prove parse)
      (fun c q => (D.extractor Z (settingsOfRead pp) c q).map id)
      (system D Z (settingsOfRead pp) Form prove parse).IsModelOutputNonEmpty
      (fun t => eps t n) := h2
  exact (soundNonEmpty_iff_soundFor _ _).2 ⟨_, h3⟩

/-- **G8 gives `SoundNonEmpty` of the system of `verify`**, at all files in scope with exact match,
at one error that is at most the ceiling up to the budget. -/
theorem nearestSoundNonEmpty_of_g8 (D : SecondHashFunctionType → Description) (h : G8 D) :
    ∃ ε : ℕ → ℝ≥0∞, (∀ t, t ≤ queryBudget → ε t ≤ ceiling) ∧
      ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
        pp.pol = Inst.Model.AcceptancePolicy.exact →
        SoundNonEmpty (systemOfRecord (atSecondHashFunction D) Z (settingsOfRead pp)) ε := by
  obtain ⟨eps, below, sound⟩ := h
  refine ⟨fun t => eps t honestBudget, fun t ht => below t honestBudget ht (by decide), ?_⟩
  intro Z pp ht hr hx
  exact soundNonEmpty_of_soundUnderPolicyAt _ eps sound Z pp ht hr hx _ _ _ honestBudget
    (sound Z pp ht hr).1

end VerifierAndGoals

#print axioms VerifierAndGoals.soundNonEmpty_of_soundUnderPolicyAt
#print axioms VerifierAndGoals.nearestSoundNonEmpty_of_g8
