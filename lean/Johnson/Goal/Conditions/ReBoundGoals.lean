-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/ReBoundGoals.lean: EVERY GOAL ON SOUNDNESS CARRIES OVER WHEN THE NUMBER OF
THE COMMITTER'S COINS IS LAID ANEW: BY A RULE, NOT BY A SECOND TYPING. General in the description.
Statements and proofs.

Why. `coinBound` is read by no verifier and no goal (Johnson/Goal/Conditions/ReBound.lean). So what is
proved on soundness of a description holds of the same description with another number of coins, and
of the description with the honest side's terms laid in over it. Here that is said once for each
goal.

Main names (namespace `VerifierAndGoals.Fit`). In each, both directions.
  (1) OF `D.reBound b` AGAINST D: `soundAt_reBound_iff` · `soundUnderPolicyAt_reBound_iff` ·
    `verifierWithin_reBound_iff`; and of families fun o => (D o).reBound b: `G7_reBound_iff` ·
    `G7'_reBound_iff` · `G8_reBound_iff` · `G7bits_reBound_iff` · `G7'bits_reBound_iff` ·
    `G8bits_reBound_iff`.
  (2) OF `(D.reBound b).withTerms (Q.reBound b coins')` AGAINST `D.withTerms Q`: `soundAt_wide_iff`
    · `soundUnderPolicyAt_wide_iff` · `verifierWithin_wide_iff`; and of families: `G7_wide_iff` ·
    `G8_wide_iff` · `G7bits_wide_iff` · `G8bits_wide_iff`.
All by definition: the two sides are the same proposition once the definitions are opened: they read
the verifier, the parser, the readings, the wiring, the extractor and the type of the randomness,
which are the same terms.

NOT HERE, AND NOT TRUE AS A RULE: the goals that read the committer: G9, G9bits (opening-form
binding: they pass by
`BindLaws.reBound`, with the coins' count asked anew) and G3'pol (completeness).
Limits. Those of ReBound.lean. Conditionals: nothing is shown of any description.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.ReBound
import Ladder.Bits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat Rom
open scoped ENNReal

/-! ## (1) The description with another number of coins -/

section Plain
variable (D : Description) (b : PublicFiles → ℕ)

theorem soundAt_reBound_iff (eps : ℕ → ℕ → ℝ≥0∞) : SoundAt (D.reBound b) eps ↔ SoundAt D eps :=
  Iff.rfl

theorem soundUnderPolicyAt_reBound_iff (eps : ℕ → ℕ → ℝ≥0∞) :
    SoundUnderPolicyAt (D.reBound b) eps ↔ SoundUnderPolicyAt D eps := Iff.rfl

theorem verifierWithin_reBound_iff : VerifierWithin (D.reBound b) ↔ VerifierWithin D := Iff.rfl

end Plain

section PlainFamily
variable (D : SecondHashFunctionType → Description) (b : PublicFiles → ℕ)

theorem G7_reBound_iff : G7 (fun o => (D o).reBound b) ↔ G7 D := Iff.rfl

theorem G7'_reBound_iff : G7' (fun o => (D o).reBound b) ↔ G7' D := Iff.rfl

theorem G8_reBound_iff : G8 (fun o => (D o).reBound b) ↔ G8 D := Iff.rfl

theorem G7bits_reBound_iff : G7bits (fun o => (D o).reBound b) ↔ G7bits D := Iff.rfl

theorem G7'bits_reBound_iff : G7'bits (fun o => (D o).reBound b) ↔ G7'bits D := Iff.rfl

theorem G8bits_reBound_iff : G8bits (fun o => (D o).reBound b) ↔ G8bits D := Iff.rfl

end PlainFamily

/-! ## (2) With the honest side's terms laid in -/

section Terms
variable {D : Description} (Q : HonestTerms D) (b : PublicFiles → ℕ)
  (coins' : (Z : PublicFiles) → Q.Rand → DeterministicAlgorithm (Fin (b Z + 1)))

theorem soundAt_wide_iff (eps : ℕ → ℕ → ℝ≥0∞) :
    SoundAt ((D.reBound b).withTerms (Q.reBound b coins')) eps ↔ SoundAt (D.withTerms Q) eps :=
  Iff.rfl

theorem soundUnderPolicyAt_wide_iff (eps : ℕ → ℕ → ℝ≥0∞) :
    SoundUnderPolicyAt ((D.reBound b).withTerms (Q.reBound b coins')) eps ↔
      SoundUnderPolicyAt (D.withTerms Q) eps := Iff.rfl

theorem verifierWithin_wide_iff :
    VerifierWithin ((D.reBound b).withTerms (Q.reBound b coins')) ↔
      VerifierWithin (D.withTerms Q) := Iff.rfl

end Terms

section TermsFamily
variable {D : SecondHashFunctionType → Description} (Q : ∀ o, HonestTerms (D o)) (b : PublicFiles → ℕ)
  (coins' : ∀ o, (Z : PublicFiles) → (Q o).Rand → DeterministicAlgorithm (Fin (b Z + 1)))

theorem G7_wide_iff :
    G7 (fun o => ((D o).reBound b).withTerms ((Q o).reBound b (coins' o))) ↔
      G7 fun o => (D o).withTerms (Q o) := Iff.rfl

theorem G8_wide_iff :
    G8 (fun o => ((D o).reBound b).withTerms ((Q o).reBound b (coins' o))) ↔
      G8 fun o => (D o).withTerms (Q o) := Iff.rfl

theorem G7bits_wide_iff :
    G7bits (fun o => ((D o).reBound b).withTerms ((Q o).reBound b (coins' o))) ↔
      G7bits fun o => (D o).withTerms (Q o) := Iff.rfl

theorem G8bits_wide_iff :
    G8bits (fun o => ((D o).reBound b).withTerms ((Q o).reBound b (coins' o))) ↔
      G8bits fun o => (D o).withTerms (Q o) := Iff.rfl

end TermsFamily

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.soundAt_reBound_iff
#print axioms VerifierAndGoals.Fit.soundUnderPolicyAt_reBound_iff
#print axioms VerifierAndGoals.Fit.verifierWithin_reBound_iff
#print axioms VerifierAndGoals.Fit.G7_reBound_iff
#print axioms VerifierAndGoals.Fit.G7'_reBound_iff
#print axioms VerifierAndGoals.Fit.G8_reBound_iff
#print axioms VerifierAndGoals.Fit.G7bits_reBound_iff
#print axioms VerifierAndGoals.Fit.G7'bits_reBound_iff
#print axioms VerifierAndGoals.Fit.G8bits_reBound_iff
#print axioms VerifierAndGoals.Fit.soundAt_wide_iff
#print axioms VerifierAndGoals.Fit.soundUnderPolicyAt_wide_iff
#print axioms VerifierAndGoals.Fit.verifierWithin_wide_iff
#print axioms VerifierAndGoals.Fit.G7_wide_iff
#print axioms VerifierAndGoals.Fit.G8_wide_iff
#print axioms VerifierAndGoals.Fit.G7bits_wide_iff
#print axioms VerifierAndGoals.Fit.G8bits_wide_iff
