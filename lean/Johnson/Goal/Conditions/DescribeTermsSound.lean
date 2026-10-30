-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/DescribeTermsSound.lean: SOUNDNESS DOES NOT FEEL THE HONEST SIDE'S TERMS:
general in the description: soundness under the files' policy (`SoundUnderPolicyAt`, Ladder.lean) of
a description D whose extractor is already the told record's, then φ, passes to `D.withTerms Q`
(Johnson/Goal/Conditions/DescribeTerms.lean); so the row's form follows from soundness OF D ITSELF,
whatever D's honest side is. Statements and proofs. Conditionals: no description is built.

Why. `nearestSoundAndBinding_withTerms` asks soundness of `D.withTerms Q`. Whoever proves soundness
proves it of a description with some honest side of its own. `SoundForWith` reads of a system the
weights' type, the proofs' type and the verifier alone (`soundForWith_honest_side`,
Johnson/Top/InnerCompiledVerifierByPublicReading.lean: by definition), and `withTerms` turns none of the three. What has
to be bridged is a quantifier: the goal ranges over all honest provers, whose type names the
description's randomness.

Main names (namespace `VerifierAndGoals.Fit`).
  `firstResult`: a result of a randomized algorithm: of the run in which every answer is zero and
    every draw is 0. Used once: `Q.sample` has a result, so Q's randomness has a member.
  **`soundUnderPolicyAt_withTerms`**: under hext, `SoundUnderPolicyAt D eps` gives
    `SoundUnderPolicyAt (D.withTerms Q) eps`: the same error.
  **`nearestSoundAndBinding_of_sound`**: `NearestSoundAndBinding` of the family with the terms laid
    in, at `joinError epsS fun t => epsBind honestBudget (t + q)`, from soundness of the family as
    it is, hext, and `BindLaws`.

WHO READS EACH LETTER: as in Johnson/Goal/Conditions/DescribeTerms.lean. hext: at every Z in scope
that the reader reads, D's own extractor is the told record's named extractor, then φ, by bind: an
equation between two functions, met by laying D's extractor so. D.Rand, D.sample, D.commit, D.prove:
nobody.
NOTHING THAT THE VERIFIER READS STANDS UNDER "THERE IS".

Limits. Those of Johnson/Goal/Conditions/DescribeTerms.lean. Soundness of D stays a premise: nothing
is shown of any verifier. A verifier that refuses everything meets it for nothing.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.DescribeTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat
open scoped ENNReal

/-- A result of a randomized algorithm: every answer zero, every draw 0. -/
def firstResult {α : Type} : RandomizedAlgorithm α → α
  | .done a => a
  | .query _ next => firstResult (next fun _ => false)
  | .sample _ next => firstResult (next 0)

variable {D : Description} (Q : HonestTerms D)

/-- **Soundness under the files' policy passes to the description with the terms laid in**, at the
same error, where D's extractor is already the told record's, then φ (hext). -/
theorem soundUnderPolicyAt_withTerms (eps : ℕ → ℕ → ℝ≥0∞)
    (hext : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      D.extractor Z (settingsOfRead pp) = fun commitment queryLog =>
        ((Q.T Z).extractor commitment queryLog).bind (Q.φ Z (settingsOfRead pp)))
    (sound : SoundUnderPolicyAt D eps) : SoundUnderPolicyAt (D.withTerms Q) eps :=
  fun Z pp h₁ h₂ => ⟨(sound Z pp h₁ h₂).1, fun Form prove parse n hn => by
    have h := (sound Z pp h₁ h₂).2 Form
      (fun w _ prompt output => prove w (firstResult Q.sample) prompt output) parse n hn
    rw [hext Z pp h₁ h₂] at h
    exact h⟩

end VerifierAndGoals.Fit

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat
open scoped ENNReal

/-- **`SoundAndBinding` OF THE GOALS' OWN VERIFIER, IN ITS NEAREST FORM, AT A NAMED ERROR, FROM
SOUNDNESS OF THE FAMILY AS IT IS.** -/
theorem nearestSoundAndBinding_of_sound (D : SecondHashFunctionType → Description) (Q : ∀ o, HonestTerms (D o))
    (tP q : ℕ) (epsS : ℕ → ℕ → ℝ≥0∞) (sound : SoundUnderPolicyAt (D OnBytes.secondHashFunction) epsS)
    (hext : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      (D OnBytes.secondHashFunction).extractor Z (settingsOfRead pp) = fun commitment queryLog =>
        (((Q OnBytes.secondHashFunction).T Z).extractor commitment queryLog).bind
          ((Q OnBytes.secondHashFunction).φ Z (settingsOfRead pp)))
    (h : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      BindLaws (Q OnBytes.secondHashFunction) Z (settingsOfRead pp) tP q) :
    NearestSoundAndBinding (fun o => (D o).withTerms (Q o))
      (joinError epsS fun t => epsBind honestBudget (t + q)) :=
  nearestSoundAndBinding_withTerms D Q tP q epsS
    (soundUnderPolicyAt_withTerms (Q OnBytes.secondHashFunction) epsS hext sound) h

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.soundUnderPolicyAt_withTerms
#print axioms VerifierAndGoals.Fit.nearestSoundAndBinding_of_sound
