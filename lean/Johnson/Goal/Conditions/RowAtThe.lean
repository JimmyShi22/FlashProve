-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/RowAtThe.lean: THE ROW `top_SoundAndBinding` IN ITS FORM, AT THE ONE CLOSED
DESCRIPTION WITH THE TERMS LAID IN (`theBound K`, Johnson/Goal/Conditions/BindsAtThe.lean):
`SoundAndBinding` of the goals' own verifier, in its nearest form (Ladder/Package.lean), and
`SoundOpened` likewise: from the stored G8 OF THAT VERY DESCRIPTION. Statements and proofs.

Main names (namespace `FlashProve`).
  **`nearestSoundAndBinding_theBound`**: there is an error epsS of soundness, at most the ceiling up
    to the two budgets (G8's own), with `NearestSoundAndBinding (theBound K)` at
    `joinError epsS fun t => epsBind honestBudget (t + 2)`.
  `nearestSoundOpened_theBound`: `NearestSoundOpened (theBound K)` at twice that error.

THE PREMISES, ALL. hG8: the stored G8 of `theBound K` (one description, so one extractor, for both
halves). hE: `theCoding` is `codingCells` (it falls by rfl when Johnson/Goal/Description/Coding.lean
is turned
so). K stands under "for all".
"THERE IS" STANDS ONCE, OF epsS: it is G8's own: G8 names no error. The error of binding is named:
3 (t + 2 + 2 · 2^48 + 2)² / 2^256. NOTHING THAT THE VERIFIER READS STANDS UNDER IT.

Limits. Those of Johnson/Goal/Conditions/BindsAtThe.lean. G8 OF `theBound K` IS A PREMISE: ALL OF
SOUNDNESS: nothing is shown here of any decision. A verifier that
refuses everything meets the first clause for nothing: the statement
weighs only beside completeness of this very description, which nobody has shown. The nearest form
speaks at the files whose policy is exact match.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.BindsAtThe

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice

variable (K : TheCoins)

/-- **THE ROW's FORM AT THE DESCRIPTION.** -/
theorem nearestSoundAndBinding_theBound (hG8 : G8 (theBound K))
    (hE : ∀ Zk, theCoding Zk = codingCells frS frZ 402653181 numsRef (ppAtFiles Zk.pol Zk.KL)
      Subtype.val) :
    ∃ epsS : ℕ → ℕ → ℝ≥0∞,
      (∀ t n, t ≤ queryBudget → n ≤ parserBudget → epsS t n ≤ ceiling) ∧
      NearestSoundAndBinding (theBound K)
        (joinError epsS fun t => epsBind honestBudget (t + 2)) := by
  obtain ⟨epsS, ceil, sound⟩ := hG8
  exact ⟨epsS, ceil, nearestSoundAndBinding_withTerms (fun _ => flashProveDescription) (fun _ => theTerms K) 8 2 epsS
    sound fun Z pp _ h₂ => bindLaws_the K hE Z pp h₂⟩

/-- Likewise `SoundOpened`, at twice that error. -/
theorem nearestSoundOpened_theBound (hG8 : G8 (theBound K))
    (hE : ∀ Zk, theCoding Zk = codingCells frS frZ 402653181 numsRef (ppAtFiles Zk.pol Zk.KL)
      Subtype.val) :
    ∃ epsS : ℕ → ℕ → ℝ≥0∞,
      (∀ t n, t ≤ queryBudget → n ≤ parserBudget → epsS t n ≤ ceiling) ∧
      NearestSoundOpened (theBound K)
        fun t => 2 * joinError epsS (fun t => epsBind honestBudget (t + 2)) t := by
  obtain ⟨epsS, ceil, sound⟩ := hG8
  exact ⟨epsS, ceil, nearestSoundOpened_of_at (theBound K) epsS _ sound
    (bindsAt_withTerms (theTerms K) 8 2 fun Z pp _ h₂ => bindLaws_the K hE Z pp h₂)⟩

end FlashProve

#print axioms FlashProve.nearestSoundAndBinding_theBound
#print axioms FlashProve.nearestSoundOpened_theBound
