-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/TopOfTwoMore.lean: what Johnson/Goal/TopOfTwo.lean does not state: the tops
from `KeySound` and `ProofSound` at the ONE CLOSED stand-in `theWideDigits`
(Johnson/Goal/Conditions/WideDigits.lean): `theWide` at `digitCoins` and `digitWide`, whose two
enumerations list all the committer's coins. No letter is left.
Five theorems. The first three are Johnson/Goal/Conditions/AllAtDigits.lean's, which take three
hypotheses, at `FlashProve.entrySound` (Johnson/Goal/Conditions/EntrySits.lean). The last two are
the two ties of Ladder/PackageBits.lean at the first one's `G8bits` and `G9bits`: at `levelError`.
  `all_digits_of_two`           `G8`, `G8bits`, `G9`, `G9bits` (the last two need neither premise)
  `soundAndBinding_digits_of_two`, `soundOpened_digits_of_two`               at `joinError`
  `soundAndBinding_level_digits_of_two`, `soundOpened_level_digits_of_two`   at `levelError`
(The second and the third are also `top_soundAndBinding_of_two` and `top_soundOpened_of_two` at
`digitCoins` and `digitWide`: stated here at the closed name.)

Limits. Those of TopOfTwo.lean, AllAtDigits.lean and WideDigits.lean travel whole. `KeySound` and
`ProofSound` are premises, and each is itself an assumption of soundness: nothing in this file shows
that they can be met. Elsewhere in this library `KeySound` is a theorem (`keySound_holds`,
Johnson/Goal/Conditions/KeyOpenHolds.lean; it asks something only under the live test's yes, which
is proved at the library's written copies of the public files (`theLive_zFull`, `theLive_zGap`,
`theLive_zAt`, AtFullSide/Top/, a side library), not at the release's files as bytes); so is
`ProofSound`, which asks every Z in scope, under the same test's yes (`proofSound_of_verify`,
SoundOfVerifyGoals.lean): `proofSoundAt_of_verify` (SoundOfVerifyMore.lean) has it at the Z whose
files are read, and files in scope are read.
`theWideDigits` has `VerifierAndGoals.theDescription`'s verifier (`verify_digits`); it is not
`theDescription`; that its extractor is `theDescription`'s is not shown. Its committer is tied to no
program; its sampler gives 0 and its provers hand over empty things. Nothing on completeness or
hiding.
No soundness is claimed.

-/
import Johnson.Goal.TopOfTwo
import Johnson.Goal.Conditions.AllAtDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- Remove the default instance `Inst.Model.Scl.ref`: no statement below may pick it up silently. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/-- **The four stored goals on soundness under the policy and on opening-form binding, at the
closed stand-in.** -/
theorem all_digits_of_two (kS : KeySound) (pS : ProofSound) :
    G8 theWideDigits ∧ G8bits theWideDigits ∧ G9 theWideDigits ∧ G9bits theWideDigits :=
  allFourGoals_atCoinsListedByDigits kS entrySound pS

/-- **Soundness with opening-form binding, in its nearest form, at the closed stand-in.** -/
theorem soundAndBinding_digits_of_two (kS : KeySound) (pS : ProofSound) :
    NearestSoundAndBinding theWideDigits (joinError soundnessErrorInQueries fun t => epsBind honestBudget (t + 2)) :=
  nearestSoundAndBinding_digits_bits kS entrySound pS

/-- **Soundness for an opened commitment, in its nearest form, at the closed stand-in.** -/
theorem soundOpened_digits_of_two (kS : KeySound) (pS : ProofSound) :
    NearestSoundOpened theWideDigits fun t =>
      2 * joinError soundnessErrorInQueries (fun t => epsBind honestBudget (t + 2)) t :=
  nearestSoundOpened_digits_bits kS entrySound pS

/-- **The same at the written error `levelError`.** -/
theorem soundAndBinding_level_digits_of_two (kS : KeySound) (pS : ProofSound) :
    NearestSoundAndBinding theWideDigits levelError :=
  nearestSoundAndBinding_of_bits theWideDigits (all_digits_of_two kS pS).2.1
    (all_digits_of_two kS pS).2.2.2

/-- **And for an opened commitment, at twice `levelError`.** -/
theorem soundOpened_level_digits_of_two (kS : KeySound) (pS : ProofSound) :
    NearestSoundOpened theWideDigits fun t => 2 * levelError t :=
  nearestSoundOpened_of_bits theWideDigits (all_digits_of_two kS pS).2.1
    (all_digits_of_two kS pS).2.2.2

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.all_digits_of_two
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_digits_of_two
#print axioms VerifierAndGoals.AtTheName.soundOpened_digits_of_two
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_level_digits_of_two
#print axioms VerifierAndGoals.AtTheName.soundOpened_level_digits_of_two
