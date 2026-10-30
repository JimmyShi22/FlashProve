-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/TopOfTwo.lean: the tops of Johnson/Goal/TopOfThree.lean and TopOfThreeBinding.lean from
TWO hypotheses in the place of three.
Each `…_of_two` is its `…_of_three` at `FlashProve.entrySound`
(Johnson/Goal/Conditions/EntrySits.lean), which pays the row `VerifierAndGoals.AtTheName.EntrySound` without a
premise. What is left in front: `KeySound` and `ProofSound`.
Whose weight. All of `EntrySound`'s weight lies in the law on the entry file's description behind
`entrySound`; nothing is proved here but eight calls.
Limits. `KeySound` and `ProofSound` stay hypotheses here. Elsewhere in this tree both are theorems:
`keySound_holds` (Johnson/Goal/Conditions/KeyOpenHolds.lean) and `proofSound_of_verify`
(Johnson/Goal/Skeleton/SoundOfVerifyGoals.lean); each asks its body only where `protocolDataWellFormed` says yes.
`EntrySound` is met by any decision that never says yes: that the entry's decision
says yes at an honest entry file is evaluated, proved by nobody. EntrySits.lean's limits travel: the
statement on codes behind it is filled by `Cb.Gl.bchks46At` (lean/LIMITS.md, L15);
its bound counts work; it is the round-by-round soundness of an interactive
protocol, at the full size alone. The statements' own limits are those of the two files named above.
No soundness is claimed.

-/
import Johnson.Goal.TopOfThreeBinding
import Johnson.Goal.Conditions.EntrySits

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

theorem soundUnderPolicyAt_of_two (kS : KeySound) (pS : ProofSound) :
    SoundUnderPolicyAt (atSecondHashFunction theDescription) VerifierAndGoals.soundnessErrorInQueries :=
  soundUnderPolicyAt_of_three kS entrySound pS

/-- **G8bits at the name, from two hypotheses.** -/
theorem g8bits_of_two (kS : KeySound) (pS : ProofSound) : G8bits theDescription :=
  g8bits_of_three kS entrySound pS

/-- **The top row on soundness at the name, from two hypotheses.** -/
theorem top_sound_of_two (kS : KeySound) (pS : ProofSound) :
    NearestSound theDescription fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  top_sound_of_three kS entrySound pS

variable (K : TheCoins) (W : WideCoins K)

theorem top_soundAndBinding_of_two (kS : KeySound) (pS : ProofSound) :
    NearestSoundAndBinding (theWide K W) (joinError soundnessErrorInQueries fun t => epsBind honestBudget (t + 2)) :=
  top_soundAndBinding_of_three K W kS entrySound pS

theorem top_soundOpened_of_two (kS : KeySound) (pS : ProofSound) :
    NearestSoundOpened (theWide K W) fun t =>
      2 * joinError soundnessErrorInQueries (fun t => epsBind honestBudget (t + 2)) t :=
  top_soundOpened_of_three K W kS entrySound pS

theorem g8bits_bound_of_two (kS : KeySound) (pS : ProofSound) : G8bits (theBound K) :=
  g8bits_bound_of_three K kS entrySound pS

theorem top_soundAndBinding_level_of_two (kS : KeySound) (pS : ProofSound) :
    NearestSoundAndBinding (theBound K) levelError :=
  top_soundAndBinding_level_of_three K kS entrySound pS

theorem top_soundOpened_level_of_two (kS : KeySound) (pS : ProofSound) :
    NearestSoundOpened (theBound K) fun t => 2 * levelError t :=
  top_soundOpened_level_of_three K kS entrySound pS

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.soundUnderPolicyAt_of_two
#print axioms VerifierAndGoals.AtTheName.g8bits_of_two
#print axioms VerifierAndGoals.AtTheName.top_sound_of_two
#print axioms VerifierAndGoals.AtTheName.top_soundAndBinding_of_two
#print axioms VerifierAndGoals.AtTheName.top_soundOpened_of_two
#print axioms VerifierAndGoals.AtTheName.g8bits_bound_of_two
#print axioms VerifierAndGoals.AtTheName.top_soundAndBinding_level_of_two
#print axioms VerifierAndGoals.AtTheName.top_soundOpened_level_of_two
