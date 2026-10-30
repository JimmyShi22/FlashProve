-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/BindingOfCore.lean: AT ONE SET OF PUBLIC FILES Z, from the hypotheses of
`sound_of_conditions_core_at` (Johnson/Goal/Skeleton/SoundOfConditionsCore.lean), to the letter: the
body of the goal with the level at Z, and the two statements that read openings of the commitment.
THE HYPOTHESES (in scope, read as pp), where `protocolDataWellFormed` accepts: `owed`: `At.CondsOwed Z`; `kinds`:
under every head `KindsConds h h.free`; `core`: `P5J.coreAt Z = true`. What each is: that file's
head.
`proofSoundAt_of_core`: they give `ProofSoundAt Z` (Johnson/Goal/Skeleton/TopAtZ.lean), by the calls
that lie inside that theorem, in order: `lastLeft_of_coreAt`, `five_at_free2_laid2`,
`kindsLaws_at_free`, `proofKinds_at_free`, `conds_of_laid`, `H2K12.lastTypedAt_of_live`,
`proofFileAt_of_kinds`, `proofSound_at_of_proofFileAt`.
Then Johnson/Goal/TopAtZBinding.lean's ends at it, the key file's condition paid by
`keySound_at_live_holds` (Johnson/Goal/Conditions/KeyOpenHolds.lean):
  `g8bits_of_core_at`: the two halves of `G8bits theDescription`, the second at Z.
  `soundAndBinding_level_of_core_at`, `soundOpened_level_of_core_at`: of `theBound K`, at
    `levelError` and at twice that: with exact match.
  `soundAndBinding_of_core_at`, `soundOpened_of_core_at`: of `theWide K W`, at
    `joinError soundnessErrorInQueries fun t => epsBind honestBudget (t + 2)` and at twice that.
Limits. CALLS ALONE: THEY PAY NOTHING. No condition is shown to be met in this file: each of the six
theorems here may be empty; all carry owed, kinds and core. Elsewhere owed follows from the live
test's yes (`P5J.owed_of_live`) and what kinds is spent for here, `KindsLaws h h.free`, is a theorem
under every head (`kindsLaws_at_head`; that there is a head is proved at `VerifierAndGoals.storedPublicFiles` and
`VerifierAndGoals.zGap` (at secondHashFunction, with `fixedConfigurationDigest` in the digest's place; side library AtFullSide/Top/); at
other files: evaluated, not proved); core
has no payer in this tree. THE FOUR THAT READ OPENINGS ARE STATED OF TWO STAND-IN DESCRIPTIONS,
NOT OF `theDescription`. Both keep its verifier (`verify_theBound` is rfl, `verify_theWide` a
theorem) and add a committer; both keep its extractor (`same_extractor_bound`,
Johnson/Goal/TopOfThreeBinding.lean; `same_extractor_wide`, Johnson/Goal/SameExtractorWide.lean).
At `theBound K` the number of the committer's coins is 0: opening-form binding and soundness for an
opened commitment speak of one setting of the coins.
No theorem ties either committer to the release's program that commits. Nothing on hiding.
THE TWO AT `theWide K W` ARE NOT AT THE LEVEL: `joinError soundnessErrorInQueries …` holds `soundnessErrorInQueries t honestBudget`, with
`honestBudget` = 2^48 (Ladder.lean): by arithmetic about 2^-76 at t = 0, against about 2^-100 for
`levelError`; both grow by 16 / 2^128 a query. OF `theWide K W` AT `levelError`:
Johnson/Goal/BindingOfCoreLevel.lean. Whoever quotes one of the four says of which stand-in and at
which error. The limits of Johnson/Goal/TopOfThreeBinding.lean and of the files that are
called travel whole.

-/
import Johnson.Goal.TopAtZBinding
import Johnson.Goal.Skeleton.SoundOfConditionsCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference
open P5J

section
variable (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
  (read : readFiles Z = .ok pp)
  (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
  (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
    (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
      KindsConds h h.free)
  (core : protocolDataWellFormed (asDescriptionFiles Z) = true → P5J.coreAt Z = true)
include scope read owed kinds core

/-- **The proof file's hypothesis at Z, from the core top's own hypotheses.** pp and `read` serve
`conds_of_laid` alone. -/
theorem proofSoundAt_of_core : ProofSoundAt Z :=
  fun hl => proofSound_at_of_proofFileAt Z scope hl
    (proofFileAt_of_kinds Z scope hl (conds_of_laid scope hl read (owed hl))
      (H2K12.lastTypedAt_of_live Z scope hl)
      fun Zp Np cF x h => proofKinds_at_free h (kindsLaws_at_free (kinds hl Zp Np cF x h))
        (five_at_free2_laid2 h hl (P5J.lastLeft_of_coreAt (core hl) h)))

/-- The two halves of `G8bits theDescription`, the second at Z. -/
theorem g8bits_of_core_at :
    VerifierWithin (atSecondHashFunction theDescription) ∧
      SoundUnderPolicyAtZ (atSecondHashFunction theDescription) VerifierAndGoals.soundnessErrorInQueries Z pp :=
  g8bits_at Z pp scope read (keySound_at_live_holds Z scope)
    (proofSoundAt_of_core Z pp scope read owed kinds core)

variable (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (K : TheCoins) (W : WideCoins K)
include exact

/-- **`SoundAndBinding` at Z, of `theBound K`, at `levelError`.** -/
theorem soundAndBinding_level_of_core_at :
    SoundAndBinding (systemOfRecord (atSecondHashFunction (theBound K)) Z (settingsOfRead pp)) levelError :=
  soundAndBinding_level_at K Z pp scope read exact (keySound_at_live_holds Z scope)
    (proofSoundAt_of_core Z pp scope read owed kinds core)

/-- **`SoundOpened`**, at twice that error. -/
theorem soundOpened_level_of_core_at :
    SoundOpened (systemOfRecord (atSecondHashFunction (theBound K)) Z (settingsOfRead pp)) fun t =>
      2 * levelError t :=
  soundOpened_level_at K Z pp scope read exact (keySound_at_live_holds Z scope)
    (proofSoundAt_of_core Z pp scope read owed kinds core)

/-- **`SoundAndBinding` at Z, of `theWide K W`**: not at the level (see the head). -/
theorem soundAndBinding_of_core_at :
    SoundAndBinding (systemOfRecord (atSecondHashFunction (theWide K W)) Z (settingsOfRead pp))
      (joinError soundnessErrorInQueries fun t => epsBind honestBudget (t + 2)) :=
  soundAndBinding_at K W Z pp scope read exact (keySound_at_live_holds Z scope)
    (proofSoundAt_of_core Z pp scope read owed kinds core)

/-- **`SoundOpened`**, at twice that error. -/
theorem soundOpened_of_core_at :
    SoundOpened (systemOfRecord (atSecondHashFunction (theWide K W)) Z (settingsOfRead pp)) fun t =>
      2 * joinError soundnessErrorInQueries (fun t => epsBind honestBudget (t + 2)) t :=
  soundOpened_at K W Z pp scope read exact (keySound_at_live_holds Z scope)
    (proofSoundAt_of_core Z pp scope read owed kinds core)

end

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.proofSoundAt_of_core
#print axioms VerifierAndGoals.AtTheName.g8bits_of_core_at
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_level_of_core_at
#print axioms VerifierAndGoals.AtTheName.soundOpened_level_of_core_at
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_of_core_at
#print axioms VerifierAndGoals.AtTheName.soundOpened_of_core_at
