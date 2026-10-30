-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/BindingOfCoreLevel.lean: a rider to Johnson/Goal/BindingOfCore.lean: THE TWO STATEMENTS
THAT READ OPENINGS, AT THE WRITTEN ERROR `levelError`, OF THE STAND-IN WHOSE COMMITTER HAS COINS, at
one set of public files Z.
Why. Johnson/Goal/BindingOfCore.lean has `levelError` of `theBound K` alone, where the number of the
committer's coins is 0 and every opening is at one setting of the coins; of `theWide K W` it has
`joinError soundnessErrorInQueries …`, which charges the parser `honestBudget` = 2^48 queries. Here the parser of
`theWide K W` is charged what it is shown to ask (`verifierWithin_theWide`: at most `verifierQueryAllowance`),
and binding is taken at `bindingErrorInQueries` (`G9bits_theWide`): so the error is `levelError`: by
arithmetic about 2^-100 at t = 0, against about 2^-76 for BindingOfCore.lean's `joinError soundnessErrorInQueries …`.
  `soundAndBinding_level_wide_at`, `soundOpened_level_wide_at`: at every K and W, from `KeySoundAt
    Z` and `ProofSoundAt Z`: the like of `soundAndBinding_level_at`
    (Johnson/Goal/TopAtZBinding.lean).
  **`soundAndBinding_level_digits_of_core_at`, `soundOpened_level_digits_of_core_at`**: of the
    closed stand-in `theWideDigits` (Johnson/Goal/Conditions/WideDigits.lean), from the hypotheses
    of `sound_of_conditions_core_at`, to the letter (`owed`, `kinds`, `core`; exact match).
THE ENTRY FILE's CONDITION IS NOT DROPPED in the two that name `KeySoundAt Z` and `ProofSoundAt Z`
alone: it is had by its own theorem, `FlashProve.entrySound Z scope`
(Johnson/Goal/Conditions/EntrySits.lean), which `soundUnderPolicyAtZ_bits_theBound`
(Johnson/Goal/TopAtZBinding.lean) calls by name.
The forms for all Z, from other hypotheses: `soundAndBinding_level_digits_of_two`
(Johnson/Goal/Skeleton/TopOfTwoMore.lean).
Limits. CALLS ALONE: THEY PAY NOTHING. That the three hypotheses of the last two are met is not
shown in this file: these two may be empty. The same two statements without owed, kinds, core:
`soundAndBinding_level_digits_of_verify_at`, `soundOpened_level_digits_of_verify_at`
(Johnson/Goal/Skeleton/SoundOfVerifyMore.lean).
STATED OF A STAND-IN DESCRIPTION, NOT OF `theDescription`: it keeps its
verifier (`verify_theWide`) and its extractor (`same_extractor_wide`,
Johnson/Goal/SameExtractorWide.lean) and adds a committer; no theorem ties the committer to the
release's program that commits. Nothing on hiding. The
limits of Johnson/Goal/TopOfThreeBinding.lean, of WideDigits.lean and of the files that are called
travel whole.

-/
import Johnson.Goal.BindingOfCore
import Johnson.Goal.Conditions.MoreAtDigits

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

/-- **`SoundAndBinding` at one Z, of `theWide K W`, at `levelError`.** -/
theorem soundAndBinding_level_wide_at (K : TheCoins) (W : WideCoins K) (Z : VerifierAndGoals.PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z) (pS : ProofSoundAt Z) :
    SoundAndBinding (systemOfRecord (atSecondHashFunction (theWide K W)) Z (settingsOfRead pp)) levelError :=
  soundAndBinding_of_atZ_within _ soundnessErrorInQueries bindingErrorInQueries Z pp
    (soundUnderPolicyAtZ_bits_theWide K W Z pp scope hr kS pS) (G9bits_theWide K W) scope hr exact
    verifierQueryAllowance (parserWithin_of_verifierWithin (verifierWithin_theWide K W OnBytes.secondHashFunction) Z scope)

/-- **`SoundOpened`**, at twice that error. -/
theorem soundOpened_level_wide_at (K : TheCoins) (W : WideCoins K) (Z : VerifierAndGoals.PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z) (pS : ProofSoundAt Z) :
    SoundOpened (systemOfRecord (atSecondHashFunction (theWide K W)) Z (settingsOfRead pp)) fun t =>
      2 * levelError t :=
  soundOpened_of_soundAndBinding _ _ (soundAndBinding_level_wide_at K W Z pp scope hr exact kS pS)

section
variable (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
  (read : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
  (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
  (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
    (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
      KindsConds h h.free)
  (core : protocolDataWellFormed (asDescriptionFiles Z) = true → P5J.coreAt Z = true)
include scope read exact owed kinds core

/-- **`SoundAndBinding` at Z, of `theWideDigits`, at `levelError`, from the core top's own
hypotheses.** -/
theorem soundAndBinding_level_digits_of_core_at :
    SoundAndBinding (systemOfRecord (atSecondHashFunction theWideDigits) Z (settingsOfRead pp)) levelError :=
  soundAndBinding_level_wide_at digitCoins digitWide Z pp scope read exact
    (keySound_at_live_holds Z scope) (proofSoundAt_of_core Z pp scope read owed kinds core)

/-- **`SoundOpened`**, at twice that error. -/
theorem soundOpened_level_digits_of_core_at :
    SoundOpened (systemOfRecord (atSecondHashFunction theWideDigits) Z (settingsOfRead pp)) fun t =>
      2 * levelError t :=
  soundOpened_level_wide_at digitCoins digitWide Z pp scope read exact
    (keySound_at_live_holds Z scope) (proofSoundAt_of_core Z pp scope read owed kinds core)

end

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.soundAndBinding_level_wide_at
#print axioms VerifierAndGoals.AtTheName.soundOpened_level_wide_at
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_level_digits_of_core_at
#print axioms VerifierAndGoals.AtTheName.soundOpened_level_digits_of_core_at
