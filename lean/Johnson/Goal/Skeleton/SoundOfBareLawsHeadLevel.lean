-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Goal/Skeleton/SoundOfBareLawsHeadLevel.lean: THE TWO STATEMENTS THAT READ OPENINGS, AT
THE CLOSED STAND-IN `theWideDigits`, AT THE WRITTEN ERROR `levelError`, FROM THE CONDITIONS OF
`sound_of_bare_laws_head_at`: owed (the one reading condition) and kinds (every kind's law a
bare field). Calls alone.

Why. Johnson/Goal/Skeleton/SoundOfBareLawsHeadNearest.lean has the two at `theWideDigits` at
`joinError soundnessErrorInQueries …`, which charges the parser 2^48 queries (about 2^-76 at no query), and at
`levelError` only at `theBound K`, WHERE THE CLAUSE ON OPENING-FORM BINDING IS WITHOUT CONTENT (its
bound is 0). Another file proves the form at one Z at
`theWide K W` at `levelError` (`soundAndBinding_level_wide_at`, `soundOpened_level_wide_at`,
Johnson/Goal/BindingOfCoreLevel.lean), and from it the pair with the kinds' conditions
(`KindsConds`). Here is the pair with every kind's law a bare field (`KindsLaws`).
`levelError t` := the larger of `soundnessErrorInQueries t verifierQueryAllowance` and `bindingErrorInQueries t` (Ladder/PackageBits.lean):
the parser is charged 2^23.

  `soundAndBinding_level_digits_of_bare_laws_head_at`,
  `soundOpened_level_digits_of_bare_laws_head_at`:
    at one set of public files Z, in scope, read, at the exact-match policy: at `levelError` and at
    twice it.
  `nearestSoundAndBinding_level_digits_of_bare_laws_head`,
  `nearestSoundOpened_level_digits_of_bare_laws_head`:
    the goals' own nearest forms, from the conditions at every set in scope where the live test
    accepts. WHERE ONE CONDITION FAILS AT ONE SUCH SET,
    THESE TWO SAY NOTHING AT ALL; the two at one Z still speak at the other sets.

Limits. THEY PAY NO LAW AND NO CONDITION. kinds is the whole list of the kinds' laws. Elsewhere in
this library neither condition is left open: kinds is a theorem under every head
(`kindsLaws_at_head`, KindsLawsAtHead.lean; that there is a head is proved at `VerifierAndGoals.storedPublicFiles` and
`VerifierAndGoals.zGap` (at secondHashFunction, with `fixedConfigurationDigest` in the digest's place; side library AtFullSide/Top/); at
other files: evaluated, not proved), and owed follows from the live test's yes (`P5J.owed_of_live`,
OwedOfLive.lean), because `verify` itself asks its like, as the fourteenth entry test: from the
other thirteen it is not proved. What these are worth is told in the head of
SoundOfVerifyAt.lean, whose limits hold of every theorem here once the premises are struck. OF A
STAND-IN, NOT OF `theDescription`, whose own committer is hollow: `theWideDigits` keeps its verifier
and adds a committer, which is tied to no program; the limits of Johnson/Goal/TopAtZBinding.lean and
BindingOfCoreLevel.lean travel whole. Nothing on completeness; nothing on zero knowledge.
No soundness is claimed.

-/
import Johnson.Goal.Skeleton.SoundOfBareLawsHeadNearest
import Johnson.Goal.BindingOfCoreLevel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open P5J

/-- **`SoundAndBinding` at Z, of `theWideDigits`, at `levelError`, every kind's law a bare
field.** -/
theorem soundAndBinding_level_digits_of_bare_laws_head_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    SoundAndBinding (systemOfRecord (atSecondHashFunction theWideDigits) Z (settingsOfRead pp)) levelError :=
  soundAndBinding_level_wide_at digitCoins digitWide Z pp scope read exact
    (keySound_at_live_holds Z scope) (proofSoundAt_of_bare_laws_head Z pp scope read owed kinds)

/-- **`SoundOpened`**, at twice that error. -/
theorem soundOpened_level_digits_of_bare_laws_head_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    SoundOpened (systemOfRecord (atSecondHashFunction theWideDigits) Z (settingsOfRead pp)) fun t =>
      2 * levelError t :=
  soundOpened_level_wide_at digitCoins digitWide Z pp scope read exact
    (keySound_at_live_holds Z scope) (proofSoundAt_of_bare_laws_head Z pp scope read owed kinds)

/-- **The goals' `NearestSoundAndBinding` at `theWideDigits`, at `levelError`.** -/
theorem nearestSoundAndBinding_level_digits_of_bare_laws_head
    (owed : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    NearestSoundAndBinding theWideDigits levelError :=
  fun Z pp scope read ex =>
    soundAndBinding_level_digits_of_bare_laws_head_at Z pp scope read ex (owed Z scope)
      (kinds Z scope)

/-- **And `NearestSoundOpened`**, at twice that error. -/
theorem nearestSoundOpened_level_digits_of_bare_laws_head
    (owed : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    NearestSoundOpened theWideDigits fun t => 2 * levelError t :=
  fun Z pp scope read ex =>
    soundOpened_level_digits_of_bare_laws_head_at Z pp scope read ex (owed Z scope)
      (kinds Z scope)

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.soundAndBinding_level_digits_of_bare_laws_head_at
#print axioms VerifierAndGoals.AtTheName.soundOpened_level_digits_of_bare_laws_head_at
#print axioms VerifierAndGoals.AtTheName.nearestSoundAndBinding_level_digits_of_bare_laws_head
#print axioms VerifierAndGoals.AtTheName.nearestSoundOpened_level_digits_of_bare_laws_head
