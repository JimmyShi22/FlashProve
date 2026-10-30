-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/SoundOfKindsAtZ.lean: `sound_of_kinds_at`: soundness of the name's system of
record AT ONE SET OF PUBLIC FILES Z, from the named conditions AT THAT Z ALONE.

Why. `sound_of_kinds` (Johnson/Goal/Skeleton/SoundOfKindsTop.lean) asks its conditions at every Z in
scope at which `protocolDataWellFormed` accepts: where one fails at one such Z it says nothing, at the release's
files either. What is shown of the conditions that are no laws is shown by evaluations at single
sets of files. Here the conclusion and every condition stand at one Z.
  `sound_of_kinds_at`: Z in scope, read as pp, with exact match. From: `KeySoundAt Z`
    (Johnson/Goal/Skeleton/TopAtZ.lean); and, where `protocolDataWellFormed` accepts at Z: `P5J.At.Conds Z`,
    `H2K12.LastTypedAt` at Z's files, and `ProofKinds h` under every head h at the name (one law for
    each kind of sub-protocol, and five rows). The end: `Sound` of
    `systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp)` at fun t => `VerifierAndGoals.soundnessErrorInQueries` t 1:
    the body of `NearestSound theDescription fun t => VerifierAndGoals.soundnessErrorInQueries t 1` (Ladder/Package.lean) at Z.
One call of `sound_at`, `proofSound_at_of_proofFileAt` (TopAtZ.lean) and `proofFileAt_of_kinds`.

Limits. NO CONDITION IS SHOWN TO BE MET IN THIS FILE; each is had elsewhere in this library, under
the live test's yes (which is evaluated at the release's files, not proved), on the road of
`sound_of_verify_at` (SoundOfVerifyAt.lean), whose head says what that is worth. The laws of the
kinds, the five rows and `KeySoundAt Z` are hypotheses here, theorems on that road. Where `protocolDataWellFormed`
rejects at Z nothing is asked but `KeySoundAt Z`, which asks nothing there: the three gates reject
all. The limits of the two files that are called stand. It stands beside the goals' form, not in its
place.

-/
import Johnson.Goal.Skeleton.TopAtZ
import Johnson.Goal.Skeleton.SoundOfKindsTop

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open P5J

/-- **SOUNDNESS AT ONE SET OF PUBLIC FILES, FROM THE NAMED CONDITIONS AT THESE FILES.** -/
theorem sound_of_kinds_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (read : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (conds : protocolDataWellFormed (asDescriptionFiles Z) = true → At.Conds Z)
    (lastTyped : protocolDataWellFormed (asDescriptionFiles Z) = true →
      H2K12.LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x), ProofKinds h) :
    Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_at Z pp scope read exact kS fun hl =>
    proofSound_at_of_proofFileAt Z scope hl
      (proofFileAt_of_kinds Z scope hl (conds hl) (lastTyped hl) (kinds hl))

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.sound_of_kinds_at
