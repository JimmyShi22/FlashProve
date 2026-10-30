-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Goal/Skeleton/SoundOfBareLawsDoorNearest.lean: THE GOALS' OWN FORMS, AND THE STATEMENTS
THAT READ OPENINGS, FROM THE KINDS' BARE LAWS ALONE. OVER THE LIST OF FOURTEEN ROWS OF THE ENTRY
TESTS ALONE.

The theorems of Johnson/Goal/Skeleton/SoundOfBareLawsHeadNearest.lean and
SoundOfBareLawsHeadLevel.lean with the premise owed struck: it is paid by `P5J.owed_of_live`
(Johnson/Goal/Skeleton/OwedOfLive.lean): where the live test accepts, the entry tests have accepted,
and the fourteenth of them gives the one reading condition. So they stand to
`sound_of_bare_laws_door_at` (Johnson/Goal/Skeleton/SoundOfBareLawsDoor.lean) as those stand to
`sound_of_bare_laws_head_at`. Calls alone.

THE ONE PREMISE: kinds: `KindsLaws h h.free` under every head, where the live test accepts: each
kind's law, whole, a bare field.

AT ONE SET OF PUBLIC FILES Z, in scope, read, at the exact-match policy:
  `proofSoundAt_of_bare_laws_door`: `ProofSoundAt Z` (this one without the premise of exact match).
  `soundAndBinding_plain_of_bare_laws_door_at`, `soundOpened_plain_of_bare_laws_door_at`: of the
    name's system of record with the committer written in Lean beside the IOP, a placeholder that
    corresponds to no program of the release (`plainSystemAt`), at `plainError` and at twice it.
  **`soundAndBinding_level_digits_of_bare_laws_door_at`**,
  **`soundOpened_level_digits_of_bare_laws_door_at`**: of the closed stand-in `theWideDigits`, at
    `levelError` and at twice it.
OVER ALL SETS IN SCOPE, kinds asked at every one where the live test accepts:
  **`nearestSound_of_bare_laws_door`**: `NearestSound theDescription` at `VerifierAndGoals.soundnessErrorInQueries t 1`: OF THE
    NAME ITSELF.
  **`nearestSoundAndBinding_level_digits_of_bare_laws_door`**,
  **`nearestSoundOpened_level_digits_of_bare_laws_door`**: the goals' two nearest forms that read
    openings, at `theWideDigits`, at `levelError` and at twice it.
  `nearestSoundAndBinding_bound_of_bare_laws_door`, `nearestSoundOpened_bound_of_bare_laws_door`:
    the same two at `theBound K`. AT `theBound K` THE CLAUSE ON OPENING-FORM BINDING IS WITHOUT
    CONTENT (its bound is 0): whoever cites this pair cites it with that sentence.
  The pair at `theWideDigits` at `joinError` is not repeated: it is the weaker form.

WHAT THE FORM OVER ALL SETS COSTS. WHERE kinds FAILS AT ONE SET IN SCOPE AT WHICH THE LIVE TEST
ACCEPTS, THE FIVE NEAREST FORMS SAY NOTHING AT ALL, at any set; the statements at one Z still speak
at each of the other sets.

Limits. THEY PAY NO LAW. NO KIND's LAW IS PROVED HERE: kinds is the whole list of the kinds' laws.
Elsewhere in this library it is not left open: kinds is a theorem under every head
(`kindsLaws_at_head`, KindsLawsAtHead.lean; that there is a head is proved at `VerifierAndGoals.storedPublicFiles` and
`VerifierAndGoals.zGap` (at secondHashFunction, with `fixedConfigurationDigest` in the digest's place; side library AtFullSide/Top/); at
other files: evaluated, not proved). What that is worth is told in the head of SoundOfVerifyAt.lean,
whose limits hold of every theorem here once the premise is struck. They speak of THE VERIFIER WITH
FOURTEEN ENTRY TESTS: where the fourteenth rejects public files that the thirteen accept, that
verifier rejects more. `plainSystemAt` has the written committer in the place of the description's
own, which is hollow; the stand-ins keep `theDescription`'s verifier and add a committer; no
committer here is tied to a program. The limits of Johnson/Goal/TopAtZBinding.lean and
BindingOfCoreLevel.lean travel whole. Nothing on completeness; nothing on zero knowledge.
No soundness is claimed.

-/
import Johnson.Goal.Skeleton.SoundOfBareLawsDoor
import Johnson.Goal.Skeleton.SoundOfBareLawsHeadNearest
import Johnson.Goal.Skeleton.SoundOfBareLawsHeadLevel

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

/-! ## At one set of public files -/

/-- **The kinds' bare laws at Z give `ProofSoundAt Z`.** -/
theorem proofSoundAt_of_bare_laws_door (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    ProofSoundAt Z :=
  proofSoundAt_of_bare_laws_head Z pp scope read (fun hl => owed_of_live hl) kinds

/-- **`SoundAndBinding` (VerifiableInference/Statements.lean) of the name's system of record with
the committer written in Lean beside the IOP, a placeholder that corresponds to no program of the
release, at one set of public files, from the kinds' bare laws alone.** -/
theorem soundAndBinding_plain_of_bare_laws_door_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free)
    (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    SoundAndBinding (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove)
      plainError :=
  soundAndBinding_plain_of_bare_laws_head_at Z pp scope read exact (fun hl => owed_of_live hl)
    kinds b sample prove

/-- **`SoundOpened` of it**, at twice the error. -/
theorem soundOpened_plain_of_bare_laws_door_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free)
    (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    SoundOpened (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove)
      fun t => 2 * plainError t :=
  soundOpened_plain_of_bare_laws_head_at Z pp scope read exact (fun hl => owed_of_live hl)
    kinds b sample prove

/-- **`SoundAndBinding` at Z, of `theWideDigits`, at `levelError`, from the kinds' bare laws
alone.** -/
theorem soundAndBinding_level_digits_of_bare_laws_door_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    SoundAndBinding (systemOfRecord (atSecondHashFunction theWideDigits) Z (settingsOfRead pp)) levelError :=
  soundAndBinding_level_digits_of_bare_laws_head_at Z pp scope read exact
    (fun hl => owed_of_live hl) kinds

/-- **`SoundOpened`**, at twice that error. -/
theorem soundOpened_level_digits_of_bare_laws_door_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    SoundOpened (systemOfRecord (atSecondHashFunction theWideDigits) Z (settingsOfRead pp)) fun t =>
      2 * levelError t :=
  soundOpened_level_digits_of_bare_laws_head_at Z pp scope read exact
    (fun hl => owed_of_live hl) kinds

/-! ## Over all sets of public files in scope -/

/-- **THE GOALS' NEAREST FORM OF SOUNDNESS, OF THE NAME ITSELF, FROM THE KINDS' BARE LAWS ALONE AT
EVERY Z.** -/
theorem nearestSound_of_bare_laws_door
    (kinds : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    NearestSound theDescription fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  fun Z pp scope read ex => sound_of_bare_laws_door_at Z pp scope read ex (kinds Z scope)

/-- **The goals' `NearestSoundAndBinding` at `theWideDigits`, at `levelError`.** -/
theorem nearestSoundAndBinding_level_digits_of_bare_laws_door
    (kinds : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    NearestSoundAndBinding theWideDigits levelError :=
  nearestSoundAndBinding_level_digits_of_bare_laws_head (fun _ _ hl => owed_of_live hl) kinds

/-- **And `NearestSoundOpened`**, at twice that error. -/
theorem nearestSoundOpened_level_digits_of_bare_laws_door
    (kinds : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    NearestSoundOpened theWideDigits fun t => 2 * levelError t :=
  nearestSoundOpened_level_digits_of_bare_laws_head (fun _ _ hl => owed_of_live hl) kinds

/-- `NearestSoundAndBinding` at the stand-in `theBound K`, WHERE THE CLAUSE ON OPENING-FORM BINDING
IS WITHOUT CONTENT (its bound is 0). -/
theorem nearestSoundAndBinding_bound_of_bare_laws_door (K : TheCoins)
    (kinds : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    NearestSoundAndBinding (theBound K) levelError :=
  nearestSoundAndBinding_bound_of_bare_laws_head K (fun _ _ hl => owed_of_live hl) kinds

/-- `NearestSoundOpened` at it, at twice the error: with the same caution. -/
theorem nearestSoundOpened_bound_of_bare_laws_door (K : TheCoins)
    (kinds : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    NearestSoundOpened (theBound K) fun t => 2 * levelError t :=
  nearestSoundOpened_bound_of_bare_laws_head K (fun _ _ hl => owed_of_live hl) kinds

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.proofSoundAt_of_bare_laws_door
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_plain_of_bare_laws_door_at
#print axioms VerifierAndGoals.AtTheName.soundOpened_plain_of_bare_laws_door_at
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_level_digits_of_bare_laws_door_at
#print axioms VerifierAndGoals.AtTheName.soundOpened_level_digits_of_bare_laws_door_at
#print axioms VerifierAndGoals.AtTheName.nearestSound_of_bare_laws_door
#print axioms VerifierAndGoals.AtTheName.nearestSoundAndBinding_level_digits_of_bare_laws_door
#print axioms VerifierAndGoals.AtTheName.nearestSoundOpened_level_digits_of_bare_laws_door
#print axioms VerifierAndGoals.AtTheName.nearestSoundAndBinding_bound_of_bare_laws_door
#print axioms VerifierAndGoals.AtTheName.nearestSoundOpened_bound_of_bare_laws_door
