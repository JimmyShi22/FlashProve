-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/SoundOfBareLawsCore.lean: `sound_of_bare_laws_core_at`: soundness of the
name's system of record at one set of public files Z, FROM THE BARE LAWS OF THE FIRST CHAIN'S KINDS
AND TWO TESTS ON THE PUBLIC FILES, and from nothing else. IT COMPILES OVER THE PROOF FILE'S ENTRY
TESTS AS A LIST OF THIRTEEN ROWS AND OVER THE LIST OF FOURTEEN.

It is `sound_of_bare_laws_free_at` (Johnson/Goal/Skeleton/SoundOfBareLawsFree.lean) with its
hypothesis on the last chain, `h.LastLeftAt`, paid by the theorem
`P5J.lastLeft_of_coreAt` (Johnson/P2LawR/CoreAtFiles.lean) from `P5J.coreAt Z = true`.

THE HYPOTHESES, all at the one Z (in scope, read as pp, with exact match), where `protocolDataWellFormed` accepts:
  `owed`    `At.CondsOwed Z`: `rowsRead Z`: one test with code on the three public files; over
           thirteen entry tests no test that `verify` runs asks it; over fourteen the fourteenth
           asks its like, and SoundOfBareLawsDoor.lean has `owed` from it
  `kinds`   under every head: `KindsLaws h h.free`: sixteen bare fields: the laws of K1 to K13
           (K12's behind a condition that is paid here); K14's and K15's, which are free: these
           kinds have no place on the first chain; and "frame": the law of the rows of the fold's
           own text, which is no numbered kind of sub-protocol
  `core`    `P5J.coreAt Z = true`: one Bool of the three public files: fifteen named tests on the
           plan of the last chain's own proximity test, at the letters that the files give; no test
           that `verify` runs asks it.

SO NO KIND'S NAMED CONDITION, NO JOINING ROW, NO SHARE OF THE TWO LATER CHAINS, NO FACT ON REACHED
STATES, AND NOTHING ON THE KEY FILE OR THE COPY'S FILE IS A HYPOTHESIS HERE.

Limits. One call: it pays nothing. The limits of the files that are called hold here too.
No evaluation of `coreAt` at any files is told in this library (CoreAtFiles.lean's head):
if it is false at the release's files this theorem says nothing there. The head stands
over the fourteen entry tests, two of which compare the plan with values
written for the full size; one of the tests beneath has been evaluated FALSE at the stored small
files: at the small size this theorem says nothing. NO KIND'S LAW IS PROVED HERE. Elsewhere in this
library two of the three hypotheses are not left open: kinds is a theorem under every head
(`kindsLaws_at_head`, KindsLawsAtHead.lean; that there is a head is proved at `VerifierAndGoals.storedPublicFiles` and
`VerifierAndGoals.zGap` (at secondHashFunction, with `fixedConfigurationDigest` in the digest's place; side library AtFullSide/Top/); at
other files: evaluated, not proved),
and owed follows from the live test's yes (`P5J.owed_of_live`, OwedOfLive.lean), because `verify`
itself asks its like, as the fourteenth entry test: from the other thirteen it is not proved.
The third, core, is not needed: SoundOfBareLawsHead.lean states its top without it, and has what
core paid from the head alone. What these are worth is told in the head of SoundOfVerifyAt.lean.

-/
import Johnson.Goal.Skeleton.SoundOfBareLawsFree
import Johnson.P2LawR.CoreAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals FlashProve FlashProve
open P5J

/-- **SOUNDNESS AT ONE SET OF PUBLIC FILES, FROM THE KINDS' BARE LAWS AND TWO TESTS ON THE PUBLIC
FILES.** -/
theorem sound_of_bare_laws_core_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free)
    (core : protocolDataWellFormed (asDescriptionFiles Z) = true → P5J.coreAt Z = true) :
    VerifiableInference.Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_of_bare_laws_free_at Z pp scope read exact owed kinds
    fun hl _ _ _ _ h => P5J.lastLeft_of_coreAt (core hl) h

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.sound_of_bare_laws_core_at
