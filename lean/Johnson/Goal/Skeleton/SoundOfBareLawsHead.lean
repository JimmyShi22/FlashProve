-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/SoundOfBareLawsHead.lean: `sound_of_bare_laws_head_at`: soundness of the
name's system of record at one set of public files Z, FROM THE BARE LAWS OF THE FIRST CHAIN'S KINDS
AND ONE TEST ON THE PUBLIC FILES, and from nothing else. IT COMPILES OVER THE PROOF FILE'S ENTRY
TESTS AS A LIST OF THIRTEEN ROWS AND AS ONE OF FOURTEEN.

It is `sound_of_bare_laws_free_at` (Johnson/Goal/Skeleton/SoundOfBareLawsFree.lean) with its
hypothesis on the last chain, `h.LastLeftAt`, paid by the theorem
`P5J.AtMgA.lastLeft_at_head_alone` (Johnson/P2LawR/LastLeftAlone.lean) from the head alone. Against
`sound_of_bare_laws_core_at`: the test `coreAt Z` is no hypothesis any more; against
`sound_of_bare_laws_rad_at`: nor is `IM.Seats.radWB`.

THE HYPOTHESES, all at the one Z (in scope, read as pp, with exact match), where `protocolDataWellFormed` accepts:
  `owed`    `At.CondsOwed Z`: `rowsRead Z`: one test with code on the three public files; over
           thirteen entry tests no test that `verify` runs asks it; over fourteen the fourteenth
           asks its like, and SoundOfBareLawsDoor.lean has `owed` from it
  `kinds`   under every head: `KindsLaws h h.free`: sixteen bare fields: the laws of K1 to K13
           (K12's behind a condition that is paid here); K14's and K15's, which are free; and
           "frame": the law of the rows of the fold's own text, which is no numbered kind of
           sub-protocol.

A second theorem, `sound_of_conditions_head_at`: the same with `KindsConds` in the bare laws' place
(Johnson/Goal/Skeleton/KindsOfConds.lean says what stands there).

Limits. CALLS ALONE: THEY PAY NOTHING. Those of the files that are called: the last chain's row now
rests whole on theorems "from the head": what these are worth is what the head is worth: it stands
over fourteen entry tests, two of which compare the plan with values written for the full size, and
a member of it is proved at `VerifierAndGoals.storedPublicFiles` (a written copy, not the release's files) alone (side
library, `AtFullSide.Top.headMember_zFull`). At the full size alone. NO KIND'S LAW IS PROVED HERE.
Elsewhere in this library neither hypothesis of the first theorem is left open: kinds is a theorem
under every head (`kindsLaws_at_head`, KindsLawsAtHead.lean; on a head, see above), and owed follows
from the live test's yes (`P5J.owed_of_live`, OwedOfLive.lean), because `verify` itself asks its
like, as the fourteenth entry test: from the other thirteen it is not proved. What these are
worth is told in the head of SoundOfVerifyAt.lean. The second theorem asks `KindsConds`: no theorem
of this library ends in it: THAT CONDITION IS NOT SHOWN TO BE MET IN LEAN AT ANY Z.
-/
import Johnson.Goal.Skeleton.SoundOfBareLawsFree
import Johnson.P2LawR.LastLeftAlone

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals FlashProve FlashProve
open P5J

/-- **SOUNDNESS AT ONE SET OF PUBLIC FILES, FROM THE KINDS' BARE LAWS AND ONE TEST ON THE PUBLIC
FILES.** -/
theorem sound_of_bare_laws_head_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    VerifiableInference.Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_of_bare_laws_free_at Z pp scope read exact owed kinds
    fun _ _ _ _ _ h => h.lastLeft_at_head_alone

/-- The same with `KindsConds` in the bare laws' place. -/
theorem sound_of_conditions_head_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsConds h h.free) :
    VerifiableInference.Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_of_conditions_free_of_bare Z pp scope read exact owed kinds
    fun _ _ _ _ _ h => h.lastLeft_at_head_alone

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.sound_of_bare_laws_head_at
#print axioms VerifierAndGoals.AtTheName.sound_of_conditions_head_at
