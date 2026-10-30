-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/SoundOfBareLawsFree.lean: `sound_of_bare_laws_free_at`: soundness of the
name's system of record at one set of public files Z, AT THE CLOSED FILLING of the tower's free
letters (`h.free`), WITH EVERY KIND'S LAW OF THE FIRST CHAIN ASKED WHOLE, AS A BARE FIELD, and with
all three joining rows, the shared chain's row, the key file's condition and the closed tests paid
by their own files' theorems. IT COMPILES OVER THE PROOF FILE'S ENTRY TESTS AS A LIST OF
THIRTEEN ROWS AND AS ONE OF FOURTEEN.

Why. `sound_of_conditions_free_at` asks the first chain's kinds through `KindsConds`, where a
kind's own named condition may stand in a law's place; some of these conditions hold facts on
reached states or parts of another row. Here no kind's own condition stands: the hypothesis on the
first chain is the list of the kinds' laws and nothing else, and it cannot be emptied by a
condition.

It is `sound_of_kinds_at_free` (Johnson/Goal/Skeleton/SoundOfKindsAtFree.lean) at
`keySound_at_live_holds`, `conds_of_laid`,
`H2K12.lastTypedAt_of_live` and `P5J.five_at_free2_laid2` (Johnson/P5J/FiveAtFree2Laid2.lean).

THE HYPOTHESES, all at the one Z (in scope, read as pp, with exact match), where `protocolDataWellFormed` accepts:
  `owed`    `At.CondsOwed Z`: `rowsRead Z`: one test with code on the three public files; over
           thirteen entry tests no test that `verify` runs asks it; over fourteen the fourteenth
           asks its like, and SoundOfBareLawsDoor.lean has `owed` from it
  `kinds`   under every head: `KindsLaws h h.free`: sixteen bare fields (two are free: K14 and K15
           have no place on the first chain; K12's stands behind a condition that is paid here).
           ONE OF THEM, "frame", IS NO KIND OF SUB-PROTOCOL: the rows of the fold's own text.
  `last`    under every head: `h.LastLeftAt` (Johnson/P5J/L0/LastLeftAt.lean): what is left of the
           last chain's row, at closed terms of the head.

A second theorem, `sound_of_conditions_free_of_bare`: the hypotheses with the kinds' own conditions
give the bare ones: so `sound_of_conditions_free_at`'s statement follows from this one.

Limits. CALLS ALONE: THEY PAY NOTHING. Those of the files that are called. NO LAW IS PROVED HERE.
Elsewhere in this library none of the first theorem's three hypotheses is left open: kinds is a
theorem under every head (`kindsLaws_at_head`, KindsLawsAtHead.lean; a head is proved at a written
copy alone, not the release's files (see `headMember_zFull`)); owed follows from the live test's yes
(`P5J.owed_of_live`, OwedOfLive.lean), because `verify` itself asks its like, as the fourteenth
entry test: from the other thirteen it is not proved; and last is a theorem from the head
alone (`P5J.AtMgA.lastLeft_at_head_alone`, Johnson/P2LawR/LastLeftAlone.lean). What these are worth
is told in the head of SoundOfVerifyAt.lean. The second theorem asks `KindsConds`: no theorem of
this library ends in it: THAT CONDITION IS NOT SHOWN TO BE MET IN LEAN AT ANY Z.
-/
import Johnson.Goal.Skeleton.SoundOfCondsAtFree
import Johnson.Goal.Skeleton.CondsOfLaid
import Johnson.Loose.H2K12.LastTypedOfLaid
import Johnson.Goal.Conditions.KeyOpenHolds
import Johnson.P5J.FiveAtFree2Laid2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals FlashProve FlashProve
open P5J

/-- **SOUNDNESS AT ONE SET OF PUBLIC FILES, AT THE CLOSED FILLING, EVERY KIND'S LAW A BARE
FIELD.** -/
theorem sound_of_bare_laws_free_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free)
    (last : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        h.LastLeftAt) :
    VerifiableInference.Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_of_kinds_at_free Z pp scope read exact (keySound_at_live_holds Z scope)
    (fun hl => conds_of_laid scope hl read (owed hl))
    (fun hl => H2K12.lastTypedAt_of_live Z scope hl) kinds
    fun hl Zp Np cF x h => five_at_free2_laid2 h hl (last hl Zp Np cF x h)

/-- The statement with the kinds' own conditions follows from the one with the bare laws. -/
theorem sound_of_conditions_free_of_bare (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsConds h h.free)
    (last : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        h.LastLeftAt) :
    VerifiableInference.Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_of_bare_laws_free_at Z pp scope read exact owed
    (fun hl Zp Np cF x h => kindsLaws_at_free (kinds hl Zp Np cF x h)) last

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.sound_of_bare_laws_free_at
#print axioms VerifierAndGoals.AtTheName.sound_of_conditions_free_of_bare
