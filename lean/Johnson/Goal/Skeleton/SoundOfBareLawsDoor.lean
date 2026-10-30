-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/SoundOfBareLawsDoor.lean: `sound_of_bare_laws_door_at`: soundness of the
name's system of record at one set of public files Z, FROM THE BARE LAWS OF THE FIRST CHAIN'S KINDS
ALONE. OVER THE PROOF FILE'S ENTRY TESTS AS A LIST
OF FOURTEEN ROWS ALONE.

It is `sound_of_bare_laws_head_at` (Johnson/Goal/Skeleton/SoundOfBareLawsHead.lean) with its
hypothesis `owed` proved by `P5J.owed_of_live` (Johnson/Goal/Skeleton/OwedOfLive.lean): where
`protocolDataWellFormed` accepts, the entry tests have accepted; the fourteenth of them is
`rowsMadeB`, and its law gives `rowsRead Z`.

THE ONE HYPOTHESIS, at the one Z (in scope, read as pp, with exact match), where `protocolDataWellFormed` accepts:
  `kinds`   under every head: `KindsLaws h h.free`: sixteen bare fields: the laws of K1 to K13
           (K12's behind a condition on the public files, `H2K12.LastTypedAt`, which
           `H2K12.lastTypedAt_of_live` proves in scope where `protocolDataWellFormed` accepts); K14's and K15's,
           which are free; and
           "frame": the law of the rows of the fold's own text, which is no numbered kind of
           sub-protocol.

SO, BEYOND THE THREE IN THE STATEMENT (in scope, read as pp, exact match), NO TEST ON THE PUBLIC
FILES IS ASSUMED THAT `verify` DOES NOT RUN ITSELF. Of the three `verify` runs the first, which
reads the files (`verifyAt InScope`, Ladder.lean); that it tests exact match is not claimed.

A second theorem, `sound_of_conditions_door_at`: the same with `KindsConds` in the bare laws' place
(Johnson/Goal/Skeleton/KindsOfConds.lean says what stands there).

Limits. CALLS ALONE: THEY PROVE NOTHING OF THEIR OWN. Those of the files that are called. It speaks
of the
verifier WITH FOURTEEN ENTRY TESTS: where the fourteenth rejects public files that the thirteen
accept, that verifier rejects more. At the full size alone. NO KIND'S LAW IS PROVED HERE. Elsewhere
in this library the first theorem's hypothesis is not left open: kinds is a theorem under every head
(`kindsLaws_at_head`, KindsLawsAtHead.lean; a head is proved at `VerifierAndGoals.storedPublicFiles` (a written copy, not
the release's files) alone (side library, `headMember_zFull`)). What that is worth is told in the
head of SoundOfVerifyAt.lean. The second theorem asks `KindsConds`: no theorem of this library ends
in it: THAT CONDITION IS NOT SHOWN TO BE MET IN LEAN AT ANY Z.
-/
import Johnson.Goal.Skeleton.SoundOfBareLawsHead
import Johnson.Goal.Skeleton.OwedOfLive

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals FlashProve FlashProve
open P5J

/-- **SOUNDNESS AT ONE SET OF PUBLIC FILES, FROM THE KINDS' BARE LAWS ALONE.** -/
theorem sound_of_bare_laws_door_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    VerifiableInference.Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_of_bare_laws_head_at Z pp scope read exact (fun hl => owed_of_live hl) kinds

/-- The same with `KindsConds` in the bare laws' place. -/
theorem sound_of_conditions_door_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsConds h h.free) :
    VerifiableInference.Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_of_conditions_head_at Z pp scope read exact (fun hl => owed_of_live hl) kinds

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.sound_of_bare_laws_door_at
#print axioms VerifierAndGoals.AtTheName.sound_of_conditions_door_at
