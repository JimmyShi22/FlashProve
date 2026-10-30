-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOfflineSides.lean: OfflineSidesAreWhole at thePartsAt, in scope and live.

  offlineSides_whole   no offline side is missing, at the description that the files make
  offlineTestOnOmega_there, offlineSenders_placed   OfflineHasATestOnOmega, OfflineSendersAtTheirPlaces

From E2E/KeyValueHolds.lean's halved_value, rooted_value, at the value as it stands in
E2E/KeyArgumentsAt.lean, by thePartsAt_of; sealPlain_key is the 198's (E2E/KeyAcceptAtFiles.lean, on no
row). Limits. In scope and live: L25's proposition bears no such premise, and out of scope this says nothing:
a join that takes OfflineSidesAreWhole bare cannot be paid from here: it takes scope and live and
calls offlineSides_whole. The two tests read a half's place and roots alone: a half stands at each of
the sixteen places that send; they say nothing of how many rounds it plays or what it sends, and they
hold at any value of the tests' numbers, noP12's arm included. They pass at a prover with no part at
the four tests: E2E/KeyOfflineSidesControl.lean. That the prover is not silent rests on ready and T2.
offlineSenders_placed is AtPlaces: seven places of chain 1, not the sixteen; the look0, look1 faces are
not asked there. Nothing on any property.
-/
import E2E.KeyThePartsFacts
import E2E.KeyNoDefaultBites
import E2E.TheHonestProverStatements
import E2E.KeyValueHolds
import E2E.KeyAcceptAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open AtPublicFiles.KeyValueHolds (valueAt halved_value rooted_value place_p12At)
open AtPublicFiles.KeyPartsIdle (fixedKeyParts)
open AtPublicFiles.KeyValues (faceAt keyBatt oneOf matrixEntryOf multiplicitiesGroups)
open ProofFile.Honest.Term (matrixInput tableCoins)

variable {files : PublicFiles}

/-- **No offline side is missing, in scope and live.** -/
theorem offlineSides_whole (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true) :
    OfflineSidesAreWhole (thePartsAt files) := by
  intro description hd
  have sourced := sourced_of_ok live hd
  have hW := (noDefaultBites scope live hd).hasW
  have hsp := senders_split scope live hd
  rw [thePartsAt_of hd]
  refine ⟨?_, ?_, AtPublicFiles.AtFiles.sealPlain_key _ _ _⟩
  · exact halved_value
      (fixedKeyParts (faceAt description.source 0) (keyBatt description.source) matrixInput.dummy () ()
        idleRecord) description.source description.numbers description.later matrixReader
      (tableCoins files) matrixInput.inRange matrixInput.dummy (offlineTestParametersOnU description.later)
      (offlineTestOnOmega description.later) (matrixEntryOf matrixReader) (multiplicitiesGroups description.source) 0
      scope sourced.named hW hsp (place_p12At _ _) (place_p12At _ _)
  · exact rooted_value
      (fixedKeyParts (faceAt description.source 0) (keyBatt description.source) matrixInput.dummy () ()
        idleRecord) description.source description.numbers description.later matrixReader
      (tableCoins files) matrixInput.inRange matrixInput.dummy (offlineTestParametersOnU description.later)
      (offlineTestOnOmega description.later) (matrixEntryOf matrixReader) (multiplicitiesGroups description.source) 0
      scope sourced.named hW hsp (place_p12At _ _) (place_p12At _ _)

/-- **The offline description has a test on the group Omega, in scope and live.** -/
theorem offlineTestOnOmega_there (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) : OfflineHasATestOnOmega files :=
  fun _ hd => (noDefaultBites scope live hd).omega

/-- **The offline senders stand at their places, in scope and live.** -/
theorem offlineSenders_placed (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) : OfflineSendersAtTheirPlaces (thePartsAt files) := by
  intro description hd
  have hW := (noDefaultBites scope live hd).hasW
  rw [thePartsAt_of hd]
  exact AtPublicFiles.KeyValueHolds.atPlaces_value
    (fixedKeyParts (faceAt description.source 0) (keyBatt description.source) matrixInput.dummy () ()
      idleRecord) description.source description.numbers description.later matrixReader
    (tableCoins files) matrixInput.inRange matrixInput.dummy (offlineTestParametersOnU description.later)
    (offlineTestOnOmega description.later) (matrixEntryOf matrixReader) (multiplicitiesGroups description.source) 0 hW

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.offlineSides_whole
#print axioms AtPublicFiles.AtFiles.HonestTerm.offlineTestOnOmega_there
#print axioms AtPublicFiles.AtFiles.HonestTerm.offlineSenders_placed
