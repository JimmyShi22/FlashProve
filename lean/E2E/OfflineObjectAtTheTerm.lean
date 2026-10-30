-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineObjectAtTheTerm.lean: THE OFFLINE OBJECT, IN ONE PLACE. The named value of the offline
prover's arguments, `thePartsAt files` (E2E/KeyArgumentsAt.lean), of which `theHonestProvers files` is
made, has the written book and plays `keyProver` (E2E/KeyProver.lean) at one value of the senders; and
the values at which the offline file's laws are stated are that value.

  `object_book`      (thePartsAt files).book = keyBook K₀, where fullPub = some K₀
  `object_types`     its three types are Unit, Unit and WitK
  `object_prover`    (thePartsAt files).prover d = keyProver (valueAt …), every letter of `valueAt`
                     (E2E/KeyValueHolds.lean) spelled, where the public files make the description d
  `object_values`    the three names under which that value stands are one: `senderValue d`
                     (E2E/OfflineRowsAtFiles.lean: the rows' laws), `AtPublicFiles.KeyStandWalked.offlineValue d`
                     (E2E/KeyStandWalked.lean: the stands' laws) and `valueAt …`
  `rowsAtTheTerm`    the offline file's rows `offlineRowsAt d offlineProverCoinCounts S c`, AT THE TYPE OF THE ROWS OF THE
                     NAMED VALUE: Sides … (thePartsAt files).book (Cz files).I ((Cz files).Pad × (Cz files).Rnd)
                     TableKey Unit (thePartsAt files).SharedState (thePartsAt files).OwnState
  `object_rows`      their three lists are the lists of the named value's prover, and their prover is it
  `object_offlineProver`, `object_provers`   the protocol's offline honest prover at the named value is
                     `offlineProverWithEncodedTable` at that book and that prover; `theHonestProvers files` is `honestProvers` there
  `object_where_live` where the public files' test says yes, in scope: a description, the written book,
                     the prover, and the sixteen places, in one sentence

That one file compiles over E2E/OfflineRowsAtFiles.lean and E2E/KeyStandWalked.lean shows that one
`keyProver` stands under both.

Limits. Equations between terms, by unfolding. Nothing says what the prover sends, nor that any row is
good. `IsProvK` (E2E/KeyExact.lean) is not stated here. Nothing on any property.
-/
import E2E.OfflineRowsAtFiles
import E2E.KeyStandWalked

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open OnBytes (TableKey)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyValues (WitK matrixEntryOf multiplicitiesGroups faceAt keyBatt)
open AtPublicFiles.KeyValueHolds (valueAt)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open AtPublicFiles.KeyPartsIdle (fixedKeyParts)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) objectAtTheTermValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) objectAtTheTermDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {files : PublicFiles}

/-- **The book of the named value is the written book.** -/
theorem object_book {K₀ : KeyPub} (hK : fullPub = some K₀) :
    (thePartsAt files).book = keyBook K₀ :=
  offlineBook_eq hK

/-- The three types of the named value. -/
theorem object_types : (thePartsAt files).SharedState = Unit ∧
    (thePartsAt files).OwnState = Unit ∧ (thePartsAt files).LookupInput = WitK :=
  ⟨rfl, rfl, rfl⟩

/-- **The prover of the named value is `keyProver` at one value of the senders, every letter
spelled.** -/
theorem object_prover {d : OfflineDescription} (h : offlineDescription files = .ok d) :
    (thePartsAt files).prover d = keyProver (valueAt
      (fixedKeyParts (faceAt d.source 0) (keyBatt d.source) matrixInput.dummy () () idleRecord) d.source
      d.numbers d.later matrixReader (tableCoins files) matrixInput.inRange matrixInput.dummy
      (H2U.proximityTestParametersAt foldedTestPlace d.later.U) (H2U.proximityTestParametersAt omegaTestPlace (d.later.O.getD d.later.U))
      (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0) := by
  have e1 : (thePartsAt files).senders = offlineSenders d := by
    show (match offlineDescription files with
      | .ok description => offlineSenders description
      | .error _ => fallbackSenders) = _
    rw [h]
  have e2 : (thePartsAt files).rangeGroups = multiplicitiesGroups d.source := by
    show (match offlineDescription files with
      | .ok description => multiplicitiesGroups description.source
      | .error _ => []) = _
    rw [h]
  show keyProver (AtPublicFiles.KeyLay.withTests (thePartsAt files).senders d.source d.numbers d.later
    (offlineTestParametersOnU d.later) (offlineTestOnOmega d.later) (matrixEntryOf matrixReader)
    (thePartsAt files).rangeGroups 0) = _
  rw [e1, e2]
  rfl

/-- **The three names of that value are one.** -/
theorem object_values (d : OfflineDescription) :
    senderValue (files := files) d = valueAt
      (fixedKeyParts (faceAt d.source 0) (keyBatt d.source) matrixInput.dummy () () idleRecord) d.source
      d.numbers d.later matrixReader (tableCoins files) matrixInput.inRange matrixInput.dummy
      (H2U.proximityTestParametersAt foldedTestPlace d.later.U) (H2U.proximityTestParametersAt omegaTestPlace (d.later.O.getD d.later.U))
      (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0 ∧
    AtPublicFiles.KeyStandWalked.offlineValue (files := files) d = valueAt
      (fixedKeyParts (faceAt d.source 0) (keyBatt d.source) matrixInput.dummy () () idleRecord) d.source
      d.numbers d.later matrixReader (tableCoins files) matrixInput.inRange matrixInput.dummy
      (H2U.proximityTestParametersAt foldedTestPlace d.later.U) (H2U.proximityTestParametersAt omegaTestPlace (d.later.O.getD d.later.U))
      (matrixEntryOf matrixReader) (multiplicitiesGroups d.source) 0 :=
  ⟨rfl, rfl⟩

/-- **The offline file's rows, at the type of the rows of the named value.** -/
def rowsAtTheTerm (d : OfflineDescription) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit) :
    Sides (keyFileDescription d.source d.numbers d.later) (thePartsAt files).book (Cz files).I
      ((Cz files).Pad × (Cz files).Rnd) TableKey Unit (thePartsAt files).SharedState
      (thePartsAt files).OwnState :=
  offlineRowsAt (files := files) d offlineProverCoinCounts S c

/-- **Their lists are the lists of the named value's prover, and their prover is it.** -/
theorem object_rows {d : OfflineDescription} (h : offlineDescription files = .ok d)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit) :
    ((thePartsAt files).prover d).first =
        (rowsAtTheTerm (files := files) d S c).first.map (fun L => ⟨L.place, L.row.map (·.1)⟩) ∧
      ((thePartsAt files).prover d).shared =
        (rowsAtTheTerm (files := files) d S c).shared.map (fun L => ⟨L.place, L.row.map (·.1)⟩) ∧
      ((thePartsAt files).prover d).second =
        (rowsAtTheTerm (files := files) d S c).second.map (fun L => ⟨L.place, L.row.map (·.1)⟩) ∧
      (rowsAtTheTerm (files := files) d S c).prover ((thePartsAt files).prover d) =
        (thePartsAt files).prover d := by
  rw [object_prover h]
  exact ⟨offlineSides_first _ _ _ _ _ _ _ _, offlineSides_shared _ _ _ _ _ _ _ _,
    offlineSides_second _ _ _ _ _ _ _ _, offlineRows_prover _ _ _ S c⟩

/-- **The protocol's offline honest prover at the named value is the frame's run of that prover at that
book**, where the public files make the description d. -/
theorem object_offlineProver {d : OfflineDescription} (h : offlineDescription files = .ok d) :
    offlineProver (thePartsAt files) =
      offlineProverWithEncodedTable files (keyFileDescription d.source d.numbers d.later) (thePartsAt files).book
        ((thePartsAt files).prover d) runValueBytes runValueBytes (offlineStart d) := by
  unfold offlineProver
  rw [h]

/-- The protocol's honest provers at the three public files are `honestProvers` at the named value. -/
theorem object_provers : theHonestProvers files = honestProvers files (thePartsAt files) := rfl

/-- **The object in one sentence.** Where the public files' test says yes, in scope. The prover's equation
stands at the named value itself. -/
theorem object_where_live (live : protocolDataWellFormed (asDescriptionFiles files) = true) (scope : InScope files = true) :
    ∃ d K₀, offlineDescription files = .ok d ∧
      KeySourced files d.source d.numbers d.later ∧ fullPub = some K₀ ∧
      thePartsAt files = partsOfDescription d ∧ (thePartsAt files).book = keyBook K₀ ∧
      (thePartsAt files).prover d = keyProver (senderValue d) ∧ (senderValue (files := files) d).AtAll := by
  obtain ⟨d, hd, hs⟩ := offlineDescription_named files live
  obtain ⟨K₀, hK⟩ := AtPublicFiles.KeyBook.full_made
  exact ⟨d, K₀, hd, hs, hK, thePartsAt_ok hd, object_book hK, object_prover hd,
    senderValue_atAll hs scope⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.object_book
#print axioms AtPublicFiles.OfflineRows.object_types
#print axioms AtPublicFiles.OfflineRows.object_prover
#print axioms AtPublicFiles.OfflineRows.object_values
#print axioms AtPublicFiles.OfflineRows.object_rows
#print axioms AtPublicFiles.OfflineRows.object_offlineProver
#print axioms AtPublicFiles.OfflineRows.object_provers
#print axioms AtPublicFiles.OfflineRows.object_where_live
