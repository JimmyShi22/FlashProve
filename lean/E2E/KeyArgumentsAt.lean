-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyArgumentsAt.lean: one named value of the offline prover's arguments (Parts,
E2E/TheHonestProver.lean) at every three public files: thePartsAt. With it the honest provers of that
file take no argument but the public files.

  storedColumn, withStoredColumnsAndPlan   keyOf without its public part
  laidFromChains_is_keyOf        at every public part that is keyOf at pubKey: the stored table
                                 reads of the public part the chains alone
  offlineProverCoinCounts                    the offline file's book of coins at the written sizes
  matrixReader                   the index's reader: matrixInput's
  offlineSenders, partsOfDescription, fallbackSenders, thePartsAt   the values
  thePartsAt_of, prover_is_keyOf   at a description

Every value reads the real index, where a value has anything to read of it.

Limits. Where the public files make no description, thePartsAt's senders are fallbackSenders, which no prover
reads: offlineProver sends the fixed messages there, and no proposition rests on it. Stand-ins: the
nine named defaults, fallbackSenders, a tenth, and what the terms called here carry (proximityTestParametersAt's noP12, recRanges,
bsOf, doorKW's idleT12): this file states nothing on whether one of them is taken in scope. offlineProverCoinCounts is the
written sizes' book: at public files of other sizes ready refuses. This file defines values alone: it states neither that a
verifier accepts this prover nor that the description is at the written sizes (five_in_scope says so in scope).
This file states no property.
-/
import E2E.TheHonestProver
import E2E.KeyFifteen
import E2E.KeyPartsIdle
import E2E.KeyBookAtWritten

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.Term (matrixInput tableCoins)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open OnBytes.Model.Verify (Chains)
open Bind.ForProver (encAt shapeOfIndex entryAtF rowsFit encW)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyStandMember (keyOf)
open AtPublicFiles.KeyPartsIdle (fixedKeyParts)
open AtPublicFiles.KeyBook (keyBook fullPub)
open AtPublicFiles.KeyValues (WitK withSendingsAndLookups matrixEntryOf multiplicitiesGroups faceAt keyBatt)
open VerifierAndGoals (PublicFiles)

section
variable {Index Coins SharedState OwnState LookupInput : Type}

/-- **The stored table's column**, at the key's shape: encW's text, off the chains. -/
def storedColumn (chains : Chains) (weights : Weights) (coins : Nat → TableRand) (item position : Nat) :
    Option (List Cb.Gl.F) :=
  if item = 0 ∧ rowsFit (shapeOfIndex chains.made.sized.key.once.shape.fold.index)
      chains.made.sized.key.once.shape.kLo chains.made.sized.key.once.shape.matrixRows = true then
    encAt (shapeOfIndex chains.made.sized.key.once.shape.fold.index)
      (entryAtF chains.made.sized.key.once.shape.kLo chains.made.sized.key.once.shape.matrixRows
        (shapeOfIndex chains.made.sized.key.once.shape.fold.index).v weights.entry) (coins 0) position
  else none

/-- **keyOf, without its public part.** -/
def withStoredColumnsAndPlan (source : Source) (later : LaterPlaces)
    (senders : KeyParts Index Coins SharedState OwnState LookupInput)
    (weights : Index → Weights) (coins : Coins → Nat → TableRand) :
    KeyParts Index Coins SharedState OwnState LookupInput :=
  { senders with
    stored := fun index coin item position =>
      storedColumn source.chains (weights index) (coins coin) item position
    weights := weights
    rand := fun coin => coins coin 0
    lin := planData (parKey source later)
    send := ⟨parKey source later, 0⟩ }

/-- **It is keyOf at pubKey, at every public part**: encW reads of its public part the chains alone
(linOf_pubKey). So no public part is needed, and a law at keyOf (pubKey _ source.chains) speaks of
it. -/
theorem laidFromChains_is_keyOf (publicPart : ProofFile.Pub) (source : Source) (later : LaterPlaces)
    (senders : KeyParts Index Coins SharedState OwnState LookupInput)
    (weights : Index → Weights) (coins : Coins → Nat → TableRand) :
    withStoredColumnsAndPlan source later senders weights coins =
      keyOf (pubKey publicPart source.chains) source later senders weights coins := rfl

end

/-- **The offline file's book of coins**, at the written sizes. The empty book stands in where
fullPub is none; full_made (E2E/KeyBookPassesNamed.lean) says that it is not. -/
def offlineProverCoinCounts : ProverCoinCounts :=
  match fullPub with
  | some publicData => keyBook publicData
  | none => ⟨[], [], [], [], []⟩

/-- **The index's reader**: matrixInput's, which reads no public part. -/
def matrixReader : FullSizeMatrix → Weights := fun matrix => ⟨AtPublicFiles.Key.cellsReader matrix⟩

theorem matrixInput_reader (publicPart : ProofFile.Pub) : matrixInput.weights publicPart = matrixReader :=
  rfl

/-- A record that reads nothing, for fixedKeyParts' wit, which withSendingsAndLookups overwrites. -/
def idleRecord : WitK :=
  (fun _ => ⟨fun _ _ _ => OnBytes.zeroE, fun _ _ => OnBytes.zeroE⟩,
    fun _ => ⟨fun _ _ _ => OnBytes.zeroE, fun _ _ => OnBytes.zeroE⟩)

variable {files : PublicFiles}

/-- **The offline file's senders at a description.** -/
def offlineSenders (description : OfflineDescription) :
    KeyParts FullSizeMatrix (protocolAtFiles files).EncodingRandomness Unit Unit WitK :=
  withStoredColumnsAndPlan description.source description.later
    (withSendingsAndLookups
      (fixedKeyParts (faceAt description.source 0) (keyBatt description.source) matrixInput.dummy () ()
        idleRecord)
      description.source description.numbers matrixReader matrixInput.inRange matrixInput.dummy)
    matrixReader (tableCoins files)

/-- **The offline prover's arguments at a description.** -/
def partsOfDescription (description : OfflineDescription) : Parts files where
  book := offlineProverCoinCounts
  SharedState := Unit
  OwnState := Unit
  LookupInput := WitK
  senders := offlineSenders description
  rangeEntry := matrixEntryOf matrixReader
  rangeGroups := multiplicitiesGroups description.source

/-- Senders that no prover reads: where the public files make no description offlineProver sends
the fixed messages. -/
def fallbackSenders : KeyParts FullSizeMatrix (protocolAtFiles files).EncodingRandomness Unit Unit WitK :=
  fixedKeyParts (VerifiableInference.Desc.K3.faceOfLkp default) AtPublicFiles.KeyPartsIdle.idleWhere
    matrixInput.dummy () () idleRecord

variable (files)

/-- **The value of the offline prover's arguments that this file names.** The match stands inside
senders and rangeGroups, so that its types and its book are what they are at every public files. -/
def thePartsAt : Parts files where
  book := offlineProverCoinCounts
  SharedState := Unit
  OwnState := Unit
  LookupInput := WitK
  senders :=
    match offlineDescription files with
    | .ok description => offlineSenders description
    | .error _ => fallbackSenders
  rangeEntry := matrixEntryOf matrixReader
  rangeGroups :=
    match offlineDescription files with
    | .ok description => multiplicitiesGroups description.source
    | .error _ => []

/-- honestProvers at that value: a function of the three public files alone. -/
abbrev theHonestProvers := honestProvers files (thePartsAt files)

variable {files}

/-- **At a description the value is partsOfDescription's.** -/
theorem thePartsAt_of {description : OfflineDescription}
    (h : offlineDescription files = .ok description) :
    thePartsAt files = partsOfDescription description := by
  unfold thePartsAt partsOfDescription
  simp only [h]

/-- **What the offline prover is handed is keyOf at every public part**: statements at keyOf, such
as `stand_three` (E2E/KeyStandMember.lean), speak of this term. -/
theorem prover_is_keyOf (publicPart : ProofFile.Pub) (description : OfflineDescription) :
    AtPublicFiles.KeyLay.withTests (offlineSenders (files := files) description) description.source
        description.numbers description.later (offlineTestParametersOnU description.later)
        (offlineTestOnOmega description.later) (matrixEntryOf matrixReader)
        (multiplicitiesGroups description.source) 0 =
      keyOf (pubKey publicPart description.source.chains) description.source description.later
        (AtPublicFiles.KeyLay.withTests (offlineSenders (files := files) description) description.source
          description.numbers description.later (offlineTestParametersOnU description.later)
          (offlineTestOnOmega description.later) (matrixEntryOf matrixReader)
          (multiplicitiesGroups description.source) 0) matrixReader (tableCoins files) := rfl

end AtPublicFiles.AtFiles.HonestTerm
