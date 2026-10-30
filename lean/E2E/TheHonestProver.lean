-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TheHonestProver.lean: the honest prover of the protocol, as one named term.

The protocol has three parts, named by what a user holds. offline: the proof in the key file, on the
committed table. link: from a further encoding to the first. online: the proof for a request (the
proof file).

This file holds the value and nothing else: honestProvers, one prover for each part, as the prover
of an interactive oracle proof, in the type ThreeProvers that the compiler's theorems take. It takes the
structure Parts as an argument; E2E/KeyArgumentsAt.lean gives its value, thePartsAt, and the
statements on completeness and zero knowledge are about honestProvers at that value. What must hold
of honestProvers, and the places known to us where these senders fall back on a fixed value, are in
E2E/TheHonestProverStatements.lean; those of the value are named in E2E/KeyArgumentsAt.lean.
-/
import Johnson.Desc.ProofFile.Honest.AtGoalInput
import Johnson.Desc.ProofFile.Honest.AtPureFullIn
import Johnson.Desc.ProofFile.Honest.ThruK13
import Johnson.Desc.ProofFile.Honest.OpenHonest
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Goal.Conditions.HomeAtWider
import E2E.BridgeJoinAtFiles
import E2E.BridgePremWKey
import E2E.BridgePremWLink
import E2E.KeyProtocolOverDescription
import E2E.KeyReaders
import E2E.KeyProver
import E2E.KeyPartsHalves
import E2E.KeyProverSideOfOwnTest
import E2E.KeyRangesJob

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

/-! ## 1 The honest side of any object with records -/

namespace ProofFile.Honest.Term
open Iop Hiop OnBytes.Prover

section General
variable {I X : Type}

/-- **What the committer holds of an index, at this level**: the encoded table and the out-of-domain
record, at the table's randomness and an out-of-domain seed. -/
def committed (L : HolographicProtocol I X) (i : I) (r : L.EncodingRandomness) (e : L.OutOfDomainSeed) :=
  (L.encodeIndex i r, L.recOf i r e)

/-- **The coins of the honest side at one request**: the committer's randomness for the first table
and for the copy that serves the request, and each prover's own coins. The out-of-domain seeds are
not coins of the honest side, and the copy's number is no draw. The compiled committer draws such
randomness for each of its copies. -/
structure HonestCoins {L : HolographicProtocol I X} (R : ThreeProvers L) where
  firstTable : L.EncodingRandomness
  copyTable : L.EncodingRandomness
  offlineProverCoin : R.T.Coin
  linkProverCoin : R.Lk.Coin
  onlineProverCoin : R.B.Coin

end General

/-- **One honest prover, at every copy's number.** -/
def familyOf {Y Wt : Type} {E : ExtSpec} {protocol : InteractiveOracleProof Y E} (H : Honest protocol Wt) :
    AtPublicFiles.Bridge.Family protocol Wt where
  Coin := H.Coin
  finCoin := H.finCoin
  neCoin := H.neCoin
  ext := fun _ => H.ext
  strat := fun _ => H.strat
  Bad := H.Bad
  Hid := fun _ => H.Hid

end ProofFile.Honest.Term

/-! ## 2 The offline prover's four proximity tests -/

namespace AtPublicFiles.KeyLay
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open VerifiableInference.Desc.K12 (P12)
open AtPublicFiles.KeyFile (KeyParts randK14)
open AtPublicFiles.KeyThread (rangesTestJob)
open OnBytes.Slice (GF)
open ProofFile.Honest (Local)
open ProofFile.Honest.K12 (proverSideOfProximityTest)
open ProofFile.Honest.K12.Light (askOf)

variable {W₀ Rc X₀ X Wk : Type}

/-- **The four proximity tests laid into the offline prover's senders.** -/
def withTests (senders : KeyParts W₀ Rc X₀ X Wk) (source : Source) (numbers : H2U.PlaceNums)
    (later : LaterPlaces) (placeU placeOmega : P12) (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF)
    (groups : List (List Nat)) (first : Nat) : KeyParts W₀ Rc X₀ X Wk :=
  { withTestsOnUAndOmega senders placeU placeOmega with
    rng := proverSideOfProximityTest (rangesTestJob source numbers later entry groups first)
    own := proverSideOfGuardedSending source numbers later senders.idx senders.w senders.send id
      (askOf senders.send (fun w => senders.weights w.w₀) fun w => randK14 (senders.rand w.rc)) }

end AtPublicFiles.KeyLay

/-! ## 3 The online prover -/

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open OnBytes (TableKey)
open OnBytes.Slice (frS frZ)
open VerifiableInference.Desc (Chain)
open P5J (TS)

/-- The value of `WiderIn` at the matrices: the matrix's own reader; the trace and the range through
the index that the matrix holds. -/
def matrixInput : WiderIn FullSizeMatrix :=
  { weights := fun _ M => ⟨AtPublicFiles.Key.cellsReader M⟩
    trace := fun publicPart M ξ =>
      (VerifiableInference.OnPublicFiles.Flat.indexOf M).bind fun i => fullIn.trace publicPart i ξ
    inRange := fun M => (VerifiableInference.OnPublicFiles.Flat.indexOf M).isSome
    dummy := VerifiableInference.OnPublicFiles.Flat.matrixOf fullIn.dummy }

/-- **The range of the index.** -/
abbrev matrixInRange (M : FullSizeMatrix) : Prop := matrixInput.inRange M = true

/-- The coins' map: the object's randomness is one table's, read at every item of the statement. -/
def tableCoins (files : VerifierAndGoals.PublicFiles) : (protocolAtFiles files).EncodingRandomness → IndexCommitterCoins :=
  ProofFile.Honest.randOf (S := frS) (cut := 402653181)

variable (files : VerifierAndGoals.PublicFiles)

/-- **The filling of the online prover**: the kinds' sides, the closings, the proximity tests' and
the message W's, at the matrices and at the object's randomness. -/
abbrev onlineFilling : OnlineProverParts FullSizeMatrix (protocolAtFiles files).EncodingRandomness Cells Unit Unit :=
  OnlineProverParts.through id (tableCoins files) matrixInput.dummy
    (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest)

/-- **What the maker returns at the filling**: the public part, the ground, the description, the
book of coins, the prover's sides, its readers and its rows' data. -/
abbrev OnlineReturn := OnlineProverWithDescription FullSizeMatrix (protocolAtFiles files).EncodingRandomness Cells Unit Unit

/-- **The maker at the filling and the three public files**: the function from which the online
description is made. -/
abbrev onlineMaker : Except String (OnlineReturn files) :=
  onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineFilling files)

end ProofFile.Honest.Term

/-! ## 4 The three provers -/

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open OnBytes (TableKey)
open OnBytes.Prover (ThreeProvers)
open OnBytes.Slice (frS GF)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open ProofFile.Honest (ProverCoinCounts Local)
open ProofFile.Honest.Term (OnlineReturn onlineMaker familyOf)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData committerCoinCountLessOne)
open P5J

local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

/-- **A run value**: thirty-two bytes. This is a reading of «run value» in lean/GLOSSARY.md, a hash
at a chain's start; the library's definitions leave its type open. The plain rounds show it. -/
abbrev RunValue : Type := Fin 32 → Fin 256

/-- Given by hand: among all that this file imports, the search for these runs out of its budget. -/
local instance (priority := high) : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) : Inhabited RunValue := ⟨fun _ => 0⟩

/-- A run value as bytes. -/
def runValueBytes (v : RunValue) : ByteArray :=
  ⟨Array.ofFn fun i => (v i).val.toUInt8⟩

variable (files : PublicFiles)

/-- **The online provers at a return of the maker, one for each copy's number.** places, firstChain:
what the online description is made of. -/
def onlineProverAt {files : PublicFiles} (returned : OnlineReturn files) (places : H2U.Places4)
    (firstChain : Chain TS ProofFile.Cl) :
    Family (protocolAtFiles files).onlineBatch.loc (FullSizeMatrix × (protocolAtFiles files).EncodingRandomness × (protocolAtFiles files).OutOfDomainSeed) :=
  onlineProversOfCommitter files returned.Z places firstChain silInst runValueBytes runValueBytes returned.B
    (dataAtFiles flashProveData files).P returned.H

/-- **The online honest provers**: the maker's return at the places and the first chain that the
public part makes, which are the ones from which the filling lays its sides. Where one of these
three functions refuses, the provers that send the fixed messages. -/
def onlineProver : Family (protocolAtFiles files).onlineBatch.loc (FullSizeMatrix × (protocolAtFiles files).EncodingRandomness × (protocolAtFiles files).OutOfDomainSeed) :=
  match onlineMaker files with
  | .ok returned =>
    match H2U.placesOfMade returned.Z.made, ProofFile.onlineFirstChainAt returned.Z with
    | .ok places, .ok firstChain => onlineProverAt returned places firstChain
    | _, _ => familyOf (filesAt files).fixedMessageProvers.hB.one
  | .error _ => familyOf (filesAt files).fixedMessageProvers.hB.one

/-- **The link's honest prover**, at the number of the committer's coins. -/
abbrev linkProver := linkProverAtFiles committerCoinCountLessOne files

/-- **What the offline description is made of**: the arguments of `keyFileDescription`. -/
structure OfflineDescription where
  source : Source
  numbers : H2U.PlaceNums
  later : LaterPlaces

/-- **What the three public files make of it**: the reader, the maker and the three functions on
which `descriptionFromPlan` matches (Johnson/Desc/Key/Desc.lean), in that order. -/
def offlineDescription : Except String OfflineDescription := do
  let read ←
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction files.pol files.KL (some files.lay)
  let made ←
    VerifiableInference.Desc.Key.madeAt read files.lay VerifiableInference.Desc.Key.fixedDigest
  let source ← VerifiableInference.Desc.Key.sourceOf made
  let numbers ← VerifiableInference.Desc.Key.rangesNumbers made
  let later ← VerifiableInference.Desc.Key.laterPlaces made
  pure ⟨source, numbers, later⟩

/-- **The offline prover's shared chain's first state, from the table's key**: the description's own
(its field `start₂`, read at the key that the prover is given). -/
def offlineStart (description : OfflineDescription) :
    TableKey → (keyFileDescription description.source description.numbers description.later).S₂ :=
  fun k => _root_.Desc.K14.first description.source.chains.made.sized.key.codes k

/-- **The offline prover's test on the group U, as the description's chain lays it.** -/
def offlineTestParametersOnU (later : LaterPlaces) : P12 := H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ later.U

/-- **The offline prover's test on the group Omega, as the description's chain lays it**; the
description has no such test where `later.O` is none (`OfflineHasATestOnOmega`). -/
def offlineTestOnOmega (later : LaterPlaces) : P12 :=
  H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (later.O.getD later.U)

/-- **Everything that the honest provers take as an argument**: the offline prover's. Four fields of
`senders` (`rng`, `onU`, `onOmega`, `own`) are overwritten by the proximity tests. -/
structure Parts where
  /-- its book of coins -/
  book : ProverCoinCounts
  /-- what its sides pass on, and what its lookups are written at -/
  SharedState : Type
  OwnState : Type
  LookupInput : Type
  /-- its senders, but for the four proximity tests -/
  senders : AtPublicFiles.KeyFile.KeyParts (Cz files).I ((Cz files).Pad × (Cz files).Rnd) SharedState OwnState
    LookupInput
  /-- what the test on the ranges reads -/
  rangeEntry : Local (Cz files).I ((Cz files).Pad × (Cz files).Rnd) KeyInst Unit → Nat → Nat → GF
  rangeGroups : List (List Nat)

variable {files}

/-- The offline prover in the frame, at its description, with the four proximity tests. -/
abbrev Parts.prover (parts : Parts files) (description : OfflineDescription) :=
  AtPublicFiles.KeyFile.keyProver (AtPublicFiles.KeyLay.withTests parts.senders description.source description.numbers
              description.later (offlineTestParametersOnU description.later) (offlineTestOnOmega description.later)
              parts.rangeEntry parts.rangeGroups 0)

/-- **The offline honest prover**; where the public files make no description, the prover that sends
the fixed messages. -/
def offlineProver (parts : Parts files) :
    Honest (protocolAtFiles files).offline (FullSizeMatrix × (protocolAtFiles files).EncodingRandomness × (protocolAtFiles files).OutOfDomainSeed) :=
  match offlineDescription files with
  | .ok description =>
    offlineProverWithEncodedTable files (keyFileDescription description.source description.numbers description.later) parts.book
      (parts.prover description) runValueBytes runValueBytes (offlineStart description)
  | .error _ => (filesAt files).fixedMessageProvers.hT

/-- **THE HONEST PROVERS OF THE PROTOCOL.** -/
def honestProvers (files : PublicFiles) (parts : Parts files) : ThreeProvers (protocolAtFiles files) :=
  proversOf (offlineProver parts) (linkProver files) (onlineProver files)

/-- **The committer of the protocol, at this level.** -/
abbrev indexCommitter (files : PublicFiles) := ProofFile.Honest.Term.committed (protocolAtFiles files)

end AtPublicFiles.AtFiles.HonestTerm
