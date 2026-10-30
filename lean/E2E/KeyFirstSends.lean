-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyFirstSends.lean: the values of the key file's prover's first chain that are sendings: the
index-mask message, the multiplicities and W, at the public record of a key, and what W and the
batching read of the challenges: where each lookup stands, the point of each part's claim, the pile.

Each sending is the job of E2E/KeySendJobs.lean at the very arguments at which the key file's
first chain lays the block for it (firstChain, Johnson/Desc/Key/Chain1.lean). The multiplicities and W
read the index through f, which is keyOf's own letter: so they read the real matrix.

  matrixEntryOf         the matrix, of a half's input
  faceAt, placeAt, baseAt, battAt, keyPoints   a lookup's face, place and rounds in front; the
                batching's three numbers; the point of a part's claim, off the challenges heard
  indexMaskSending, multiplicitiesSending, batchedRowsSending, constraintRowsAtClaimPoints, keyBatt   the values

Limits. This says nothing of what a verifier does with them. batchedRowsSending sends the index masks' job at a
shape with no message W: a stand-in at sizes that are not served; at the written sizes W is there
(rides_full, E2E/KeyBookHeldK1Jobs.lean). rideMsg and rideW are numbers of the written sizes alone:
elsewhere sendFits says no and the part errs. firstW counts the messages in front by reading.
keyPoints is the verifier's point by HeardLaw.lean's theorem at one part alone; at several parts by a
toy program, not by Lean. Nothing on any property.
-/
import E2E.KeyProver
import E2E.KeySendJobs
import E2E.KeyBookHeldK1Jobs
import Johnson.Desc.Key.Chain1
import Johnson.Desc.Key.FileOk
import Johnson.Desc.ProofFile.Honest.K3.Heard

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtPublicFiles.KeyValues
open OnBytes OnBytes.Params
open OnBytes.Slice (GF)
open ProofFile.Honest (Weights roundsInFront)
open ProofFile.Honest.K1 (SendJob)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K3 (faceOfLkp)
open VerifiableInference.Desc.Key (Source firstChain pieces groupsTold rootsAt rootsBefore
  lastSendRound batchRound batchWhere lookupsOf)
open AtPublicFiles.Key (idxJob msgJob wJob pileOf BattAt)
open AtPublicFiles.KeyBook (rideMsg rideW)
open AtPublicFiles.KeyFile (In1 KeyInst)

variable {W₀ Rc X : Type}

/-- The one-time chain's public values. -/
abbrev oneOf (Xs : Source) : OneTime := Xs.Y.k.oneTime

/-- **The matrix, of a half's input**: what f reads of the index. -/
def matrixEntryOf (f : W₀ → Weights) : In1 W₀ Rc → Nat → Nat → GF := fun t => (f t.w₀).entry

/-- The first chain's blocks, as the file lays them. -/
def blocksOf (Xs : Source) (N : H2U.PlaceNums) :=
  (firstChain (oneOf Xs) Xs.Y.D.1 Xs.Y.told.1 Xs.set N).blocksInOrder

/-- Lookup i's public record. -/
def lookAt (Xs : Source) (i : Nat) : Lkp.Public := (lookupsOf (oneOf Xs)).getD i default

/-- Lookup i's face. -/
def faceAt (Xs : Source) (i : Nat) : ProofFile.Honest.K3.LFace := faceOfLkp (lookAt Xs i)

/-- Lookup i's place: K3.lookupKind's at chain 1, link i, piece 2. -/
def placeAt (i : Nat) : Place := ⟨1, some i, 2, .K3⟩

/-- How many rounds of the chain stand in front of lookup i: off the file's own list. -/
def baseAt (Xs : Source) (N : H2U.PlaceNums) (i : Nat) : Nat :=
  (roundsInFront (blocksOf Xs N) (placeAt i)).getD 0

/-- **The point of the claim on the keys of part p of lookup i**, off the challenges heard: the key
tree's last point, coordinate t with bit t of a key's number (keyClaims, K3Key.lean, turns the
hearing's point round in the same way). -/
def keyPoints (Xs : Source) (N : H2U.PlaceNums) (ds : List Fmt.Drawn) (i p : Nat) : List E :=
  ((ProofFile.Honest.K3.ptsOf (faceAt Xs i) (baseAt Xs N i) ds).keyPt p
    ((faceAt Xs i).parts.getD p 0)).toList.reverse

/-- The batching's three numbers: "BAT-sigma" at the first of its rounds, "PSC epsilon" behind it,
then the rounds of the column variables. -/
def battAt (Xs : Source) (N : H2U.PlaceNums) : BattAt :=
  let b := (roundsInFront (blocksOf Xs N) (⟨1, none, pieces.batt, .K13⟩ : Place)).getD 0
  ⟨b, b + 1, b + 2⟩

/-- **The index-mask message's sending**: no main row: all it holds is coins. -/
def indexMaskSending (Xs : Source) : SendJob (In1 W₀ Rc) X :=
  idxJob (oneOf Xs) pieces (groupsTold Xs.Y.told.1 0 (rootsAt Xs.Y.D.1 0)) 0

/-- The groups of the multiplicities' sending: IOP's letter groups in rangesTestJob is this list. -/
def multiplicitiesGroups (Xs : Source) : List (List Nat) :=
  groupsTold Xs.Y.told.1 (rootsBefore Xs.Y.D.1 2) (rootsAt Xs.Y.D.1 2)

/-- **The multiplicities' sending**: the bits of how often each row of each table is met in the
matrix (msgData, planesData, bitOf). It reads the index. -/
def multiplicitiesSending (f : W₀ → Weights) (Xs : Source) : SendJob (In1 W₀ Rc) X :=
  msgJob (matrixEntryOf f) (oneOf Xs) pieces (multiplicitiesGroups Xs) 1 rideMsg

/-- The number of the first message of W's sending: the index-mask message, the multiplicities'
sending, and what the ranges' test sends. -/
def firstW (Xs : Source) : Nat :=
  1 + (Wf.messageOf (oneOf Xs).ranges).size +
    ((AtPublicFiles.TreeReads.sentOfTest (oneOf Xs).given.plan.samples true (oneOf Xs).ranges.stages).map
      List.length).sum

/-- **W's sending**: the batching's weights on the matrix's rows times the matrix (wVec, wWeights).
It reads the index and the challenges heard. Where the shape has no message W: the index masks'
job, IN ITS PLACE, at sizes that are not served. -/
def batchedRowsSending (f : W₀ → Weights) (Xs : Source) (N : H2U.PlaceNums) : SendJob (In1 W₀ Rc) X :=
  (wJob (matrixEntryOf f) (oneOf Xs) pieces
    (groupsTold Xs.Y.told.1 (rootsBefore Xs.Y.D.1 (lastSendRound Xs.Y.D.1))
      (rootsAt Xs.Y.D.1 (lastSendRound Xs.Y.D.1)))
    (firstW Xs) rideW (keyPoints Xs N) (battAt Xs N)).getD (indexMaskSending Xs)

/-- **The pile**: the rows on the matrix at the claims' points. Their masks and targets are not the
verifier's, and nothing reads them (K13/Part.lean's head; handedWeights_congr, E2E/KeyPile.lean). -/
def constraintRowsAtClaimPoints (Xs : Source) (N : H2U.PlaceNums) : ProofFile.Honest.K13.PileOf KeyInst :=
  fun _ ds => pileOf (Wf.matrixOf (oneOf Xs).lin) (oneOf Xs).ranges.lookups (keyPoints Xs N ds)

/-- **The batching's numbers**: the block's own. -/
def keyBatt (Xs : Source) : VerifiableInference.Desc.K13.Where :=
  batchWhere (oneOf Xs) pieces (rootsBefore Xs.Y.D.1 (batchRound Xs.Y.D.1))

end AtPublicFiles.KeyValues
