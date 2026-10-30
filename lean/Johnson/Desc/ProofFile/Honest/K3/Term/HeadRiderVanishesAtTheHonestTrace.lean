-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT ANY FILLING.
Johnson/Desc/ProofFile/Honest/K3/Term/HeadRiderVanishesAtTheHonestTrace.lean: the honest side of the
kind "lookup" (K3), at the lookup on the calls of the output head.

Behind the lookup's step the exchange asks that each array of the caller's rider is 0 at every
vertex of its cube (the field cubes of AtHead, K3/Law/Thread/ExchangeHeadAll.lean). At the head
these are the two lines on a position's cost (the clip; the table values' sum), at every position.
Here they are shown of the honest trace, at every token.

Premises: the three on the public files (in scope; the files are read; publicOf returns), "the
request is served", and RequestCoversTheSamePositions: the checked range of the head's class Request
is the served request's.

What is defined.
  RequestCoversTheSamePositions: the premise on the head's class Request.
What is shown.
  theTwoCostLinesReadTheCheckedRangeAndTheCellsAlone: CornerGuests reads, of the request, the
    checked range alone; of the cells, the table of integers alone; the token and the weights not at
    all.
  headRiderVanishesWhereTheTwoCostLinesHold: from CornerGuests at the cells off a tuple of messages
    to "0 on the cubes". The way back is the library's head_guests.
  theTwoCostLinesHoldAtTheHonestTrace: CornerGuests at the head's cells off the honest trace, at
    every token and every Request that covers the served request's positions.
  headRiderVanishesAtTheHonestTrace: the three joined, at the library's own map of the head's cells
    (adrOf), at every tuple of messages whose cells are those of the trace's list 24 (MatsAre).

Not claimed: that any tuple of messages holds the trace's cells; that a verifier's block accepts;
anything on soundness, completeness or zero knowledge.
-/
import Johnson.Goal.HonestTrace.FullPlanesInScope
import Johnson.Desc.First.Look.K3CallerHead
import Johnson.Desc.Kinds.Law.RiderNoWeights
import Johnson.Desc.ProofFile.Honest.K6.Law.TraceCellsAtTheTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes (OracleShape)
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (theTrace ServesAt meetsAll_theTrace)
open OnBytes.Model.Verify (publicOf borderOf)
open Inst.Model (Instance ppref ScalesAndPolicy)
open VerifiableInference.OnPublicFiles (tailId tailPlaces_len forall_get_map)
open VerifiableInference.Desc.First.Look (Place Sent laySg MatsAre)
open VerifiableInference.Desc.Kinds.Norm (lt T)
open VerifiableInference.Desc.Kinds.Head (Sizes Policy Request Token)
open VerifiableInference.Desc.Kinds.Head.Law
  (Cells CornerGuests PlanFacts planFacts clipAt tableAt corner
  rd rd_clip rd_table rd_zero_iff okE_clipAt okE_tableAt HeadAdr adrOf sizesOf policyOf headCaller
  headCells headArrs headRider head_cells_cast reqX)
open VerifiableInference.Desc.Kinds.Head.Law.Came (traceCells headCells_says_theTrace)

/-- **The two lines on a position's cost read the checked range and the table of integers alone**:
not the request's tokens, not the reply's token, not the weights. -/
theorem theTwoCostLinesReadTheCheckedRangeAndTheCellsAlone [Sizes] [Policy] (plan : PlanFacts)
    (headRequest headRequest' : Request) (token token' : ℕ) (cells cells' : Cells)
    (sameFirst : headRequest.r = headRequest'.r) (sameEnd : headRequest.e = headRequest'.e)
    (sameCells : cells.cell = cells'.cell)
    (lines : letI := headRequest; letI : Token := ⟨token⟩; CornerGuests cells) :
    letI := headRequest'; letI : Token := ⟨token'⟩; CornerGuests cells' := by
  obtain ⟨tokens, firstPosition, endPosition⟩ := headRequest
  obtain ⟨tokens', firstPosition', endPosition'⟩ := headRequest'
  obtain rfl : firstPosition = firstPosition' := sameFirst
  obtain rfl : endPosition = endPosition' := sameEnd
  obtain ⟨cell, weights⟩ := cells
  obtain ⟨cell', weights'⟩ := cells'
  obtain rfl : cell = cell' := sameCells
  intro position positionIsInRange
  obtain ⟨clipIsZero, tableIsZero⟩ := lines position positionIsInRange
  have clipRead :=
    letI : Request := ⟨tokens, firstPosition, endPosition⟩
    letI : Token := ⟨token⟩
    (rd_clip (c := ⟨cell, weights⟩) positionIsInRange).symm.trans
      ((rd_zero_iff (okE_clipAt _ _)).2 clipIsZero)
  have tableRead :=
    letI : Request := ⟨tokens, firstPosition, endPosition⟩
    letI : Token := ⟨token⟩
    (rd_table (c := ⟨cell, weights⟩) plan positionIsInRange).symm.trans
      ((rd_zero_iff (okE_tableAt _ _)).2 tableIsZero)
  exact
    letI : Request := ⟨tokens', firstPosition, endPosition⟩
    letI : Token := ⟨token'⟩
    ⟨(rd_zero_iff (okE_clipAt _ _)).1
        ((rd_clip (c := ⟨cell, weights'⟩) positionIsInRange).trans clipRead),
      (rd_zero_iff (okE_tableAt _ _)).1
        ((rd_table (c := ⟨cell, weights'⟩) plan positionIsInRange).trans tableRead)⟩

/-- **From the two lines at the cells off a tuple of messages to "the rider's arrays are 0 on their
cubes"**, at the token at which the lines are said. -/
theorem headRiderVanishesWhereTheTwoCostLinesHold [Sizes] [Policy] [Request] (addresses : HeadAdr)
    (place : Place) (tail : HTailF2) (sent : Sent) (radius : OracleShape → ℕ)
    (weightsOracle : Cb.OMsg Cb.Gl.E) (weightsReading : weightsOracle.Msg → ℕ → ℕ → Cb.Gl.E)
    (weightRows weightColumns : ℕ) (extension : Iop.ExtSpec) (witnessPart : Type) (token : ℕ)
    (messages : (laySg place sent radius weightsOracle).Msg)
    (lines : letI : Token := ⟨token⟩; CornerGuests
      (headCells addresses place tail sent radius weightsOracle weightsReading weightRows
        weightColumns messages).toCells) :
    Cb.Rider.OnCubes
      (headRider addresses place tail sent radius weightsOracle weightsReading weightRows
        weightColumns extension witnessPart).g
      (headRider addresses place tail sent radius weightsOracle weightsReading weightRows
        weightColumns extension witnessPart).f token messages := by
  letI : Token := ⟨token⟩
  refine (forall_get_map
    (fun member => tailId
        (headCaller addresses place tail sent radius weightsOracle weightsReading weightRows
          weightColumns extension witnessPart) lt member.1 member.2)
    (headArrs addresses place tail sent radius weightsOracle weightsReading weightRows
        weightColumns)
    fun guest => ∀ vertex < 2 ^ guest.places.length, guest.cells token messages vertex = 0).2 ?_
  intro member memberIsListed vertex vertexIsInTheCube
  have inRange : vertex < T := by
    show vertex < 2 ^ lt
    rw [← tailPlaces_len place.fs lt]
    exact vertexIsInTheCube
  rcases List.mem_cons.1 memberIsListed with rfl | memberIsListed
  · exact (rd_zero_iff (okE_clipAt _ _)).2 (lines vertex inRange).1
  · obtain rfl := List.mem_singleton.1 memberIsListed
    exact (rd_zero_iff (okE_tableAt _ _)).2 (lines vertex inRange).2

variable {files : VerifierAndGoals.PublicFiles} {settings : ScalesAndPolicy} {layout : Option ByteArray}
  {publicRecord : OnBytes.Model.Verify.Public} {index : Cm.Idx} {request : Instance ppref}

/-- **The head's class Request covers the positions that the served request covers**: its first
checked position and the end of its checked positions are the request's. On public data. The
library's reqX at the request meets it (requestOfTheInstanceCoversTheSamePositions). At the letters
of the first chain the class is P5J.At.rq at the instance's public part (the request that the
request file's words spell, Johnson/Desc/Kinds/Head/AtZ.lean): there it holds where the instance is
read as the request (Term/RequestAtTheLettersCoversTheSamePositions.lean). -/
structure RequestCoversTheSamePositions (headRequest : Request) (request : Instance ppref) :
    Prop where
  /-- the first checked position -/
  sameFirstPosition : headRequest.r = request.r
  /-- one behind the last checked position -/
  sameEndPosition : headRequest.e = request.e

/-- The library's own Request of an instance covers the instance's positions. -/
theorem requestOfTheInstanceCoversTheSamePositions (request : Instance ppref) :
    RequestCoversTheSamePositions (reqX request) request :=
  ⟨rfl, rfl⟩

/-- The tests on the head's plan pass in scope: what the two lines' readings ask. -/
theorem headPlanFactsInScope (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsRead : publicOf files.pol files.KL layout = .ok publicRecord) :
    letI := sizesOf publicRecord.hS
    letI := policyOf publicRecord.hS
    PlanFacts :=
  letI := sizesOf publicRecord.hS
  letI := policyOf publicRecord.hS
  letI : Request := ⟨fun _ => 0, 0, 0⟩
  letI : Token := ⟨0⟩
  planFacts (sT := publicRecord.hS.tabS)
    (VerifiableInference.Desc.Kinds.Head.Law.InScope.ok_in_scope filesAreInScope filesAreRead
        publicPartIsRead 0)

/-- **At the honest trace of a served request the two lines on a position's cost hold at every
position**, at every token and at every Request that covers the served request's positions. -/
theorem theTwoCostLinesHoldAtTheHonestTrace (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsRead : publicOf files.pol files.KL layout = .ok publicRecord)
    (requestIsServed : ServesAt publicRecord index request) (headRequest : Request)
    (requestCoversTheSamePositions : RequestCoversTheSamePositions headRequest request)
    (token : ℕ) :
    letI := sizesOf publicRecord.hS
    letI := policyOf publicRecord.hS
    letI := headRequest
    letI : Token := ⟨token⟩
    CornerGuests (traceCells publicRecord index (theTrace publicRecord index request)).toCells :=
  have atTheInstance :=
    letI := VerifiableInference.Desc.Kinds.Head.sizesOf publicRecord.hS
    letI : Policy := (VerifiableInference.Desc.Kinds.Head.parOf publicRecord.hS 0).policy
    letI := reqX request
    letI : Token := ⟨request.y.val⟩
    (headCells_says_theTrace filesAreInScope filesAreRead publicPartIsRead requestIsServed
        0).2.1.lines
  letI := sizesOf publicRecord.hS
  letI := policyOf publicRecord.hS
  theTwoCostLinesReadTheCheckedRangeAndTheCellsAlone
    (headPlanFactsInScope filesAreInScope filesAreRead publicPartIsRead) (reqX request) headRequest
    request.y.val token _ _ requestCoversTheSamePositions.sameFirstPosition.symm
    requestCoversTheSamePositions.sameEndPosition.symm rfl atTheInstance

/-- **So the rider of the head's lookup is 0 on its cubes, at every token**, at every tuple of
messages whose cells are those of the honest trace's list 24. -/
theorem headRiderVanishesAtTheHonestTrace (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsRead : publicOf files.pol files.KL layout = .ok publicRecord)
    (requestIsServed : ServesAt publicRecord index request) (headRequest : Request)
    (requestCoversTheSamePositions : RequestCoversTheSamePositions headRequest request)
    (place : Place) (tail : HTailF2) (sent : Sent) (radius : OracleShape → ℕ)
    (weightsOracle : Cb.OMsg Cb.Gl.E) (weightsReading : weightsOracle.Msg → ℕ → ℕ → Cb.Gl.E)
    (weightRows weightColumns : ℕ) (extension : Iop.ExtSpec) (witnessPart : Type)
    (messages : (laySg place sent radius weightsOracle).Msg)
    (messagesHoldTheTrace : MatsAre place tail sent radius weightsOracle weightsReading weightRows
      weightColumns messages (theTrace publicRecord index request 24))
    (token : ℕ) :
    letI := sizesOf publicRecord.hS
    letI := policyOf publicRecord.hS
    letI := headRequest
    Cb.Rider.OnCubes
      (headRider (adrOf publicRecord.hS publicRecord.HLy (borderOf publicRecord.y)) place tail sent
          radius weightsOracle weightsReading weightRows weightColumns extension witnessPart).g
      (headRider (adrOf publicRecord.hS publicRecord.HLy (borderOf publicRecord.y)) place tail sent
          radius weightsOracle weightsReading weightRows weightColumns extension witnessPart).f
        token messages := by
  letI := sizesOf publicRecord.hS
  letI := policyOf publicRecord.hS
  letI := headRequest
  have small : ∀ matrix row column,
      |theTrace publicRecord index request 24 matrix row column| < 2 ^ 18 :=
    fun matrix row column => lt_trans
      ((meetsAll_theTrace filesAreInScope filesAreRead publicPartIsRead requestIsServed).small 24
        matrix row column) (by norm_num)
  have sameCells :
    (traceCells publicRecord index (theTrace publicRecord index request)).toCells.cell =
      (headCells (adrOf publicRecord.hS publicRecord.HLy (borderOf publicRecord.y)) place tail sent
          radius weightsOracle weightsReading weightRows weightColumns messages).toCells.cell := by
    funext matrixName feature position
    rw [(head_cells_cast messages (theTrace publicRecord index request 24) messagesHoldTheTrace
          small).1 matrixName feature position]
    cases matrixName <;> rfl
  exact headRiderVanishesWhereTheTwoCostLinesHold _ place tail sent radius weightsOracle
    weightsReading weightRows weightColumns extension witnessPart token messages
    (theTwoCostLinesReadTheCheckedRangeAndTheCellsAlone
        (headPlanFactsInScope filesAreInScope filesAreRead publicPartIsRead) headRequest
      headRequest token token _ _ rfl rfl sameCells
      (theTwoCostLinesHoldAtTheHonestTrace filesAreInScope filesAreRead publicPartIsRead
          requestIsServed headRequest requestCoversTheSamePositions token))

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.theTwoCostLinesReadTheCheckedRangeAndTheCellsAlone
#print axioms ProofFile.Honest.K3.Term.headRiderVanishesWhereTheTwoCostLinesHold
#print axioms ProofFile.Honest.K3.Term.requestOfTheInstanceCoversTheSamePositions
#print axioms ProofFile.Honest.K3.Term.headPlanFactsInScope
#print axioms ProofFile.Honest.K3.Term.theTwoCostLinesHoldAtTheHonestTrace
#print axioms ProofFile.Honest.K3.Term.headRiderVanishesAtTheHonestTrace
