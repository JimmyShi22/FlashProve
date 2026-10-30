-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT THE BOOK OF ANY RETURN OF THE MAKER; THE SCRIPT A LETTER; AT INPUTS THAT HOLD THE HONEST TRACE.
Johnson/Desc/ProofFile/Honest/K3/Term/PackedCellsFromWhatTheLookupsAsk.lean: the honest side of the
kind "lookup" (K3): from fields 1 and 2 of `LookupsAskOfTheScript`
(Term/WhatTheLookupsAskOfTheScript.lean): the named premise on the calls' cells,
`ScriptHoldsThePackedTraceCells` (Term/ScriptHoldsTheHonestValues.lean), at each of the 25 links, at the
number of challenges heard in front of that link's lookup on the calls, in the three forms that the
bundle at the calls binds.

  `challengesHeardGrowWithTheLink`       an earlier link's number is at most a later link's
  `cellsAreLaidAtEarlierLinks`           field 1, brought to one link's number at all links at or in front
  `packedCellsFromWhatTheLookupsAsk`     THE END: three implications, of which at most one speaks

Calls of `packedTraceCellsAtAttention`, `packedTraceCellsAtLayers`, `packedTraceCellsAtTheHead` and
`laysFillingAtMoreChallenges` (Term/PackedTraceCellsAtTheHonestTrace.lean).

Limits. CONDITIONAL on the structure, which no `Script` is shown to meet, and on
validInputsHoldTheHonestTrace, which is on the input and false at a valid that lets another input by.
The limits of the files called hold here. The full size and the earlier hash alone. Nothing is
claimed on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.WhatTheLookupsAskOfTheScript
import Johnson.Desc.ProofFile.Honest.K3.Term.PackedTraceCellsAtTheHonestTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.Desc.First.Look (attAt layAt)
open VerifiableInference.OnPublicFiles (headLink)
open ProofFile.Honest.FirstThread (Script)
open ProofFile.Honest.K1 (PlaceIn)
open ProofFile.Honest.K5 (LaysFilling)
open P5J (AtMgA TS CellsM)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "recordAt" => VerifiableInference.Desc.First.Look.tlAt

/-- What has been heard in front of an earlier link's lookup on the calls has been heard in front of
a later link's. -/
theorem challengesHeardGrowWithTheLink (cF : Chain TS ProofFile.Cl) {earlier link : Nat}
    (isEarlier : earlier ≤ link) :
    challengesHeardAtTheLookup cF earlier false ≤ challengesHeardAtTheLookup cF link false := by
  refine ProofFile.Honest.roundsTo_mono cF.blocksInOrder _ _ ?_
  unfold borderOf VerifiableInference.Desc.Sound.MgAt.ixOf
  simp only [Bool.false_eq_true, if_false]
  split <;> split <;> omega

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL} {atHead : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀}
  {W₀ Rc X₀ X : Type} {filling : ProofFile.Honest.OnlineProverParts W₀ Rc Cells X₀ X}
  {A : ProofFile.Honest.OnlineProverWithDescription W₀ Rc Cells X₀ X}
  {makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL filling = .ok A}
  {Q : Script A.B (Local W₀ Rc ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
  {valid : Local W₀ Rc ProofFile.Inst Cells → Prop} {weights : W₀ → Weights}
  {readers : Local W₀ Rc ProofFile.Inst Cells → Readers} {OpeningsInstance OpeningsOwnState : Type}
  {openingsLens : Local W₀ Rc ProofFile.Inst Cells → PlaceIn OpeningsInstance}
  {openingsOwnState : OpeningsOwnState} {openingsFirstNumber : Nat}
  {openingsData : RowDataOf OpeningsInstance} {switchesData : RowDataOf ProofFile.Inst}
  {layout : OnBytes.Params.ReqLayout} {segments : List K2.SegmentPub} {challengesRead : Nat → Nat}

/-- **Field 1 at one link's number, at every link at or in front of it.** -/
theorem cellsAreLaidAtEarlierLinks
    (asked : LookupsAskOfTheScript atHead makerReturns Q valid weights readers openingsLens
      openingsOwnState openingsFirstNumber openingsData switchesData layout segments challengesRead)
    {link : Nat} (linkBelow : link < 25) :
    ∀ earlier, earlier ≤ link → ∃ seat heard,
      LaysFilling atHead Q valid (challengesHeardAtTheLookup cF link false) readers seat heard
        earlier := by
  intro earlier isEarlier
  obtain ⟨seat, heard, lays⟩ := asked.cellsAreLaid earlier (Nat.lt_of_le_of_lt isEarlier linkBelow)
  exact ⟨seat, heard,
    laysFillingAtMoreChallenges atHead Q (challengesHeardGrowWithTheLink cF isEarlier) lays⟩

/-- **FROM FIELDS 1 AND 2: THE CALLS' CELLS AT EACH OF THE 25 LINKS**, at the place and the record that
the public readers answer at the link: three implications, in the form of
`ScriptHoldsThePackedTraceCellsAtTheLink` (Term/LookupWitnessFactsAtTheHonestTrace.lean). CONDITIONAL on
the structure and on validInputsHoldTheHonestTrace. -/
theorem packedCellsFromWhatTheLookupsAsk
    (asked : LookupsAskOfTheScript atHead makerReturns Q valid weights readers openingsLens
      openingsOwnState openingsFirstNumber openingsData switchesData layout segments challengesRead)
    (validInputsHoldTheHonestTrace : ∀ input, valid input →
      ∃ index request, InputHoldsTheHonestTrace Zp weights input index request)
    {link : Nat} (linkBelow : link < 25) :
    (∀ x A tl, attAt Zp.p.X link = some (x, A, tl) →
      ScriptHoldsThePackedTraceCells Q atHead.𝔇.sent atHead.𝔇.l3 valid
        (challengesHeardAtTheLookup cF link false) x tl
        fun input => traceMatricesOfTheCells Zp.p.X input.trace.cell link) ∧
    (∀ x tl, layAt Zp.p.X link = some x → recordAt Zp.p.X link = some tl →
      ScriptHoldsThePackedTraceCells Q atHead.𝔇.sent atHead.𝔇.l3 valid
        (challengesHeardAtTheLookup cF link false) x tl
        fun input => traceMatricesOfTheCells Zp.p.X input.trace.cell link) ∧
    (link = headLink Zp.p.X →
      ScriptHoldsThePackedTraceCells Q atHead.𝔇.sent atHead.𝔇.l3 valid
        (challengesHeardAtTheLookup cF link false) x₀ Zp.p.X.H.tl
        fun input => traceMatricesOfTheCells Zp.p.X input.trace.cell link) := by
  refine ⟨?_, ?_, fun isTheHeads => ?_⟩
  · exact packedTraceCellsAtAttention atHead Q validInputsHoldTheHonestTrace
      asked.readersReadTheTrace linkBelow (cellsAreLaidAtEarlierLinks asked linkBelow)
  · exact packedTraceCellsAtLayers atHead Q validInputsHoldTheHonestTrace
      asked.readersReadTheTrace linkBelow (cellsAreLaidAtEarlierLinks asked linkBelow)
  · obtain rfl : link = 24 := isTheHeads.trans (P1K8T.headLink_at atHead)
    exact packedTraceCellsAtTheHead atHead Q validInputsHoldTheHonestTrace
      asked.readersReadTheTrace (cellsAreLaidAtEarlierLinks asked linkBelow)

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.challengesHeardGrowWithTheLink
#print axioms ProofFile.Honest.K3.Term.cellsAreLaidAtEarlierLinks
#print axioms ProofFile.Honest.K3.Term.packedCellsFromWhatTheLookupsAsk
