-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT THE BASE PROVER: NOT THE HONEST PROVER's FILLING: onlineFilling is this one read through tableCoins; the crossing is not here.
E2E/Lookup/LookupPaysAllFiveAtTheBaseMaker.lean: the honest side of the kind "lookup" (K3).
CONDITIONAL. At a return A of THE BASE MAKER BY ITS NAME, `ProofFile.Honest.Term.baseMaker files`
(E2E/BaseMaker.lean: `onlineProverFromPublicFiles` at `onlineProverPartsInUse` at `matrixInput`, the earlier hash, `Sz.ref`
and `openHonest`), at the first chain's thread `firstThread` (Honest/Thread/TheFirstThread.lean):
the debt `ExchangeS`, and then all five statements that a lookup owes, at each of the fifty borders
`borderOf l d`, l below 25. No definition; three theorems.

  `readyInputsAtTheBaseMakerHoldTheHonestTrace`   one premise: makerReturns
      each input that `ReadyInput` lets by holds the honest trace of a served request
  `lookupExchangeAtTheFirstThreadOfTheBaseMaker`   four premises, listed below
      `ExchangeS (firstThread …) Said (borderOf l d)`
  `lookupPaysAllFiveAtTheFirstThreadOfTheBaseMaker`   the same four premises
      `FiveAtBorder (firstThread …) Said fall (borderOf l d)`, at every fall

THE FOUR PREMISES, each under its name. None is shown in this file.
  1  makerReturns                  `baseMaker files` returns A
  2  headAtTheReturn               `HeadAtReturn`: the library's hypothesis `P5J.AtMgA` at A.Z
  3  saidGivesWordsBelowThePrime   Said gives `SaidOk`
  4  whatTheLookupsAskIsMet        on the first thread's Script: `LookupsAskOfTheScript`, seven
                                   fields (Honest/K3/Term/WhatTheLookupsAskOfTheScript.lean), at
                                   `ReadyInput` and the plain reader of the matrix's cells. NO
                                   SCRIPT IS SHOWN TO MEET IT
PAID HERE, of the five premises of `lookupExchangeAtTheFirstThread` and
`lookupPaysAllFiveAtTheFirstThread` (AtFullSide/Honest/K3/Term/LookupExchangeAtTheFirstThread.lean):
validInputsHoldTheHonestTrace, by `readyInputsHoldTheHonestTrace`
(Honest/K3/Term/LookupDataAtReadyInputs.lean): that the base filling's trace goes through the index
that the matrix holds is true by unfolding, and so is it that `matrixInput`'s reader of the weights
is `matrixWeights`.

Limits. Implications from `ThrS` and the member's step: no state is shown to meet these at any
border. That the premises can hold together is not shown. The elder row `proverSideOfLookupInChainAtOneOwner`. The full size
alone. Nothing on soundness,
completeness, hiding or any other property of a protocol.
-/
import AtFullSide.Honest.K3.Term.LookupExchangeAtTheFirstThread
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupDataAtReadyInputs
import E2E.BaseMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.Lookup
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term
open AtFullSide.Honest.K3.Term (lookupExchangeAtTheFirstThread lookupPaysAllFiveAtTheFirstThread)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open P5J (TS)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstThread)
open ProofFile.Honest.K1 (PlaceIn)
open ProofFile.Honest.Term (baseMaker matrixInput)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
  (makerReturns : baseMaker files = .ok A)
  (headAtTheReturn : HeadAtReturn files A) (parts : FirstThreadParts A)
  (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
  (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)

include makerReturns in
/-- **At the base maker an input that ready could prepare holds the honest trace of a served
request**, at `matrixInput`'s own reader of the weights. Conditional on the maker's return. -/
theorem readyInputsAtTheBaseMakerHoldTheHonestTrace (input : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (ready : ReadyInput headAtTheReturn.description A.H input) :
    ∃ index request,
      InputHoldsTheHonestTrace A.Z (matrixInput.weights A.Z) input index request :=
  readyInputsHoldTheHonestTrace makerReturns (fun _ _ _ => rfl) input ready

/-- **`ExchangeS` AT EACH OF THE LOOKUPS' FIFTY BORDERS OF THE FIRST THREAD, AT THE BASE
MAKER.** Conditional on the four premises that this file's head lists. -/
theorem lookupExchangeAtTheFirstThreadOfTheBaseMaker
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    {readers : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Readers} {OpeningsInstance OpeningsOwnState : Type}
    {openingsLens : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → PlaceIn OpeningsInstance}
    {openingsOwnState : OpeningsOwnState} {openingsFirstNumber : Nat}
    {openingsData : RowDataOf OpeningsInstance} {switchesData : RowDataOf ProofFile.Inst}
    {layout : OnBytes.Params.ReqLayout} {segments : List K2.SegmentPub}
    {challengesRead : Nat → Nat}
    (whatTheLookupsAskIsMet : LookupsAskOfTheScript headAtTheReturn.head makerReturns parts.script
      (ReadyInput headAtTheReturn.description A.H) (matrixInput.weights A.Z) readers openingsLens
      openingsOwnState openingsFirstNumber openingsData switchesData layout segments
      challengesRead)
    (l : Nat) (linkBelow : l < 25) (d : Bool) :
    ExchangeS (firstThread headAtTheReturn parts w) Said (borderOf l d) :=
  lookupExchangeAtTheFirstThread makerReturns headAtTheReturn parts w Said
    saidGivesWordsBelowThePrime
    (readyInputsAtTheBaseMakerHoldTheHonestTrace makerReturns headAtTheReturn)
    whatTheLookupsAskIsMet l linkBelow d

/-- **ALL FIVE STATEMENTS THAT A LOOKUP OWES, AT EACH OF THE FIFTY BORDERS OF THE FIRST THREAD, AT
THE BASE MAKER.** Conditional on the same four premises. -/
theorem lookupPaysAllFiveAtTheFirstThreadOfTheBaseMaker
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    {readers : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Readers} {OpeningsInstance OpeningsOwnState : Type}
    {openingsLens : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → PlaceIn OpeningsInstance}
    {openingsOwnState : OpeningsOwnState} {openingsFirstNumber : Nat}
    {openingsData : RowDataOf OpeningsInstance} {switchesData : RowDataOf ProofFile.Inst}
    {layout : OnBytes.Params.ReqLayout} {segments : List K2.SegmentPub}
    {challengesRead : Nat → Nat}
    (whatTheLookupsAskIsMet : LookupsAskOfTheScript headAtTheReturn.head makerReturns parts.script
      (ReadyInput headAtTheReturn.description A.H) (matrixInput.weights A.Z) readers openingsLens
      openingsOwnState openingsFirstNumber openingsData switchesData layout segments
      challengesRead)
    (fall : Nat → TS → List Fmt.Drawn → Option String) (l : Nat) (linkBelow : l < 25) (d : Bool) :
    FiveAtBorder (firstThread headAtTheReturn parts w) Said fall (borderOf l d) :=
  lookupPaysAllFiveAtTheFirstThread makerReturns headAtTheReturn parts w Said
    saidGivesWordsBelowThePrime
    (readyInputsAtTheBaseMakerHoldTheHonestTrace makerReturns headAtTheReturn)
    whatTheLookupsAskIsMet fall l linkBelow d

end AtPublicFiles.Lookup

#print axioms AtPublicFiles.Lookup.readyInputsAtTheBaseMakerHoldTheHonestTrace
#print axioms AtPublicFiles.Lookup.lookupExchangeAtTheFirstThreadOfTheBaseMaker
#print axioms AtPublicFiles.Lookup.lookupPaysAllFiveAtTheFirstThreadOfTheBaseMaker
