-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT THE BASE PROVER: NOT THE HONEST PROVER's FILLING: onlineFilling is this one read through tableCoins; the crossing is not in this file.
AtFullSide/Honest/K3/Term/LookupExchangeAtTheFirstThread.lean: the honest side of the kind "lookup"
(K3). CONDITIONAL. The debt `ExchangeS` (Honest/Thread/PaysS.lean) at each of the lookups' fifty
borders, at a return A of `onlineProverFromPublicFiles` at the base filling `onlineProverPartsInUse I o S O`: first at every
letter "rides" and every letter "keeps" of `lettersHead` (Honest/Thread/FirstHead.lean), then at the
first chain's thread BY ITS NAME, `firstThread` (Honest/Thread/TheFirstThread.lean). That is the one
premise that `lookupFiveAtTheFirstThread` (Honest/K3/Term/LookupFiveAtTheFirstThread.lean) leaves:
the last theorem calls it. OF THE FILES ON THE LOOKUPS' EXCHANGE THIS ONE ALONE NAMES THAT THREAD,
and of its letters it reads four: the Script parts.script, the border 339, the valid inputs
`ReadyInput`, the run's input w. No definition; three theorems.

  `lookupExchangeAtTheBaseProverAtEveryRidersAndKeeps`   seven premises, listed below
      `ExchangeS` at every number of the kind K3, at every letter "rides" and "keeps"
  `lookupExchangeAtTheFirstThread`   five premises: 1 to 5 below, the head as `HeadAtReturn`
      `ExchangeS (firstThread …) Said (borderOf l d)`, l below 25
  `lookupPaysAllFiveAtTheFirstThread`   the five premises of `lookupExchangeAtTheFirstThread`
      `FiveAtBorder` (Honest/Thread/FiveAtBorder.lean) at `borderOf l d`, l below 25, at every fall

THE SEVEN PREMISES, each under its name. None is shown in this file.
  1  atHead                          the library's hypothesis `P5J.AtMgA`, at the earlier hash
  2  makerReturns                    `onlineProverFromPublicFiles` returns A at the base filling
  3  saidGivesWordsBelowThePrime     Said gives `SaidOk`
  4  validInputsHoldTheHonestTrace   on the letter Vd: each input that it lets by holds the honest
                                     trace of a served request, at the reader I.weights Zp. AT A
                                     LETTER Vd THAT LETS BY ANOTHER INPUT IT IS FALSE
  5  whatTheLookupsAskIsMet          on the Script: `LookupsAskOfTheScript`, seven fields
                                     (Honest/K3/Term/WhatTheLookupsAskOfTheScript.lean). NO SCRIPT
                                     IS SHOWN TO MEET IT
  6  replyBorderStandsInFront        b₀ ≤ 340, the border of the head's lookup on the calls
  7  replyBorderIsNotBehindALookup   b₀ is the border behind no lookup
At the first thread b₀ is 339: 6 is decided and 7 is `replyBorderIsBehindNoLookup`
(Honest/K3/Term/LookupBehindAndRidesPast.lean).

How the first proof goes. `lookupExchangeAtTheBaseProverFromWhatTheLookupsAsk` (this folder) is
called at no rider and at the lookups' own clause of "keeps". There its premise
formRidersAndKeepsBehind is `lookupBehindAtNoRidersAndTheLookupsOwnClause` and its premise
keepsGivesTheLookupClause is an identity. `exchangeAtEveryRidersAndKeeps` carries the end to every
"rides" and "keeps" (both: Honest/K3/Term/LookupExchangeAtEveryRidersAndKeeps.lean).

Limits. Implications from `ThrS` and the member's step: no state is shown to meet these at any
border. That the premises can hold together is not shown. The elder row `proverSideOfLookupInChainAtOneOwner`. The full size
alone. Nothing on soundness,
completeness, hiding or any other property of a protocol.
-/
import AtFullSide.Honest.K3.Term.LookupExchangeAtTheBaseProverFromWhatTheLookupsAsk
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupExchangeAtEveryRidersAndKeeps
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupFiveAtTheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.Honest.K3.Term
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain Place KindName Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf places_are_k3)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF HeadAtReturn FirstThreadParts firstThread)
open ProofFile.Honest.K1 (PlaceIn)
open ProofFile.Honest.K3.Law.AtThr (k3KeepsAt link_lt_head)

/-! ## 1 At every letter "rides" and every letter "keeps" -/

section AtTheLetters
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (atHead : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A)
  (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
  (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

/-- **`ExchangeS` AT EVERY NUMBER OF THE KIND K3, AT THE BASE PROVER, WHATEVER THE THREAD's RIDERS
AND "keeps".** Conditional on the seven premises that this file's head lists. The elder row. The
full size alone. -/
theorem lookupExchangeAtTheBaseProverAtEveryRidersAndKeeps
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (validInputsHoldTheHonestTrace : ∀ input, Vd input →
      ∃ index request, InputHoldsTheHonestTrace Zp (I.weights Zp) input index request)
    {readers : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Readers} {OpeningsInstance OpeningsOwnState : Type}
    {openingsLens : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → PlaceIn OpeningsInstance}
    {openingsOwnState : OpeningsOwnState} {openingsFirstNumber : Nat}
    {openingsData : RowDataOf OpeningsInstance} {switchesData : RowDataOf ProofFile.Inst}
    {layout : OnBytes.Params.ReqLayout} {segments : List K2.SegmentPub}
    {challengesRead : Nat → Nat}
    (whatTheLookupsAskIsMet : LookupsAskOfTheScript atHead makerReturns Q Vd (I.weights Zp) readers
      openingsLens openingsOwnState openingsFirstNumber openingsData switchesData layout segments
      challengesRead)
    (replyBorderStandsInFront : b₀ ≤ 340)
    (replyBorderIsNotBehindALookup : ∀ l d, b₀ ≠ borderOf l d + 1)
    (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K3 →
      ExchangeS (lettersHead atHead A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b :=
  fun b p placeIsWritten isALookup =>
    exchangeAtEveryRidersAndKeeps atHead A.H Q test carryX item n₁ n₂ b₀ Vd w Said
      (lookupExchangeAtTheBaseProverFromWhatTheLookupsAsk atHead makerReturns Q test carryX item n₁
        n₂ b₀ Vd [] (kpBy fun _ place => k3KeepsAt Zp place) w Said saidGivesWordsBelowThePrime
        validInputsHoldTheHonestTrace whatTheLookupsAskIsMet replyBorderStandsInFront
        (fun s siteIsListed =>
          lookupBehindAtNoRidersAndTheLookupsOwnClause atHead A.H Q test carryX item n₁ n₂ b₀ Vd w
            Said saidGivesWordsBelowThePrime (link_lt_head atHead s siteIsListed) s.digits
            (replyBorderIsNotBehindALookup s.link s.digits))
        (fun _ _ _ _ kept => kept) b p placeIsWritten isALookup)
      Rd Kp

end AtTheLetters

/-! ## 2 At the first thread, by its name -/

section AnyIndex
variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument}
  {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (makerReturns :
    onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I o S O) = .ok A)
  (headAtTheReturn : HeadAtReturn files A) (parts : FirstThreadParts A)
  (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
  (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)

/-- **`ExchangeS` AT EACH OF THE LOOKUPS' FIFTY BORDERS OF THE FIRST THREAD.** Conditional on five
premises: the maker's return, the head at it, a Said that gives `SaidOk`, the ready inputs' trace,
and what the lookups ask of the first thread's Script. The elder row. The full size alone. -/
theorem lookupExchangeAtTheFirstThread
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (validInputsHoldTheHonestTrace : ∀ input,
      ReadyInput headAtTheReturn.description A.H input →
      ∃ index request, InputHoldsTheHonestTrace A.Z (I.weights A.Z) input index request)
    {readers : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Readers} {OpeningsInstance OpeningsOwnState : Type}
    {openingsLens : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → PlaceIn OpeningsInstance}
    {openingsOwnState : OpeningsOwnState} {openingsFirstNumber : Nat}
    {openingsData : RowDataOf OpeningsInstance} {switchesData : RowDataOf ProofFile.Inst}
    {layout : OnBytes.Params.ReqLayout} {segments : List K2.SegmentPub}
    {challengesRead : Nat → Nat}
    (whatTheLookupsAskIsMet : LookupsAskOfTheScript headAtTheReturn.head makerReturns parts.script
      (ReadyInput headAtTheReturn.description A.H) (I.weights A.Z) readers openingsLens
      openingsOwnState openingsFirstNumber openingsData switchesData layout segments
      challengesRead)
    (l : Nat) (linkBelow : l < 25) (d : Bool) :
    ExchangeS (firstThread headAtTheReturn parts w) Said (borderOf l d) :=
  lookupExchangeAtTheBaseProverAtEveryRidersAndKeeps headAtTheReturn.head makerReturns parts.script
    _ _ _ _ _ 339 (ReadyInput headAtTheReturn.description A.H) w Said saidGivesWordsBelowThePrime
    validInputsHoldTheHonestTrace whatTheLookupsAskIsMet (by decide) replyBorderIsBehindNoLookup
    _ _ (borderOf l d) _ (places_are_k3 linkBelow d) rfl

/-- **ALL FIVE STATEMENTS THAT A LOOKUP OWES, AT EACH OF THE FIFTY BORDERS OF THE FIRST THREAD.**
Conditional on the five premises of `lookupExchangeAtTheFirstThread`. -/
theorem lookupPaysAllFiveAtTheFirstThread
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (validInputsHoldTheHonestTrace : ∀ input,
      ReadyInput headAtTheReturn.description A.H input →
      ∃ index request, InputHoldsTheHonestTrace A.Z (I.weights A.Z) input index request)
    {readers : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Readers} {OpeningsInstance OpeningsOwnState : Type}
    {openingsLens : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → PlaceIn OpeningsInstance}
    {openingsOwnState : OpeningsOwnState} {openingsFirstNumber : Nat}
    {openingsData : RowDataOf OpeningsInstance} {switchesData : RowDataOf ProofFile.Inst}
    {layout : OnBytes.Params.ReqLayout} {segments : List K2.SegmentPub}
    {challengesRead : Nat → Nat}
    (whatTheLookupsAskIsMet : LookupsAskOfTheScript headAtTheReturn.head makerReturns parts.script
      (ReadyInput headAtTheReturn.description A.H) (I.weights A.Z) readers openingsLens
      openingsOwnState openingsFirstNumber openingsData switchesData layout segments
      challengesRead)
    (fall : Nat → TS → List Fmt.Drawn → Option String) (l : Nat) (linkBelow : l < 25) (d : Bool) :
    FiveAtBorder (firstThread headAtTheReturn parts w) Said fall (borderOf l d) :=
  lookupFiveAtTheFirstThread makerReturns headAtTheReturn parts w Said saidGivesWordsBelowThePrime
    fall l linkBelow d
    (lookupExchangeAtTheFirstThread makerReturns headAtTheReturn parts w Said
      saidGivesWordsBelowThePrime validInputsHoldTheHonestTrace whatTheLookupsAskIsMet l linkBelow
      d)

end AnyIndex

end AtFullSide.Honest.K3.Term

#print axioms AtFullSide.Honest.K3.Term.lookupExchangeAtTheBaseProverAtEveryRidersAndKeeps
#print axioms AtFullSide.Honest.K3.Term.lookupExchangeAtTheFirstThread
#print axioms AtFullSide.Honest.K3.Term.lookupPaysAllFiveAtTheFirstThread
