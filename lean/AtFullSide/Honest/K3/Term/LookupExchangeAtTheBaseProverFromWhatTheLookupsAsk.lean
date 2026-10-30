-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT THE BASE PROVER: NOT THE HONEST PROVER's FILLING: onlineFilling is this one read through tableCoins; the crossing is not here.
AtFullSide/Honest/K3/Term/LookupExchangeAtTheBaseProverFromWhatTheLookupsAsk.lean: the honest side
of the kind "lookup" (K3). CONDITIONAL. `lookupExchangeAtTheBaseProverFromTheScriptsSentences`
(Johnson/Desc/ProofFile/Honest/K3/Term/LookupExchangeAtTheBaseProverFromTheScript.lean) with its
premise on the book and its four sentences on the Script paid from the head, the maker's return and
ONE structure on the Script, `LookupsAskOfTheScript`
(Johnson/Desc/ProofFile/Honest/K3/Term/WhatTheLookupsAskOfTheScript.lean). It lies in this folder
since two of the laws called lie here, and no file under Johnson/ imports one under AtFullSide/. No
definition; two theorems.

  `samplingRoundIsHeardInFrontOfTheDigits`   one premise beside the site's own: the head
      at a listed site on the digits that names a sampling round, that round is among the
      challenges heard in front of the lookup
  `lookupExchangeAtTheBaseProverFromWhatTheLookupsAsk`   eight premises, listed below
      `ExchangeS` at every number of the kind K3 in the written list of places

THE TOP's EIGHT PREMISES, each under its name. None is shown in this file.
  1  atHead                          the library's hypothesis `P5J.AtMgA`, at the earlier hash
  2  makerReturns                    `onlineProverFromPublicFiles` returns A at the base filling
  3  saidGivesWordsBelowThePrime     Said gives `SaidOk`
  4  validInputsHoldTheHonestTrace   on the letter Vd: each input that it lets by holds the honest
                                     trace of a served request, at the reader I.weights Zp. AT A
                                     LETTER Vd THAT LETS BY ANOTHER INPUT IT IS FALSE
  5  whatTheLookupsAskIsMet          on the Script Q: `LookupsAskOfTheScript`, seven fields, at Vd
                                     and I.weights Zp; its other letters are variables. NO SCRIPT
                                     IS SHOWN TO MEET IT
  6  replyBorderStandsInFront        b₀ ≤ 340, the border of the head's lookup on the calls
  7  formRidersAndKeepsBehind        `BehindS` at every listed site's border
  8  keepsGivesTheLookupClause       the letter Kp at a listed site's place gives `k3KeepsAt`
PAID HERE BY CALLS, of the twelve premises of the theorem called:
  bookLendsTheMaskRow              `bookLendsTheMaskRowUnderTheHeadAlone`
                                   (this folder's LookupThreeTestsUnderTheHeadAlone.lean)
  scriptLaysEveryLinksMaskRow      `scriptLaysEveryLinksMaskRowFromOwnersTexts`
                                   (this folder's MaskRowAtEveryLinkFromOwnersTexts.lean), from
                                   fields 5, 6 and 7
  scriptHoldsTheDigitArrays        `digitArraysFromWhatTheLookupsAsk` (the structure's file), from
                                   fields 2 and 3, with `samplingRoundIsHeardInFrontOfTheDigits`
  scriptHoldsThePackedTraceCells   `packedCellsFromWhatTheLookupsAsk`
                                   (Honest/K3/Term/PackedCellsFromWhatTheLookupsAsk.lean), from
                                   fields 1 and 2 and premise 4
  scriptCellsAreTheIndexWeights    `storedCellsFromWhatTheLookupsAsk` (the structure's file), from
                                   field 4

Limits. Implications from `ThrS` and the member's step: no state is shown to meet these at any
border. That the premises can hold together is not shown. The elder row `proverSideOfLookupInChainAtOneOwner`. The full size
alone. Nothing on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupExchangeAtTheBaseProverFromTheScript
import Johnson.Desc.ProofFile.Honest.K3.Term.PackedCellsFromWhatTheLookupsAsk
import AtFullSide.Honest.K3.Term.MaskRowAtEveryLinkFromOwnersTexts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.Honest.K3.Term
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain Place KindName Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K1 (PlaceIn)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.AtThr

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL}
  (atHead : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)

include atHead in
/-- **The round that samples the matrix is among the challenges heard in front of the lookup on the
digits.** Conditional on the head, the site, its sort and its round. -/
theorem samplingRoundIsHeardInFrontOfTheDigits (site : Site) (siteIsListed : site ∈ lookSites Zp)
    (onTheDigits : site.digits = true) {round : Nat} (namesTheRound : site.rng = some round) :
    round + 1 ≤ challengesHeardAtTheLookup cF site.link true := by
  have inFront := rng_front Zp (samplingRoundsStandInFrontUnderTheHead atHead) site siteIsListed
    round namesTheRound
  rw [lookupBaseIsTheRoundsToTheBorder atHead site siteIsListed, onTheDigits] at inFront
  exact inFront

variable {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A)
  (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
  (cs : List (RiderCl (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) TS))
  (Kp : Place → TS → TS → Prop) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

local notation "LB" => lettersHead atHead A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w

/-- **`ExchangeS` AT EVERY NUMBER OF THE KIND K3, AT THE BASE PROVER, FROM THE ONE STRUCTURE ON THE
SCRIPT.** Conditional on the eight premises that this file's head lists. The elder row. The full
size alone. -/
theorem lookupExchangeAtTheBaseProverFromWhatTheLookupsAsk
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
    (formRidersAndKeepsBehind : ∀ s ∈ lookSites Zp,
      BehindS (LB).thread Said (borderOf s.link s.digits))
    (keepsGivesTheLookupClause : ∀ s ∈ lookSites Zp, ∀ t t', Kp s.at_.place t t' →
      k3KeepsAt Zp s.at_.place t t') :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K3 → ExchangeS (LB).thread Said b :=
  lookupExchangeAtTheBaseProverFromTheScriptsSentences atHead makerReturns Q test carryX item n₁ n₂
    b₀ Vd cs Kp w Said saidGivesWordsBelowThePrime validInputsHoldTheHonestTrace
    (bookLendsTheMaskRowUnderTheHeadAlone atHead makerReturns)
    (scriptLaysEveryLinksMaskRowFromOwnersTexts atHead makerReturns
      (challengesInFront := fun link => challengesHeardAtTheLookup cF link false)
      (challengesRead := challengesRead) openingsLens openingsOwnState openingsFirstNumber
      openingsData whatTheLookupsAskIsMet.openingsTextIsLaid switchesData readers layout segments
      whatTheLookupsAskIsMet.switchTextsAnswer whatTheLookupsAskIsMet.switchesTextsAreLaid)
    (fun s siteIsListed onTheDigits _ _ placeIsFound _ namesTheRound =>
      digitArraysFromWhatTheLookupsAsk whatTheLookupsAskIsMet siteIsListed onTheDigits
        namesTheRound placeIsFound
        (samplingRoundIsHeardInFrontOfTheDigits atHead s siteIsListed onTheDigits namesTheRound))
    (fun s siteIsListed _ =>
      packedCellsFromWhatTheLookupsAsk whatTheLookupsAskIsMet validInputsHoldTheHonestTrace
        (link_lt_head atHead s siteIsListed))
    (fun _ _ _ => storedCellsFromWhatTheLookupsAsk whatTheLookupsAskIsMet _)
    replyBorderStandsInFront formRidersAndKeepsBehind keepsGivesTheLookupClause

end AtFullSide.Honest.K3.Term

#print axioms AtFullSide.Honest.K3.Term.samplingRoundIsHeardInFrontOfTheDigits
#print axioms AtFullSide.Honest.K3.Term.lookupExchangeAtTheBaseProverFromWhatTheLookupsAsk
