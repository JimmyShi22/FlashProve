-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT THE BASE PROVER: NOT THE HONEST PROVER's FILLING: onlineFilling is this one read through tableCoins; the crossing is not here.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupExchangeAtTheBaseProver.lean: the honest side of the
kind "lookup" (K3). CONDITIONAL. The debt `ExchangeS` (Honest/Thread/PaysS.lean) at every number of
the kind K3 in the written list of places, at the first chain's thread of `lettersHead`
(Honest/Thread/FirstHead.lean) with the prover A.H and the book A.B, A any return of `onlineProverFromPublicFiles` at the
base filling `onlineProverPartsInUse I o S O`, the index's reader I a variable. The Script Q and the
thread's other letters are variables. No definition; three theorems.

  `samplingRoundsStandInFrontUnderTheHead`   one premise: the head
      the public test `rngFrontB` accepts at the head's public part
  `lookupDataHoldsAtInputsThatHoldTheHonestTrace`   two premises: the head;
      validInputsHoldTheHonestTrace
      `LookupDataHoldsAtValidInputs` at what the lookup's row is handed (`lookupWitness`)
  `lookupExchangeAtTheBaseProver`   eleven premises, listed below
      `ExchangeS` at every number of the kind K3

THE TOP's ELEVEN PREMISES, each under its name. None is shown in this file.
   1  atHead                          the library's hypothesis `P5J.AtMgA`, at the earlier hash
   2  makerReturns                    `onlineProverFromPublicFiles` returns A at the base filling
   3  saidGivesWordsBelowThePrime     Said gives `SaidOk`
   4  validInputsHoldTheHonestTrace   on the letter Vd: each input that it lets by holds the honest
                                      trace of a served request, at the reader I.weights Zp. AT A
                                      LETTER Vd THAT LETS BY ANOTHER INPUT IT IS FALSE
   5  bookLendsTheMaskRow             on public data: `BookLendsTheMaskRowAtEverySite` at A.B
   6  scriptLaysEveryLinksMaskRow     on the Script: `ScriptLaysEveryLinksMaskRow` at the message's
                                      number `maskRowMessageNumber Zp`
   7  enoughChallengesAreHeard        on the letter challengesInFront of premise 6
   8  digitsWitnessFacts              on the Script's witness: `DigitsWitnessFacts`, at the
                                      reader `lookupWitness Zp (I.weights Zp)`
   9  callsWitnessFacts               on the Script's witness: `CallsWitnessFacts`, at that reader
  10  formRidersAndKeepsBehind        `BehindS` at every listed site's border
  11  keepsGivesTheLookupClause       the letter Kp at a listed site's place gives `k3KeepsAt`
The letter challengesInFront of premises 6 and 7 is a variable.
PAID HERE BY CALLS, of the premises of `lookupExchangeSharesFromWitnessFacts`
(Honest/K3/Term/LookupExchangeFromWitnessFacts.lean):
  hSeat                 `lookupSiteRestAtTheBaseProverAtTheHeadsPublicPart`
                        (Honest/K3/Term/LookupSiteRestAtTheBaseProver.lean), from 1 and 2
  hHead                 `lookupHeadReturnsFromTheThreadAlone`
                        (Honest/K3/Term/LookupHeadReturnsFromTheThread.lean), from 1
  hData                 `lookupDataHoldsAtInputsThatHoldTheHonestTrace`, from 1 and 4
  hReaderDigits, hReaderCalls   `readerAtBehindDigitsLookup`, `readerAtBehindCallsLookup`
                        (Honest/K3/Term/MaskEntriesAtTheWitness.lean), from 1 and 3
and then `lookupExchangeAtEveryBorder` (Honest/K3/Term/LookupOwesAgainWhatItReads.lean), from 1, 10
and 11.

Limits. Implications from `ThrS` and the member's step: no state is shown to meet these at any
border. That the premises can hold together is not shown. The elder row `proverSideOfLookupInChainAtOneOwner`. The full size
alone. Nothing on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupExchangeFromWitnessFacts
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupOwesAgainWhatItReads
import Johnson.Desc.ProofFile.Honest.K3.Term.MaskEntriesAtTheWitness
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupSiteRestAtTheBaseProver
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupHeadReturnsFromTheThread
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupDataAtTheHonestTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc (Chain Place KindName Strs)
open VerifiableInference.Desc.First.Look (digAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.AtThr

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL}
  (atHead : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)

include atHead in
/-- **Under the head the public test `rngFrontB` accepts**: at every site that names a round that
samples the matrix, that round stands in front of the lookup. Conditional on the head. -/
theorem samplingRoundsStandInFrontUnderTheHead : rngFrontB Zp = true := by
  have publicRecord : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X :=
    atHead.toAtMg.pubOne
  have cutsAreWritten := cuts_head atHead
  obtain ⟨fourPlans, twelveGroups, -, -⟩ :=
    publicNumbersInScope (Zp := Zp) atHead.toAtMg.scope atHead.toAtMg.reads publicRecord
  unfold rngFrontB rngFrontOn
  refine List.all_eq_true.2 fun site siteIsListed => ?_
  cases namesARound : site.rng with
  | none => rfl
  | some round =>
    exact decide_eq_true (roundInFrontAtWrittenTable fourPlans twelveGroups cutsAreWritten site
      siteIsListed
      (linkIsBelowTwentyFiveAtSite atHead.toAtMg.scope atHead.toAtMg.reads publicRecord site
        siteIsListed) namesARound)

include atHead in
/-- **What each lookup's row is handed is settled and meets the relation after the challenge, at
every input of a set of inputs that hold the honest trace of a served request.** Conditional on the
head and on validInputsHoldTheHonestTrace. -/
theorem lookupDataHoldsAtInputsThatHoldTheHonestTrace {W₀ Rc : Type} (weights : W₀ → Weights)
    (validInput : Local W₀ Rc ProofFile.Inst Cells → Prop)
    (validInputsHoldTheHonestTrace : ∀ input, validInput input →
      ∃ index request, InputHoldsTheHonestTrace Zp weights input index request) :
    LookupDataHoldsAtValidInputs Zp validInput fun site => lookupWitness Zp weights site := by
  intro input valid site siteIsListed
  obtain ⟨index, request, holds⟩ := validInputsHoldTheHonestTrace input valid
  have lawful := lookupDataAtTheHonestTrace atHead.toAtMg.scope atHead.toAtMg.reads
    atHead.toAtMg.pubOne (samplingRoundsStandInFrontUnderTheHead atHead) holds site siteIsListed
  exact ⟨lawful.settledAtTheFirstRound, lawful.relationAfterTheChallenge⟩

variable {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A)
  (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
  (cs : List (RiderCl (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) TS))
  (Kp : Place → TS → TS → Prop) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

local notation "LB" => lettersHead atHead A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w

include makerReturns in
/-- **`ExchangeS` AT EVERY NUMBER OF THE KIND K3, AT THE BASE PROVER.** Conditional on the head, the
maker's return and the nine named premises that this file's head lists. The elder row. The full size
alone. -/
theorem lookupExchangeAtTheBaseProver
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (validInputsHoldTheHonestTrace : ∀ input, Vd input →
      ∃ index request, InputHoldsTheHonestTrace Zp (I.weights Zp) input index request)
    (bookLendsTheMaskRow : BookLendsTheMaskRowAtEverySite A.B Zp)
    (challengesInFront : Nat → Nat)
    (scriptLaysEveryLinksMaskRow :
      ScriptLaysEveryLinksMaskRow Q Vd Zp challengesInFront (maskRowMessageNumber Zp))
    (enoughChallengesAreHeard : ∀ s ∈ lookSites Zp, challengesInFront s.link ≤
      (LB).thread.front + roundsTo (LB).thread.bs (borderOf s.link s.digits))
    (digitsWitnessFacts : ∀ s ∈ lookSites Zp, s.digits = true → ∀ (x : PlaceL) (tl : HTailF2),
      digAt Zp.p.X s.link = some (x, tl) →
      DigitsWitnessFacts atHead A.H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s
        (lookupWitness Zp (I.weights Zp) s) x tl)
    (callsWitnessFacts : ∀ s ∈ lookSites Zp, s.digits = false →
      CallsWitnessFacts atHead A.H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s
        (lookupWitness Zp (I.weights Zp) s))
    (formRidersAndKeepsBehind : ∀ s ∈ lookSites Zp,
      BehindS (LB).thread Said (borderOf s.link s.digits))
    (keepsGivesTheLookupClause : ∀ s ∈ lookSites Zp, ∀ t t', Kp s.at_.place t t' →
      k3KeepsAt Zp s.at_.place t t') :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K3 → ExchangeS (LB).thread Said b :=
  lookupExchangeAtEveryBorder atHead A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w Said
    (lookupExchangeSharesFromWitnessFacts atHead A.H Q test carryX item n₁ n₂ b₀ Vd cs Kp w
      (Rc' := IndexCommitterCoins) (sourcesAt id (I.weights Zp) (reqAt Zp) Zp)
      (fun site => lookupWitness Zp (I.weights Zp) site) Said saidGivesWordsBelowThePrime
      (fun s siteIsListed =>
        lookupSiteRestAtTheBaseProverAtTheHeadsPublicPart atHead makerReturns s siteIsListed)
      (fun s siteIsListed _ =>
        lookupHeadReturnsFromTheThreadAlone atHead A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs)
          Kp w s siteIsListed)
      (lookupDataHoldsAtInputsThatHoldTheHonestTrace atHead (I.weights Zp) Vd
        validInputsHoldTheHonestTrace)
      bookLendsTheMaskRow challengesInFront (maskRowMessageNumber Zp) scriptLaysEveryLinksMaskRow
      enoughChallengesAreHeard
      (fun s siteIsListed onTheDigits => by
        obtain ⟨sub, sortOfTheLink, -, -⟩ :=
          K3Lot.k03_sub_full s.link (link_lt_head atHead s siteIsListed)
        exact readerAtBehindDigitsLookup atHead A.H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s
          siteIsListed onTheDigits sortOfTheLink Said saidGivesWordsBelowThePrime)
      (fun s siteIsListed onTheCalls => by
        obtain ⟨sub, sortOfTheLink, -, -⟩ :=
          K3Lot.k03_sub_full s.link (link_lt_head atHead s siteIsListed)
        exact readerAtBehindCallsLookup atHead A.H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s
          siteIsListed onTheCalls sortOfTheLink Said saidGivesWordsBelowThePrime)
      digitsWitnessFacts callsWitnessFacts)
    formRidersAndKeepsBehind keepsGivesTheLookupClause

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.samplingRoundsStandInFrontUnderTheHead
#print axioms ProofFile.Honest.K3.Term.lookupDataHoldsAtInputsThatHoldTheHonestTrace
#print axioms ProofFile.Honest.K3.Term.lookupExchangeAtTheBaseProver
