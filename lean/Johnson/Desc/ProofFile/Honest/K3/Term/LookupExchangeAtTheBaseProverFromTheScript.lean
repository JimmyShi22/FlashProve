-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT THE BASE PROVER: NOT THE HONEST PROVER's FILLING: onlineFilling is this one read through tableCoins; the crossing is not in this file.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupExchangeAtTheBaseProverFromTheScript.lean: the honest
side of the kind "lookup" (K3). CONDITIONAL. `lookupExchangeAtTheBaseProver`
(Honest/K3/Term/LookupExchangeAtTheBaseProver.lean) with its two premises at the Script's witness,
digitsWitnessFacts and callsWitnessFacts, paid by `digitsWitnessFactsAtTheHonestTrace` and
`callsWitnessFactsAtTheHonestTrace` (Honest/K3/Term/LookupWitnessFactsAtTheHonestTrace.lean), and
each number of challenges at its value: the rounds of the first chain's sub-protocols in front of
the lookup. No definition; two theorems.

  `callsBorderStandsInFrontOfBothBorders`   no premise
      a link's border on the calls is at most either of its two borders
  `lookupExchangeAtTheBaseProverFromTheScriptsSentences`   twelve premises, listed below
      `ExchangeS` at every number of the kind K3 in the written list of places

THE TOP's TWELVE PREMISES, each under its name. None is shown in this file.
   1  atHead                          the library's hypothesis `P5J.AtMgA`, at the earlier hash
   2  makerReturns                    `onlineProverFromPublicFiles` returns A at the base filling
   3  saidGivesWordsBelowThePrime     Said gives `SaidOk`
   4  validInputsHoldTheHonestTrace   on the letter Vd: each input that it lets by holds the honest
                                      trace of a served request, at the reader I.weights Zp. AT A
                                      LETTER Vd THAT LETS BY ANOTHER INPUT IT IS FALSE
   5  bookLendsTheMaskRow             on public data: `BookLendsTheMaskRowAtEverySite` at A.B
  ON THE SCRIPT, four sentences, each from the challenges heard in front of the lookup on:
   6  scriptLaysEveryLinksMaskRow     `ScriptLaysEveryLinksMaskRow`, at the message's number
                                      `maskRowMessageNumber Zp`; from the link's lookup on the calls
   7  scriptHoldsTheDigitArrays       `ScriptHoldsTheDigitArrays` at every listed site on the digits
                                      that names a sampling round
   8  scriptHoldsThePackedTraceCells  `ScriptHoldsThePackedTraceCellsAtTheLink` at every listed site
                                      on the calls
   9  scriptCellsAreTheIndexWeights   `ScriptCellsAreTheIndexWeights` at every listed site on the
                                      calls, at the reader I.weights Zp
  ON THE THREAD's LETTERS:
  10  replyBorderStandsInFront        b₀ ≤ 340, the border of the head's lookup on the calls
  11  formRidersAndKeepsBehind        `BehindS` at every listed site's border
  12  keepsGivesTheLookupClause       the letter Kp at a listed site's place gives `k3KeepsAt`
PAID HERE BY CALLS: enoughChallengesAreHeard of the theorem called, and the like premise of the two
theorems on the witness: at this thread front is 0 and bs is cF.blocksInOrder, by unfolding; the seat at the
head's link: `lookupSiteRestAtTheBaseProverAtTheHeadsPublicPart`
(Honest/K3/Term/LookupSiteRestAtTheBaseProver.lean); the head's link is 24: `P1K8T.headLink_at`.

Limits. Implications from `ThrS` and the member's step: no state is shown to meet these at any
border. That the premises can hold together is not shown. The elder row `proverSideOfLookupInChainAtOneOwner`. The full size
alone. Nothing on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupExchangeAtTheBaseProver
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupWitnessFactsAtTheHonestTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc (Chain Place KindName Strs)
open VerifiableInference.Desc.First.Look (digAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf ixOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.AtThr

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

/-- A link's border on the calls is at most either of its two borders. -/
theorem callsBorderStandsInFrontOfBothBorders (link : Nat) (digits : Bool) :
    borderOf link false ≤ borderOf link digits := by
  unfold borderOf ixOf
  cases digits <;> simp

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL}
  (atHead : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A)
  (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
  (cs : List (RiderCl (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) TS))
  (Kp : Place → TS → TS → Prop) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

local notation "LB" => lettersHead atHead A.H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w

include makerReturns in
/-- **`ExchangeS` AT EVERY NUMBER OF THE KIND K3, AT THE BASE PROVER, FROM FOUR SENTENCES ON THE
SCRIPT.** Conditional on the premises that this file's head lists. The elder row. The full size
alone. -/
theorem lookupExchangeAtTheBaseProverFromTheScriptsSentences
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (validInputsHoldTheHonestTrace : ∀ input, Vd input →
      ∃ index request, InputHoldsTheHonestTrace Zp (I.weights Zp) input index request)
    (bookLendsTheMaskRow : BookLendsTheMaskRowAtEverySite A.B Zp)
    (scriptLaysEveryLinksMaskRow : ScriptLaysEveryLinksMaskRow Q Vd Zp
      (fun link => roundsTo cF.blocksInOrder (borderOf link false)) (maskRowMessageNumber Zp))
    (scriptHoldsTheDigitArrays : ∀ s ∈ lookSites Zp, s.digits = true →
      ∀ (x : PlaceL) (tl : HTailF2), digAt Zp.p.X s.link = some (x, tl) →
      ∀ samplingRound, s.rng = some samplingRound →
      ScriptHoldsTheDigitArrays Q atHead.𝔇.sent atHead.𝔇.l3 Vd
        (roundsTo cF.blocksInOrder (borderOf s.link true)) x tl
        fun input heard => zzOwn Zp.p.X s.link input.trace (tritsAt heard samplingRound))
    (scriptHoldsThePackedTraceCells : ∀ s ∈ lookSites Zp, s.digits = false →
      ScriptHoldsThePackedTraceCellsAtTheLink atHead Q Vd
        (roundsTo cF.blocksInOrder (borderOf s.link false)) s.link)
    (scriptCellsAreTheIndexWeights : ∀ s ∈ lookSites Zp, s.digits = false →
      ScriptCellsAreTheIndexWeights Q atHead.𝔇.l3 Vd (roundsTo cF.blocksInOrder (borderOf s.link false))
        fun input => (I.weights Zp input.w₀).entry)
    (replyBorderStandsInFront : b₀ ≤ 340)
    (formRidersAndKeepsBehind : ∀ s ∈ lookSites Zp,
      BehindS (LB).thread Said (borderOf s.link s.digits))
    (keepsGivesTheLookupClause : ∀ s ∈ lookSites Zp, ∀ t t', Kp s.at_.place t t' →
      k3KeepsAt Zp s.at_.place t t') :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K3 → ExchangeS (LB).thread Said b := by
  have heardAtTheBorder : ∀ link digits, roundsTo cF.blocksInOrder (borderOf link digits) ≤
      (LB).thread.front + roundsTo (LB).thread.bs (borderOf link digits) :=
    fun _ _ => Nat.le_of_eq (Nat.zero_add _).symm
  refine lookupExchangeAtTheBaseProver atHead makerReturns Q test carryX item n₁ n₂ b₀ Vd cs Kp w
    Said saidGivesWordsBelowThePrime validInputsHoldTheHonestTrace bookLendsTheMaskRow
    (fun link => roundsTo cF.blocksInOrder (borderOf link false)) scriptLaysEveryLinksMaskRow
    (fun s _ => Nat.le_trans
      (roundsTo_mono cF.blocksInOrder _ _ (callsBorderStandsInFrontOfBothBorders s.link s.digits))
      (heardAtTheBorder s.link s.digits))
    (fun s siteIsListed onTheDigits x tl placeIsFound => ?_)
    (fun s siteIsListed onTheCalls => ?_) formRidersAndKeepsBehind keepsGivesTheLookupClause
  · exact digitsWitnessFactsAtTheHonestTrace atHead A.H Q test carryX item n₁ n₂ b₀ Vd cs Kp w
      (I.weights Zp) Said saidGivesWordsBelowThePrime s siteIsListed onTheDigits placeIsFound
      (roundsTo cF.blocksInOrder (borderOf s.link true))
      (by rw [onTheDigits]; exact heardAtTheBorder s.link true)
      (scriptHoldsTheDigitArrays s siteIsListed onTheDigits x tl placeIsFound)
  · exact callsWitnessFactsAtTheHonestTrace atHead A.H Q test carryX item n₁ n₂ b₀ Vd cs Kp w
      (I.weights Zp) Said saidGivesWordsBelowThePrime s siteIsListed onTheCalls
      validInputsHoldTheHonestTrace (roundsTo cF.blocksInOrder (borderOf s.link false))
      (by rw [onTheCalls]; exact heardAtTheBorder s.link false)
      (scriptHoldsThePackedTraceCells s siteIsListed onTheCalls)
      (scriptCellsAreTheIndexWeights s siteIsListed onTheCalls) _
      (fun _ => lookupSiteRestAtTheBaseProverAtTheHeadsPublicPart atHead makerReturns s
        siteIsListed)
      (fun atTheHeadsLink => by
        rw [atTheHeadsLink.trans (P1K8T.headLink_at atHead), onTheCalls]
        exact replyBorderStandsInFront)

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.callsBorderStandsInFrontOfBothBorders
#print axioms ProofFile.Honest.K3.Term.lookupExchangeAtTheBaseProverFromTheScriptsSentences
