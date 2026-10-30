-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE BASE PROVER: NOT THE HONEST PROVER's FILLING: the honest prover's `onlineFilling`
(E2E/TheHonestProver.lean) is the base filling `onlineProverPartsInUse` read through `tableCoins`; its
return has another type; the crossing of the threads to it is not this folder's.
The wide filling is defined in Honest/K1/Law/WSideAtFill.lean. Here it is called the base filling.
This file does not show that the maker returns at it.

Johnson/Desc/ProofFile/Honest/K3/Term/LookupFiveAtEveryBorder.lean: the kind "lookup" (K3): the five
statements that a sub-protocol owes at its border, as the one structure `FiveAtBorder`
(Honest/Thread/FiveAtBorder.lean), at each of the lookups' fifty borders `borderOf l d`, l below 25,
at the first chain's thread of `lettersHead` (Honest/Thread/FirstHead.lean) with: the prover A.H, A
any return of `onlineProverFromPublicFiles` at the base filling at a variable index; the reply's border 339; the riders
`csHead` (Honest/Thread/CsHead.lean); "keeps" by the place's kind (`kpBy f`). Every letter is a
variable; what the lookups read of four of them is ONE structure. One structure, five theorems.

  `LookupReadsOfTheLetters`   four fields: the next free slot behind the head's lookup is 3531; the
                              sentence behind the digits follows from what the lookup lays; the
                              sentence on what attention's lookup returned holds of every hearing;
                              the clause of "keeps" at the kind K3 is `LookupClauseOfKeepsIs`
  `lookupThreeAtEveryBorder`  `PlaysS`, `RidesPastS`, `AcceptedS` at all fifty
  `lookupBehindAtTheCalls`    `BehindS` at the twenty-five calls
  `lookupBehindAtTheDigits`   `BehindS` at the twenty-five digits
  `lookupFourAtEveryBorder`   the four at all fifty
  `lookupFiveAtEveryBorder`   **the join**: `FiveAtBorder` at all fifty, from these and `ExchangeS`

What is paid, and where. `PlaysS`, `AcceptedS`: Honest/K3/Term/LookupPlaysAndIsAcceptedAtAllFifty.lean.
`BehindS`: Honest/K3/Term/LookupBehindAndRidesPast.lean, with
Honest/K3/Term/LookupAtTheClauseOfKeeps.lean. `RidesPastS`: that same file.

Hypotheses that remain. The head `P5J.AtMgA`. hA: `onlineProverFromPublicFiles` returns A. A Said that gives `SaidOk`.
`LookupReadsOfTheLetters`: Honest/K3/Term/LookupFiveAtTheFirstThread.lean shows it at the first
thread's letters. `ExchangeS` at all fifty, which carries the values: not this file's.

Limits. All statements are implications. Each of the five speaks from a stand of `ThrS`; that a run
reaches such a stand is not shown here. At the full size alone: that limit comes with the head.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupPlaysAndIsAcceptedAtAllFifty
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupAtTheClauseOfKeeps
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain Place Strs KindName)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.K3.Law (hearVia)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K3.Law.AtThr

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **What the lookups read of the first thread's letters.** A definition, meant as a hypothesis on
the four letters. -/
structure LookupReadsOfTheLetters (nextFreeSlot : Nat) (behindTheDigits : Nat → TS → Prop)
    (heardByAttention : Nat → Option OnBytes.Model.Forest.Heard → Prop)
    (f : KindName → Place → TS → TS → Prop) : Prop where
  /-- the ledger's next free slot behind the head's lookup on the digits -/
  nextFreeSlotIsTheWrittenOne : nextFreeSlot = 3531
  /-- on states alone: the sentence behind the digits of a link follows from what the lookup lays -/
  standingGivesTheClause : ∀ l, l < 25 → ∃ standsAtNumber : Nat, ∀ p,
    placeAt Zp.p.X l true = some p → ∀ t, StandsHere true standsAtNumber p.first t →
      behindTheDigits l t
  /-- the sentence on what the lookup on the calls of an attention link returned holds of whatever
  the hearing returns at the plan's shape -/
  attentionClauseHoldsOfEveryHearing : ∀ g, g < 12 → ∀ a, (P5J.At.X Zp).A[g]? = some a →
    ∀ p : VerifiableInference.Desc.First.Look.P, p.shape = some a.fs →
    ∀ F rs Hd G₁, hearVia p F rs = some (Hd, G₁) → heardByAttention g (some Hd)
  /-- the clause of "keeps" at the kind K3 -/
  clauseOfKeepsIs : LookupClauseOfKeepsIs Zp h.𝔇.pubD f

variable {Bk : ProverCoinCounts} {W₀ : Type} {I : WiderIn W₀}
  {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A)
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
  (nextFreeSlot : Nat) (behindTheDigits : Nat → TS → Prop)
  (heardByAttention : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop)
  (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
  (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)

local notation "TheLetters" =>
  lettersHead h A.H Q test carryX item n₁ n₂ 339 Vd
    (ridersOf (csHead nextFreeSlot behindTheDigits heardByAttention)) (kpBy f) w

include hA in
/-- **`PlaysS`, `RidesPastS`, `AcceptedS` at all fifty borders.** Conditional on the head, the maker's
return, a Said that gives `SaidOk`, and the sentence on f. -/
theorem lookupThreeAtEveryBorder (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (clauseIs : LookupClauseOfKeepsIs Zp h.𝔇.pubD f)
    (fall : Nat → TS → List Fmt.Drawn → Option String) (l : Nat) (linkBelow : l < 25) (d : Bool) :
    PlaysS (TheLetters).thread Said (borderOf l d) ∧
      RidesPastS (TheLetters).thread Said (borderOf l d) ∧
      AcceptedS (TheLetters).thread Said fall (borderOf l d) :=
  ⟨lookupPlaysAtAllFifty h hA Q test carryX item n₁ n₂ 339 Vd _ _ w Said l linkBelow d,
    lookupOpenItemsRidePastAtTheClauseOfKeeps h A.H Q test carryX item n₁ n₂ 339 Vd _ f w Said
      clauseIs saidGivesWordsBelowThePrime linkBelow d,
    lookupIsAcceptedAtAllFifty h hA Q test carryX item n₁ n₂ 339 Vd _ _ w Said fall l linkBelow d⟩

/-- **`BehindS` at the twenty-five lookups on the calls.** Conditional on the head, a Said that gives
`SaidOk`, and what the lookups read of the letters. -/
theorem lookupBehindAtTheCalls (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (reads : LookupReadsOfTheLetters h nextFreeSlot behindTheDigits heardByAttention f)
    (l : Nat) (linkBelow : l < 25) : BehindS (TheLetters).thread Said (borderOf l false) :=
  lookupFormRidersAndKeepsBehindTheCalls h A.H Q test carryX item n₁ n₂ Vd nextFreeSlot
    behindTheDigits heardByAttention f w Said saidGivesWordsBelowThePrime linkBelow
    (lookupStepPaysTheClauseOfKeeps h A.H Q test carryX item n₁ n₂ 339 Vd _ f w Said
      reads.clauseOfKeepsIs saidGivesWordsBelowThePrime linkBelow false)
    reads.attentionClauseHoldsOfEveryHearing

/-- **`BehindS` at the twenty-five lookups on the digits.** Conditional on the same. -/
theorem lookupBehindAtTheDigits (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (reads : LookupReadsOfTheLetters h nextFreeSlot behindTheDigits heardByAttention f)
    (l : Nat) (linkBelow : l < 25) : BehindS (TheLetters).thread Said (borderOf l true) := by
  have clauseBack := clauseOfKeepsGivesTheLookupClause reads.clauseOfKeepsIs
  have stepPays := lookupStepPaysTheClauseOfKeeps h A.H Q test carryX item n₁ n₂ 339 Vd
    (ridersOf (csHead nextFreeSlot behindTheDigits heardByAttention)) f w Said
    reads.clauseOfKeepsIs saidGivesWordsBelowThePrime linkBelow true
  obtain ⟨standsAtNumber, hStands⟩ := reads.standingGivesTheClause l linkBelow
  by_cases e : l = 24
  · subst e
    exact lookupFormRidersAndKeepsBehindTheHeadsDigits h A.H Q test carryX item n₁ n₂ Vd
      nextFreeSlot behindTheDigits heardByAttention f w Said saidGivesWordsBelowThePrime
      clauseBack stepPays reads.nextFreeSlotIsTheWrittenOne standsAtNumber hStands
  · exact lookupFormRidersAndKeepsBehindTheDigits h A.H Q test carryX item n₁ n₂ Vd
      nextFreeSlot behindTheDigits heardByAttention f w Said saidGivesWordsBelowThePrime
      (by omega) clauseBack stepPays standsAtNumber hStands

include hA in
/-- **`PlaysS`, `BehindS`, `RidesPastS`, `AcceptedS` at all fifty borders.** Conditional on the head,
the maker's return, a Said that gives `SaidOk`, and what the lookups read of the letters. -/
theorem lookupFourAtEveryBorder (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (reads : LookupReadsOfTheLetters h nextFreeSlot behindTheDigits heardByAttention f)
    (fall : Nat → TS → List Fmt.Drawn → Option String) (l : Nat) (linkBelow : l < 25) (d : Bool) :
    PlaysS (TheLetters).thread Said (borderOf l d) ∧ BehindS (TheLetters).thread Said (borderOf l d) ∧
      RidesPastS (TheLetters).thread Said (borderOf l d) ∧
      AcceptedS (TheLetters).thread Said fall (borderOf l d) := by
  obtain ⟨plays, ridesPast, accepted⟩ := lookupThreeAtEveryBorder h hA Q test carryX item n₁ n₂ Vd
    nextFreeSlot behindTheDigits heardByAttention f w Said saidGivesWordsBelowThePrime
    reads.clauseOfKeepsIs fall l linkBelow d
  refine ⟨plays, ?_, ridesPast, accepted⟩
  cases d with
  | false =>
    exact lookupBehindAtTheCalls h Q test carryX item n₁ n₂ Vd nextFreeSlot behindTheDigits
      heardByAttention f w Said saidGivesWordsBelowThePrime reads l linkBelow
  | true =>
    exact lookupBehindAtTheDigits h Q test carryX item n₁ n₂ Vd nextFreeSlot behindTheDigits
      heardByAttention f w Said saidGivesWordsBelowThePrime reads l linkBelow

include hA in
/-- **THE FIVE AT EACH OF THE LOOKUPS' FIFTY BORDERS.** Conditional on the head, the maker's return, a
Said that gives `SaidOk`, what the lookups read of the letters, and `ExchangeS` there. -/
theorem lookupFiveAtEveryBorder (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (reads : LookupReadsOfTheLetters h nextFreeSlot behindTheDigits heardByAttention f)
    (fall : Nat → TS → List Fmt.Drawn → Option String) (l : Nat) (linkBelow : l < 25) (d : Bool)
    (owedItemsHoldBehindTheStep : ExchangeS (TheLetters).thread Said (borderOf l d)) :
    FiveAtBorder (TheLetters).thread Said fall (borderOf l d) := by
  obtain ⟨plays, behind, ridesPast, accepted⟩ := lookupFourAtEveryBorder h hA Q test carryX
    item n₁ n₂ Vd nextFreeSlot behindTheDigits heardByAttention f w Said
    saidGivesWordsBelowThePrime reads fall l linkBelow d
  exact ⟨plays, behind, owedItemsHoldBehindTheStep, ridesPast, accepted⟩

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupThreeAtEveryBorder
#print axioms ProofFile.Honest.K3.Term.lookupBehindAtTheCalls
#print axioms ProofFile.Honest.K3.Term.lookupBehindAtTheDigits
#print axioms ProofFile.Honest.K3.Term.lookupFourAtEveryBorder
#print axioms ProofFile.Honest.K3.Term.lookupFiveAtEveryBorder
