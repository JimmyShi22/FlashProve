-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE BASE PROVER: NOT THE HONEST PROVER's FILLING: the honest prover's `onlineFilling`
(E2E/TheHonestProver.lean) is the base filling `onlineProverPartsInUse` read through `tableCoins`; its
return has another type; the crossing of the threads to it is not this folder's.
The wide filling is defined in Honest/K1/Law/WSideAtFill.lean. Here it is called the base filling.
This file does not show that the maker returns at it.

Johnson/Desc/ProofFile/Honest/K3/Term/LookupFiveAtTheFirstThread.lean: the kind "lookup" (K3): the
statements that a lookup owes at its border, at the first chain's thread BY ITS NAME: `firstThread h
parts w` (Honest/Thread/TheFirstThread.lean), at a return A of `onlineProverFromPublicFiles` at the base filling at a
variable index, at each of the fifty borders `borderOf l d`, l below 25. THIS IS THE ONE FILE OF THE
LOOKUPS THAT NAMES THE FIRST THREAD's LETTERS: Lean holds them here. Five theorems.

  `firstClausesAtTheLookups`                  the first thread's clause of "keeps" at the kind K3 is
                                              `LookupClauseOfKeepsIs`: by unfolding its layers
  `digitsStandFollowsFromWhatTheLookupLays`   on states alone
  `lookupReadsOfTheFirstThreadsLetters`       `LookupReadsOfTheLetters` at the first thread's four
                                              letters: under the head alone
  `lookupFourAtTheFirstThread`                `PlaysS`, `BehindS`, `RidesPastS`, `AcceptedS` at all
                                              fifty
  `lookupFiveAtTheFirstThread`                `FiveAtBorder` (Honest/Thread/FiveAtBorder.lean) at all
                                              fifty, from `ExchangeS` there

Hypotheses that remain. hA: `onlineProverFromPublicFiles` returns A. The head at the return (`HeadAtReturn`). A Said that
gives `SaidOk`. For the last: `ExchangeS`, which carries the values: not this file's.

The four letters. The next free slot: `nextSlotBehindTheHead`, 3531. The sentence behind the digits:
`digitsStand`: at the head's link, that what the lookup has heard stands for some rounds (`StandsHere`,
Honest/K3/Law/Thread/LaysStands.lean), at the number 5 and the place's first slot; at the other links
nothing: that is what the lookup lays. That it stays past the member behind the lookup is that
member's. The sentence on attention's lookup: `heardByAttention`: it holds of every hearing
(`attentionClauseAtLookRHoldsOfEveryHearing`). The clause of "keeps": `firstClauses h`: a tower of
layers, each of which beyond the third is "True" at the kind K3. Where a layer is added to that tower,
`firstClausesAtTheLookups` turns by one projection and one `trivial`, and nothing else of the lookups'.

Limits. All statements are implications. Each speaks from a stand of `ThrS`; that a run reaches such a
stand is not shown here. At the full size alone.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupFiveAtEveryBorder
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupAttentionClauseAtLookR
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.Desc.First.Look (placeAt)
open P5J (TS)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstThread firstClauses digitsStand
  heardByAttention nextSlotBehindTheHead)
open ProofFile.Honest.K3.Law.AtThr (StandsHere)

/-- **The first thread's sentence behind the digits follows from what the lookup lays.** On states
alone; no hypothesis. -/
theorem digitsStandFollowsFromWhatTheLookupLays (publicPart : ProofFile.Pub) (l : Nat) :
    ∃ standsAtNumber : Nat, ∀ p, placeAt publicPart.p.X l true = some p → ∀ t,
      StandsHere true standsAtNumber p.first t → digitsStand publicPart l t := by
  refine ⟨5, fun p hp t hStands e p' hp' => ?_⟩
  subst e
  obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
  exact hStands

section
variable {files : VerifierAndGoals.PublicFiles} {W₀ Rc Tr X₀ X : Type} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (h : HeadAtReturn files A)

/-- **The first thread's clause of "keeps" at the kind K3**, by unfolding its layers. No
hypothesis. -/
theorem firstClausesAtTheLookups :
    LookupClauseOfKeepsIs A.Z h.head.𝔇.pubD (firstClauses h) :=
  fun _ _ _ =>
    ⟨fun clause => ⟨⟨clause.1.1.1.1.1, clause.1.1.1.1.2⟩, clause.1.1.1.2⟩,
      fun clause => ⟨⟨⟨⟨⟨clause.1.1, clause.1.2⟩, clause.2⟩, trivial⟩, trivial⟩, trivial⟩⟩

/-- **What the lookups read of the letters holds at the first thread's four letters.** Conditional on
the head at the return alone. -/
theorem lookupReadsOfTheFirstThreadsLetters :
    LookupReadsOfTheLetters h.head nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)
      (firstClauses h) where
  nextFreeSlotIsTheWrittenOne := rfl
  standingGivesTheClause := fun l _ => digitsStandFollowsFromWhatTheLookupLays A.Z l
  attentionClauseHoldsOfEveryHearing := attentionClauseAtLookRHoldsOfEveryHearing h.head
  clauseOfKeepsIs := firstClausesAtTheLookups h

end

variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument}
  {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I o S O) = .ok A)
  (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
  (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)

include hA in
/-- **`PlaysS`, `BehindS`, `RidesPastS`, `AcceptedS` at all fifty borders of the first thread.**
Conditional on the maker's return, the head at it, and a Said that gives `SaidOk`. -/
theorem lookupFourAtTheFirstThread
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (fall : Nat → TS → List Fmt.Drawn → Option String) (l : Nat) (linkBelow : l < 25) (d : Bool) :
    PlaysS (firstThread h parts w) Said (borderOf l d) ∧
      BehindS (firstThread h parts w) Said (borderOf l d) ∧
      RidesPastS (firstThread h parts w) Said (borderOf l d) ∧
      AcceptedS (firstThread h parts w) Said fall (borderOf l d) :=
  lookupFourAtEveryBorder h.head hA _ _ _ _ _ _ _ nextSlotBehindTheHead (digitsStand A.Z)
    (heardByAttention A.Z) (firstClauses h) w Said saidGivesWordsBelowThePrime
    (lookupReadsOfTheFirstThreadsLetters h) fall l linkBelow d

include hA in
/-- **THE FIVE AT EACH OF THE LOOKUPS' FIFTY BORDERS OF THE FIRST THREAD**, from `ExchangeS` there. -/
theorem lookupFiveAtTheFirstThread
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (fall : Nat → TS → List Fmt.Drawn → Option String) (l : Nat) (linkBelow : l < 25) (d : Bool)
    (owedItemsHoldBehindTheStep : ExchangeS (firstThread h parts w) Said (borderOf l d)) :
    FiveAtBorder (firstThread h parts w) Said fall (borderOf l d) := by
  obtain ⟨plays, behind, ridesPast, accepted⟩ := lookupFourAtTheFirstThread hA h parts w Said
    saidGivesWordsBelowThePrime fall l linkBelow d
  exact ⟨plays, behind, owedItemsHoldBehindTheStep, ridesPast, accepted⟩

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.digitsStandFollowsFromWhatTheLookupLays
#print axioms ProofFile.Honest.K3.Term.firstClausesAtTheLookups
#print axioms ProofFile.Honest.K3.Term.lookupReadsOfTheFirstThreadsLetters
#print axioms ProofFile.Honest.K3.Term.lookupFourAtTheFirstThread
#print axioms ProofFile.Honest.K3.Term.lookupFiveAtTheFirstThread
