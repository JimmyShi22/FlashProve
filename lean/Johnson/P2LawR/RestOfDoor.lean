-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/RestOfDoor.lean: SEVEN OF THE TEN CLOSED FIELDS LEFT
BY NAME BENEATH lastLeft_at_head (Johnson/P2LawR/LastLeftAtHead.lean: structure AtMgA.LastRest)
FOLLOW FROM THE HEAD ALONE, OVER LEAN FILES WHOSE DOOR (the proof file's entry tests) IS THE LIST OF
THIRTEEN ROWS. Where this and lean/THEOREM.md
differ, the page holds. AtMgA.LastRestTen is declared in Johnson/P2LawR/LastLeftOfTen.lean:81, with ten fields; AtMgA.LastRest is declared in Johnson/P2LawR/LastLeftAtHead.lean:66, with the one field core. ONE THEOREM: SEVEN CALLS OF OTHER FILES' THEOREMS: nothing of theirs is
typed anew. At every o.
  **AtMg.rest_of_door** (h : AtMg o Z D r Zp Np cF): in LastRest's order, in its fields' own texts:
    twoTrees   1 < (D.at frS.P.T.a).t₂            AtMg.trees_at
               (Johnson/HB/LLHARD/HeadFacts.lean: that number is 11): the one step beside a call
    elder      both elder seats' trees lie below t₁     AtMg.elderBelow_at
    endTests   a closed test and two memberships        AtMg.endTests_at
               (both: Johnson/HB/LLHARD/PlanOk3AtHead.lean)
    indexNo    (At.N Zp cF).indexNo = 4           AtMg.indexNo_at
               (Johnson/P5J/PlanSitsCore.lean)
    msgs       (At.N Zp cF).msgsAt none = 197 + wMsgs Zp    AtMg.num_at_head
               (Johnson/P5J/NumAtHeadCall.lean)
    cutRow · madeRow   the door's two rows on written values    AtMg.pins
               (Johnson/P5T/FenceAtMg.lean: by asks_pins, Johnson/Desc/Laid/ProofAsksLaw2.lean,
               off h.laid.asks)
  AtMgA.rest_of_door: the same under the wider head.
WHAT IS LEFT OF LastRest BEHIND IT: k2told · core · sits. Johnson/P2LawR/LastLeftAtHead.lean:86 calls k2Told_paid (declared in Johnson/IMR/ToldPaid.lean:59) and Johnson/P2LawR/LastLeftAtHead.lean:87 calls sits_at_head (declared in Johnson/P2LawR/SitsAtLeft.lean:39); AtMgA.LastRest is declared in Johnson/P2LawR/LastLeftAtHead.lean:66, with the one field core.
Limits. IT STANDS OVER NO LEAN FILES WHOSE DOOR IS THE LIST OF EIGHT ROWS: there h.laid.asks holds neither
row. THAT A HEAD CAN BE HAD AT GIVEN PUBLIC FILES UNDER THIRTEEN ROWS IS NOT SAID: NO MEMBER. The
numerals are the written values' numbers: they hold under the head because its own tests compare
with the written lists. The full size alone. Nothing on soundness or on hiding.

-/
import Johnson.HB.LLHARD.PlanOk3AtHead
import Johnson.P5J.NumAtHeadCall
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (openSets start sampledIn)
open VerifiableInference.Desc.Sound (sampledBelow)
open OnBytes.Maker (WholeD)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **SEVEN OF LastRest's FIELDS, FROM THE HEAD ALONE, AT THE DOOR's VERSION 2.** -/
theorem AtMg.rest_of_door (h : AtMg o Z D r Zp Np cF) :
    1 < (D.at OnBytes.Slice.frS.P.T.a).t₂ ∧
    ((At.N Zp cF).index.1 < (D.at OnBytes.Slice.frS.P.T.a).t₁ ∧
      (At.N Zp cF).w.1 < (D.at OnBytes.Slice.frS.P.T.a).t₁) ∧
    (sampledBelow ((D.at OnBytes.Slice.frS.P.T.a).t₁ + (D.at OnBytes.Slice.frS.P.T.a).t₂)
        (At.N Zp cF) ((openSets fullLinks
        (VerifiableInference.Desc.First.flatPlaces true fullLinks true)
        (start fullLinks))[(VerifiableInference.Desc.First.flatPlaces true fullLinks
        true).length]?.getD []) = true ∧
      (At.N Zp cF).w ∈ sampledIn (At.N Zp cF) ((openSets fullLinks
        (VerifiableInference.Desc.First.flatPlaces true fullLinks true)
        (start fullLinks))[(VerifiableInference.Desc.First.flatPlaces true fullLinks
        true).length]?.getD []) ∧
      (At.N Zp cF).index ∈ sampledIn (At.N Zp cF) ((openSets fullLinks
        (VerifiableInference.Desc.First.flatPlaces true fullLinks true)
        (start fullLinks))[(VerifiableInference.Desc.First.flatPlaces true fullLinks
        true).length]?.getD [])) ∧
    (At.N Zp cF).indexNo = 4 ∧
    (At.N Zp cF).msgsAt none = 197 + VerifiableInference.Desc.Last.wMsgs Zp ∧
    VerifiableInference.PlanWritten.cutRow (F0T o Zp Np cF) Zp = true ∧
    VerifiableInference.PlanWritten.madeRow Zp = true := by
  have h2 : 1 < (D.at OnBytes.Slice.frS.P.T.a).t₂ := by
    rw [h.trees_at.2]
    decide
  exact ⟨h2, h.elderBelow_at, h.endTests_at, h.indexNo_at, h.num_at_head, h.pins.2, h.pins.1⟩

/-- The same under the wider head. -/
theorem AtMgA.rest_of_door {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA o Z D r Zp Np cF x) :
    1 < (D.at OnBytes.Slice.frS.P.T.a).t₂ ∧
    ((At.N Zp cF).index.1 < (D.at OnBytes.Slice.frS.P.T.a).t₁ ∧
      (At.N Zp cF).w.1 < (D.at OnBytes.Slice.frS.P.T.a).t₁) ∧
    (sampledBelow ((D.at OnBytes.Slice.frS.P.T.a).t₁ + (D.at OnBytes.Slice.frS.P.T.a).t₂)
        (At.N Zp cF) ((openSets fullLinks
        (VerifiableInference.Desc.First.flatPlaces true fullLinks true)
        (start fullLinks))[(VerifiableInference.Desc.First.flatPlaces true fullLinks
        true).length]?.getD []) = true ∧
      (At.N Zp cF).w ∈ sampledIn (At.N Zp cF) ((openSets fullLinks
        (VerifiableInference.Desc.First.flatPlaces true fullLinks true)
        (start fullLinks))[(VerifiableInference.Desc.First.flatPlaces true fullLinks
        true).length]?.getD []) ∧
      (At.N Zp cF).index ∈ sampledIn (At.N Zp cF) ((openSets fullLinks
        (VerifiableInference.Desc.First.flatPlaces true fullLinks true)
        (start fullLinks))[(VerifiableInference.Desc.First.flatPlaces true fullLinks
        true).length]?.getD [])) ∧
    (At.N Zp cF).indexNo = 4 ∧
    (At.N Zp cF).msgsAt none = 197 + VerifiableInference.Desc.Last.wMsgs Zp ∧
    VerifiableInference.PlanWritten.cutRow (F0T o Zp Np cF) Zp = true ∧
    VerifiableInference.PlanWritten.madeRow Zp = true :=
  h.toAtMg.rest_of_door

end P5J

#print axioms P5J.AtMg.rest_of_door
#print axioms P5J.AtMgA.rest_of_door
