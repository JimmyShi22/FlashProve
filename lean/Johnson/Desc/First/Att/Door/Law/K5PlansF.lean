-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5PlansF.lean: kind K5 (an attention segment's own rounds): THE KIND's CLOSED TESTS ON THE SEATS AND ON THE SHAPES (K5WrittenPlans.lean: seatsAllW g · shapesAllW g) IN A FORM THAT LEAN's KERNEL CAN WALK.
The names LFull · laid_written · msgs_written stand in this file's own namespace too, for other things (the written list of segments; laws under the head): the four of Johnson/HB/LLHARD/LaidWritten.lean are written with their whole names.

Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)


Why. The closed tests stand over two terms at which an evaluation in the kernel does not end: the written seats with the roots in front of a sending summed over all 48,293 written rounds, and the sendings passed through a sort by well-founded recursion. Both have forms made for the kernel in other files: the same seats with the roots off the 82 sendings (Johnson/P5T/PlanSeatsFull.lean: psFull), and the listed seats and shapes over the written sendings as they stand (Johnson/HB/LLHARD/LaidWritten.lean: LFull · MFull, with laid_written · msgs_written: the written sendings stand in the order of their entries, so the sort returns them).

Main names:
  `laidW_is`, `msgsW_is`: laidW = some LFull · msgsW = MFull: by those files' laws (and codes_written, Johnson/Desc/Ok/PlanWritten/SizedTestLaws.lean); nothing is evaluated here.
  `numsF`, `seatsAtF`, `seatsAllF g`, `shapesAllF g`: the closed tests' own texts, with psFull for the written seats, LFull for the listed seats, MFull for the listed shapes.
  `seatsAllW_eq`, `shapesAllW_eq`: under E : pseatsW = psFull the two forms are one.
Is it empty here? Sentences without a premise, and equations.
Limits. They speak of the written values.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5WrittenPlans
import Johnson.P5T.PlanSeatsFull
import Johnson.HB.LLHARD.LaidWritten
import Johnson.Desc.Ok.PlanWritten.SizedTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.FillSent (baseAt)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.PlanWritten (proofSizedFull codes_written)

theorem laidW_is : laidW = some VerifiableInference.Desc.K13.Law.LFull := by
  unfold laidW
  rw [codes_written]
  exact VerifiableInference.Desc.K13.Law.laid_written

theorem msgsW_is : msgsW = VerifiableInference.Desc.K13.Law.MFull := VerifiableInference.Desc.K13.Law.msgs_written

/-- The table's numbers over the written seats psFull (Johnson/P5T/PlanSeatsFull.lean). -/
def numsF : Numbers := (P5T.numbersOf P5T.psFull).withTold P5J.At.ps toldW

def seatsAtF (g : ℕ) (L : Laid) : Bool :=
  seatsAllBy proofSizedFull.request (baseAt numsF P5J.At.links P5J.At.ps) (fun _ => []) sentW (fun _ => 0)
    (fun k => P6T.seatCallsT P5T.psFull sentW (2 * g + 1) k) (numsF.sent (2 * g + 1) 0) (numsF.msgsAt (some ⟨1, some (2 * g + 1), 3, .K5⟩)) (2 * g + 1) L

def seatsAllF (g : ℕ) : Bool := seatsAtF g VerifiableInference.Desc.K13.Law.LFull

def shapesAllF (g : ℕ) : Bool :=
  shapesAllBy proofSizedFull.request (baseAt numsF P5J.At.links P5J.At.ps) (fun _ => []) sentW (fun _ => 0)
    (numsF.msgsAt (some ⟨1, some (2 * g + 1), 3, .K5⟩)) (2 * g + 1) VerifiableInference.Desc.K13.Law.MFull

theorem seatsAllW_eq (E : pseatsW = P5T.psFull) (g : ℕ) : seatsAllW g = seatsAllF g := by
  have e : seatsAtW g = seatsAtF g := by
    funext L
    unfold seatsAtW seatsAtF numsW numsF
    rw [E]
  unfold seatsAllW seatsAllF
  rw [laidW_is, e] <;> rfl

theorem shapesAllW_eq (E : pseatsW = P5T.psFull) (g : ℕ) : shapesAllW g = shapesAllF g := by
  unfold shapesAllW shapesAllF numsW numsF
  rw [msgsW_is, E]

end H2K5.Door

#print axioms H2K5.Door.laidW_is
#print axioms H2K5.Door.msgsW_is
#print axioms H2K5.Door.seatsAllW_eq
#print axioms H2K5.Door.shapesAllW_eq
