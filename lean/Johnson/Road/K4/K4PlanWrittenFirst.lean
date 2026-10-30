-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanWrittenFirst.lean: THE TWELVE TESTS AT K4's GROUPS AS ONE CLOSED FACT ON
WRITTEN VALUES, DECIDED BY LEAN's KERNEL. `firstClosedCoreB` (Johnson/Road/K4/K4PlanNine.lean) reads
the first chain's codes, the request's shape and layout, the plan's seats, and eighteen numerals
with a rule; nothing of the public parameters X, no built link. Here it is asked at the written
values of Johnson/Road/K4/K4PlanWritten.lean and K4PlanWrittenShapes.lean, at all twelve groups. One
definition and four theorems, each theorem by `decide +kernel`.

  `sentW`: what the lookup's caller reads, at the written values; its list of the built links'
    arrays is empty: the test does not read it.
  `asked_written`: how much the yes asks: the caller's list has 3 members at the first group and 4
    at each of the eleven others.
  `first_written`: the test accepts at all twelve groups.
  NEGATIVE TESTS: `first_written_no` (the numbering read a tenant further) · `first_written_no'`
    (the first sending's members left out): each rejects at the first group.

Limits. K04_law IS NOT PROVED BY THIS. A CLOSED FACT, OUTSIDE THE VERIFIER. No theorem of this file
names Z or X. The reference sizes alone.
-/
import Johnson.Road.K4.K4PlanNine
import Johnson.Road.K4.K4PlanWrittenShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Desc.First.Look (Sent sigListCalls)
open VerifiableInference.Desc.Sound (msOf)
open Johnson.G (layoutFull)

/-- What the lookup's caller reads, at the written values. -/
def sentW : Sent := ⟨proofSizedFull.codes, proofSizedFull.request, layoutFull, #[]⟩

/-- How much the yes asks: the members of the caller's list, a group. -/
theorem asked_written :
    ((List.range 12).map fun g => (sigListCalls sentW (fun _ => 0) (2 * g)).length) =
      [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] := by
  decide +kernel

/-- **At the written values the test at a group accepts, at all twelve.** -/
theorem first_written :
    ((List.range 12).all fun g =>
      firstClosedCoreB sentW P5T.psFull P5T.N0Full (msOf listsW) g
        (fun l k => keysW.idxOf (0, l, k))
        (fun j t => (tabW.lookup (j, t)).getD keysW.length)) = true := by
  decide +kernel

/-- A negative test: with the numbering read a tenant further it rejects. -/
theorem first_written_no :
    firstClosedCoreB sentW P5T.psFull P5T.N0Full (msOf listsW) 0
      (fun l k => keysW.idxOf (0, l, k))
      (fun j t => (tabW.lookup (j, t + 1)).getD keysW.length) = false := by
  decide +kernel

/-- A negative test: without the first sending's members it rejects. -/
theorem first_written_no' :
    firstClosedCoreB sentW P5T.psFull P5T.N0Full (msOf (listsW.drop 1)) 0
      (fun l k => keysW.idxOf (0, l, k))
      (fun j t => (tabW.lookup (j, t)).getD keysW.length) = false := by
  decide +kernel

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.asked_written
#print axioms OnBytes.Road.K4.first_written
#print axioms OnBytes.Road.K4.first_written_no
#print axioms OnBytes.Road.K4.first_written_no'
