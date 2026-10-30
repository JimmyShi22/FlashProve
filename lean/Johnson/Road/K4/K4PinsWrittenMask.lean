-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsWrittenMask.lean: K4's TESTS ON THE SEGMENT's MASK ROW AS CLOSED FACTS ON
WRITTEN VALUES, DECIDED BY LEAN's KERNEL: `maskEllP`, `maskPlanB`
(Johnson/Road/K4/Rec/PinsBools.lean), each at all twelve groups, at the plan without radii and cells
(`pin0`,
Johnson/Road/K4/K4PinsAnyRad.lean). Three definitions and five theorems, each theorem by
`decide +kernel`.

  `seatW l j`: the seat of member j of link l's caller's list, off the written seats.
  `recW L`: the plan's letters (`RecPlan`, Johnson/Road/K4/Rec/Whole.lean) at the written values;
    the two parts that the tests do not read (the lists of names; the ledgers' looks) are empty.
  `ownSentW g`: what segment 2 g sends at its first moment.
  `ell_written`: the plan's length of the mask row is 8192 at each group · NEGATIVE:
    `ell_written_no` (at a number that is no link's it is 0).
  `maskPlan_written` · NEGATIVE, AT GROUP 0 ALONE: `maskPlan_written_no` (the next segment's
  tenants) ·
    `maskPlan_written_no'` (the seats read a tenant further).

Limits. K04_law IS NOT PROVED BY THIS. CLOSED FACTS, OUTSIDE THE VERIFIER: no theorem of this file
names the public parameters Z: the carrying stands in Johnson/Road/K4/K4PinsPaid.lean. The written
values rest on prints of Lean's evaluator (their files' heads). The full size alone.
-/
import Johnson.Road.K4.K4PinsBook
import Johnson.Road.K4.K4PinsSends
import Johnson.Road.K4.K4PinsAnyRad
import Johnson.Road.K4.K4PlanWrittenFirst
import Johnson.Desc.First.SentTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Desc.First (flatPlacesOf)
open VerifiableInference.Desc.First.FillSent (sentDataOf baseAt)
open VerifiableInference.Desc.Sound (linksFull)
open OnBytes.Road.K4.Rec (RecPlan maskPlanB maskEllP)
open Johnson.G (layoutFull)

/-- the table's own list of places -/
local notation "𝐩𝐬" => (flatPlacesOf linksFull true)

/-- The seat of member j of link l's caller's list, off the written seats. -/
def seatW (l j : ℕ) : ℕ × ℕ := P6T.seatCallsT P5T.psFull sentW l j

/-- The plan's letters at the written values. -/
def recW (L : VerifiableInference.Desc.K12.Door.Laid) : RecPlan :=
  ⟨proofSizedFull.codes, proofSizedFull.request, layoutFull, fun _ => #[], L, mW,
    sentDataOf proofSizedFull.request (baseAt nW linksFull 𝐩𝐬) fun _ => []⟩

/-- What segment 2 g sends at its first moment. -/
def ownSentW (g : ℕ) : List (ℕ × ℕ) := nW.sent (2 * g) 0

/-! ## The mask row -/

set_option maxRecDepth 1000000 in
/-- The plan's length of the mask row, a group. -/
theorem ell_written :
    ((List.range 12).all fun g => maskEllP (pin0 sentW (seatW (2 * g)) (2 * g)) == 8192) =
      true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: at a number that is no link's the length is 0. -/
theorem ell_written_no : maskEllP (pin0 sentW (seatW 25) 25) = 0 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **At the written values the test on the mask row accepts at all twelve groups.** -/
theorem maskPlan_written :
    (laidW?.any fun L => (List.range 12).all fun g =>
      maskPlanB (pin0 sentW (seatW (2 * g)) (2 * g)) (ownSentW g) (recW L)
        (nW.msgsAt 𝐩𝐬[28 * g + 4]?) (2 * g)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the next segment's tenants. -/
theorem maskPlan_written_no :
    (laidW?.any fun L =>
      maskPlanB (pin0 sentW (seatW 0) 0) (nW.sent 1 0) (recW L) (nW.msgsAt 𝐩𝐬[4]?) 0) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the seats read a tenant further. -/
theorem maskPlan_written_no' :
    (laidW?.any fun L =>
      maskPlanB (pin0 sentW (fun j => ((seatW 0 j).1, (seatW 0 j).2 + 1)) 0) (ownSentW 0) (recW L)
        (nW.msgsAt 𝐩𝐬[4]?) 0) = false := by
  decide +kernel

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ell_written
#print axioms OnBytes.Road.K4.ell_written_no
#print axioms OnBytes.Road.K4.maskPlan_written
#print axioms OnBytes.Road.K4.maskPlan_written_no
#print axioms OnBytes.Road.K4.maskPlan_written_no'
