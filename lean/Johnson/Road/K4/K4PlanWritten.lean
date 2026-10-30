-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanWritten.lean: K4's TESTS ON PUBLIC DATA AS CLOSED FACTS ON WRITTEN VALUES,
DECIDED BY LEAN's KERNEL. The tests of Johnson/Road/K4/K4PlanFast.lean that read
nothing but the first chain's codes, the request's shape and layout and the plan's seats are asked
at the written values that another file's pin compares whole: `proofSizedFull.codes`,
`proofSizedFull.request` (Johnson/Desc/Ok/PlanWritten/SizedLit.lean), `Johnson.G.layoutFull`
(Johnson/G/LayoutLit.lean), and at the closed plan's seats `P5T.psFull`,
`P5T.seatsAllFull`, `P5T.N0Full` (Johnson/P5T/PlanSeatsFull.lean). Four definitions and eleven
theorems, each theorem by `decide +kernel`.

  `numW`, `arrW`, `listsW`, `lastW`: the numbering over all three chains' written seats; the
    members' lists by the make at the radii 0; the number of the request's groups.
  `seamClosed_written_1`, `seamClosed_written_all`: `seamClosedB` accepts at the first seam; at all
    eleven.
  `lengths_written`, `shape_written`, `layout_written`: the programs' three tests accept.
  `last_written`: the request has 26 groups. `counts_written`: the written first list has 82
    sendings; they yield 167 members: so that a yes over them says something.
  `groups_written`: `groupsAreMembers` accepts.
  NEGATIVE TESTS: `layout_written_no` (the first segment's arrays left out) · `groups_written_no`
    (the first sending left out): each rejects. `seamClosed_written_no` (no segment sends
    anything) rejects too, but is no control: it cannot fail, since every group is then empty.

Limits. K04_law IS NOT PROVED BY THIS. CLOSED FACTS, OUTSIDE THE VERIFIER. THAT THE VERIFIER's OWN
VALUES ARE THE WRITTEN ONES is another file's pin and its laws: not called here: no theorem of this
file names Z. `shapesTiedB`, the heaviest of the common tests, is not here. The twelve tests at the
groups read the public parameters X besides: not here.
-/
import Johnson.Road.K4.K4PlanFast
import Johnson.Road.K4.SeamArrInScope
import Johnson.P5T.PlanSeatsFull
import Johnson.G.LayoutLit
import Johnson.Desc.Ok.PlanWritten.SizedLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Desc (MemberLists)
open VerifiableInference.Desc.First (groupsAreMembers)
open VerifiableInference.Desc.Sound (msOf)
open Johnson.G (layoutFull)

/-- The witness's number of (link, message), over all three chains' written seats. -/
def numW : ℕ → ℕ → ℕ := P5T.numOfPlan P5T.seatsAllFull

/-- The witness's number at a (tree, tenant), over the same list. -/
def arrW : ℕ → ℕ → ℕ := P5T.arrOf P5T.seatsAllFull

/-- The members' lists by the make off the written seats, at the radii 0: one entry a sending of the
written first list of sendings. -/
def listsW : MemberLists :=
  P5T.memberListsR Johnson.G.proofSendsFull.1.sends.length (fun _ _ => 0) P5T.psFull

/-- The number of the written request's groups. -/
def lastW : ℕ := (OnBytes.reqGroups proofSizedFull.request).toList.length

/-! ## The seams -/

theorem seamClosed_written_1 : seamClosedB layoutFull numW arrW P5T.N0Full 1 = true := by
  decide +kernel

/-- **At the written values the test accepts at all eleven seams.** -/
theorem seamClosed_written_all :
    ((List.range 11).all fun i => seamClosedB layoutFull numW arrW P5T.N0Full (i + 1)) = true := by
  decide +kernel

/-- A closed fact, no control: it cannot fail. Where no segment sends anything every group is empty,
and the test asks for just one tenant in a group. -/
theorem seamClosed_written_no :
    seamClosedB layoutFull numW arrW { P5T.N0Full with sent := fun _ _ => [] } 1 = false := by
  decide +kernel

/-! ## The common tests, lightest first -/

theorem lengths_written : proofSizedFull.codes.lengthsOk = true := by decide +kernel

theorem shape_written : OnBytes.reqShapeOk proofSizedFull.request = true := by decide +kernel

theorem last_written : lastW = 26 := by decide +kernel

theorem counts_written :
    (Johnson.G.proofSendsFull.1.sends.length, (msOf listsW).length) = (82, 167) := by
  decide +kernel

/-- **Every seat of every group, the index masks' and W's is a member's.** -/
theorem groups_written : groupsAreMembers P5T.N0Full lastW listsW = true := by decide +kernel

/-- A negative test: without the first sending it rejects. -/
theorem groups_written_no : groupsAreMembers P5T.N0Full lastW (listsW.drop 1) = false := by
  decide +kernel

/-- **The programs' own test on the layout accepts the written layout.** -/
theorem layout_written :
    OnBytes.reqLayoutOk proofSizedFull.codes proofSizedFull.request layoutFull = true := by
  decide +kernel

/-- A negative test: with the first segment's arrays left out it rejects. -/
theorem layout_written_no :
    OnBytes.reqLayoutOk proofSizedFull.codes proofSizedFull.request ⟨layoutFull.link.drop 1⟩ =
      false := by
  decide +kernel

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.seamClosed_written_1
#print axioms OnBytes.Road.K4.seamClosed_written_all
#print axioms OnBytes.Road.K4.seamClosed_written_no
#print axioms OnBytes.Road.K4.lengths_written
#print axioms OnBytes.Road.K4.shape_written
#print axioms OnBytes.Road.K4.last_written
#print axioms OnBytes.Road.K4.counts_written
#print axioms OnBytes.Road.K4.groups_written
#print axioms OnBytes.Road.K4.groups_written_no
#print axioms OnBytes.Road.K4.layout_written
#print axioms OnBytes.Road.K4.layout_written_no
