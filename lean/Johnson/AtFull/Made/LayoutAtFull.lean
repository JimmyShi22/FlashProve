-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/LayoutAtFull.lean: the written layout of a request's arrays at the full size
passes the test under which it is read back as it was spelled.

The layout is `layoutFull` (Johnson/G/LayoutLit.lean): 25 links with four distinct lists of arrays.
The test is `layoutB` (Johnson/AtFull/Made/ItemTests.lean). Closed facts, by Lean's kernel (`decide
+kernel`): one for each of the four lists, and from these the whole. The test reads numbers and
names: no byte of a spelling is laid.

Limits. That the written layout is the one that the planner is handed is not said here: by its own
file's head it was printed from a layout as read back. Nothing on soundness.
-/
import Johnson.AtFull.Made.ItemTests
import Johnson.G.LayoutLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open Johnson.G (layoutFirst layoutAtt layoutLay layoutHead layoutFull)

set_option maxRecDepth 1000000 in
theorem arraysB_first : arraysB layoutFirst = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem arraysB_att : arraysB layoutAtt = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem arraysB_lay : arraysB layoutLay = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem arraysB_head : arraysB layoutHead = true := by decide +kernel

theorem layoutB_full : layoutB layoutFull = true := by
  simp only [layoutB, layoutFull, List.all_cons, List.all_nil, arraysB_first, arraysB_att,
    arraysB_lay, arraysB_head, Bool.and_true, Bool.and_self]
  decide

/-- Negative tests: a name with a line feed; a block's number of 2 ^ 64. -/
theorem layoutB_rejects :
    (layoutB ⟨[[⟨"a\nb", 0, 1, 1, []⟩]]⟩,
      layoutB ⟨[[⟨"a", 0, 1, 1, [⟨2 ^ 64, 0, 0, 0, 0, 0, 0, 0, false⟩]⟩]]⟩) = (false, false) := by
  decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.arraysB_first
#print axioms Johnson.AtFull.Made.arraysB_att
#print axioms Johnson.AtFull.Made.arraysB_lay
#print axioms Johnson.AtFull.Made.arraysB_head
#print axioms Johnson.AtFull.Made.layoutB_full
#print axioms Johnson.AtFull.Made.layoutB_rejects
