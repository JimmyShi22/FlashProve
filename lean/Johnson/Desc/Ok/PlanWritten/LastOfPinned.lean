-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/LastOfPinned.lean: under a yes of the test on the planner's sizes of a
proof file (`sizedPinnedAt`, Johnson/Desc/Ok/PlanWritten/SizedTest.lean), the stages of the first
chain's last proximity test are the typed list `szLFull`
(Johnson/Desc/K12/Law/Sizes/StagesFull.lean).

Why. Laws on that test stand under a premise on the layout file: its group lines, as read, are a
typed list (`LayoutGroupsAre`, Johnson/Desc/K12/Law/Sizes/LastAtScope.lean). That premise is proved
in the side library (AtFullSide/LayoutRead/GroupsPaid.lean). What these laws conclude from it is an
equation on one field of the planner's sizes. The test on the planner's sizes holds all fields
against the written value (`proofSizedFull`, Johnson/Desc/Ok/PlanWritten/SizedLit.lean), so under
its yes the equation follows from a closed fact on two written values, and the layout file is not
named.

The statement is a tool: no description of the protocol is named.

  `last_of_pinnedAt`: from a yes of `sizedPinnedAt P made`, where the scan P has the full size's
    key: by `sized_of_pinnedAt` (Johnson/Desc/Ok/PlanWritten/SizedTestLaws.lean) and the closed fact
    `last_written` (Johnson/Desc/K12/Law/Sizes/WrittenIsTyped.lean).

What of OnBytes/Model/ is used: `PolScan`, by name.

Limits. That the test says yes at any public files is no theorem: it is asked at the run. That P and
made are of the same files is the caller's. Nothing is said of the layout file or of its group
lines. At a key other than the full size's nothing follows. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.SizedTestLaws
import Johnson.Desc.K12.Law.Sizes.WrittenIsTyped

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open OnBytes.Params

/-- **Under a yes of the test on the planner's sizes, at the full size's key**: the stages of the
first chain's last proximity test are the typed list. -/
theorem last_of_pinnedAt {P : OnBytes.Model.PolScan} {made : Configured}
    (h : sizedPinnedAt P made = true) (hk : keyOfScan P = fullKey) :
    made.sized.proof.last.stages = H2K.Member.szLFull := by
  rw [sized_of_pinnedAt h hk]
  exact H2K.Sizes.last_written

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.last_of_pinnedAt
