-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/LayoutRead/GroupsPaid.lean: ONE CLOSED PREMISE, PAID: `H2K.Sizes.LayoutGroupsAre`
(Johnson/Desc/K12/Law/Sizes/LastAtScope.lean): the layout file's reader returns at the stored
full-size layout file, and its group lines are the typed list `H2K.Sizes.groupsFull`
(GroupsFull.lean in that folder). One theorem: a call.
  **`layoutGroupsAre`** : H2K.Sizes.LayoutGroupsAre: by `layoutRead_full` (Full.lean) and
    `groups_are` (Johnson/AtFull/LayoutRead/GroupsAre.lean: the written value's groups are that
    typed list).
Limits. It says what the reader returns. What hangs on that premise is said where it is spent. It
lies in the side library AtFullSide, which is built with a larger thread stack, since Full.lean
does. Nothing on soundness.

-/
import AtFullSide.LayoutRead.Full
import Johnson.AtFull.LayoutRead.GroupsAre
import Johnson.Desc.K12.Law.Sizes.LastAtScope

set_option autoImplicit false

namespace Johnson.AtFull.LayoutRead

/-- **The closed premise on the layout file.** -/
theorem layoutGroupsAre : H2K.Sizes.LayoutGroupsAre := by
  unfold H2K.Sizes.LayoutGroupsAre
  rw [layoutRead_full, Option.map_some, groups_are]

end Johnson.AtFull.LayoutRead

#print axioms Johnson.AtFull.LayoutRead.layoutGroupsAre
