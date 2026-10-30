-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/LayoutRead/GroupsAre.lean: THE GROUPS OF THE WRITTEN VALUE LW (Values/All.lean) ARE
THE TYPED LIST H2K.Sizes.groupsFull (Johnson/Desc/K12/Law/Sizes/GroupsFull.lean): 99 lines, compared
by Lean's kernel. A plain file: it imports nothing that wants a larger stack.

  **`groups_are`** : LW.groups = H2K.Sizes.groupsFull. `groups_no`: without LW's last group: no.
Limits. An equation between two written values. That the layout file's reader returns LW: Full.lean.
Nothing on soundness.

-/
import Johnson.AtFull.LayoutRead.Values.All
import Johnson.Desc.K12.Law.Sizes.GroupsFull

set_option autoImplicit false

namespace Johnson.AtFull.LayoutRead

/-- **The written value's groups are the typed list.** -/
theorem groups_are : LW.groups = H2K.Sizes.groupsFull := by decide +kernel

/-- A control: without the last group the comparison says no. -/
theorem groups_no : decide (LW.groups.dropLast = H2K.Sizes.groupsFull) = false := by decide +kernel

end Johnson.AtFull.LayoutRead

#print axioms Johnson.AtFull.LayoutRead.groups_are
#print axioms Johnson.AtFull.LayoutRead.groups_no
