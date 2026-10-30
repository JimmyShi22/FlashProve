-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/ToldBentBases.lean: WHAT THE CONTROLS ON THE WRITTEN TABLE BEND, HELD BY
LEAN. Each control in ToldAtA, ToldAtB, ToldAtC and ToldAtBTurned says that the run is not a bent
table, and the bent table's turned part is typed by hand. A slip in another field of that part would
make the control true for the wrong reason. Here, for each control but one, the same right side with
the one bent thing put back is shown to be the written table itself
(Johnson/HB/LLHARD/KB4/Told.lean). So a control's right side parts from the table in what its name
says, and in nothing else: to be seen by holding the two statements side by side.
  `base_A_group`, `base_B_group`, `base_C_group`: the first tree with its group as written.
  `base_B_order`: trees number 1 and 2 in the written order.
  `base_B_turned_one`, `base_B_turned_two`: the tenant's list of groups in the written order.
`told_A_bent_order` has no typed part (its right side is the written list reversed): `base_A_order`
says that this list is not its own reverse.
Limits. Closed facts on one written table. Nothing on what any routine returns.
Nothing on soundness, nothing on hiding.

-/
import Johnson.HB.LLHARD.KB4.Told

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack


theorem base_A_group :
    ⟨13, 3, [⟨0, 3, 1, true, [300]⟩]⟩ :: Johnson.KB4.told1.tail = Johnson.KB4.told1 := by
  decide +kernel

theorem base_A_order : ¬ Johnson.KB4.told1.reverse = Johnson.KB4.told1 := by decide +kernel

theorem base_B_group :
    ⟨24, 324, [⟨321, 0, 3, true, [200]⟩, ⟨0, 3, 1, false, []⟩]⟩ :: Johnson.KB4.told2.tail =
      Johnson.KB4.told2 := by
  decide +kernel

theorem base_B_order :
    Johnson.KB4.told2.take 1 ++ [⟨22, 36, [⟨36, 0, 3, true, [250, 300]⟩]⟩,
        ⟨13, 3, [⟨0, 3, 1, true, [250, 200]⟩]⟩] ++ Johnson.KB4.told2.drop 3 =
      Johnson.KB4.told2 := by
  decide +kernel

theorem base_B_turned_one :
    Johnson.KB4.told2.take 1 ++ [⟨22, 36, [⟨36, 0, 3, true, [250, 300]⟩]⟩] ++
        Johnson.KB4.told2.drop 2 = Johnson.KB4.told2 := by
  decide +kernel

theorem base_B_turned_two :
    Johnson.KB4.told2.take 2 ++ [⟨13, 3, [⟨0, 3, 1, true, [250, 200]⟩]⟩] ++
        Johnson.KB4.told2.drop 3 = Johnson.KB4.told2 := by
  decide +kernel

theorem base_C_group :
    ⟨18, 96, [⟨48, 24, 3, true, [301]⟩, ⟨0, 24, 1, false, []⟩]⟩ :: Johnson.KB4.told3.tail =
      Johnson.KB4.told3 := by
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.base_A_group
#print axioms Johnson.AtFull.KeyBack.base_A_order
#print axioms Johnson.AtFull.KeyBack.base_B_group
#print axioms Johnson.AtFull.KeyBack.base_B_order
#print axioms Johnson.AtFull.KeyBack.base_B_turned_one
#print axioms Johnson.AtFull.KeyBack.base_B_turned_two
#print axioms Johnson.AtFull.KeyBack.base_C_group
