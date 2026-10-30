-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/TestTableFew.lean.
A test file for OnBytes/Model/Fit/TableFew.lean and OnBytes/K/Oracle/SeedsRoomAll.lean: a run of the
verifier's own routine planned (OnBytes/Model/Verify.lean) at the library's two written example
configurations (OnBytes/Tie/Pv/Plan/PlanKits.lean; PlanLayoutFull.lean and PlanLayoutSmall.lean in
the same folder). A #guard is a run while the file compiles, no theorem.

Why. planned_table and seedsRoom speak of every plan that the planner returns. Where it refuses they
hold for nothing, and where the line record is 0 the shape has 0 answers. The two runs show that at
these configurations the planner returns and the table has a record (one answer for each row).

Tested, at each of the two: planned returns; four numbers of the stored tables' shape: the answers
for each row; the coordinates of the record's point; the logarithm of the code's length; 24 times
answers times (coordinates + 1), the number that seedsRoom bounds. Full size: 1, 29, 32, 720. Small:
1, 19, 23, 480. The first two stand under planned_table's bounds (4 and 32), the fourth under
seedsRoom's (2^31). The third stands under neither theorem; the parameter file's reader admits at
most 32. That the written full-size values are those of Johnson/G/KitFull.lean is tested in
Johnson/G/TableFewGuard.lean.

A green run does not show anything at another configuration. This file does not compare the written
configurations with the files of the repository.

-/
import OnBytes.Model.Fit.TableFew
import OnBytes.Tie.Pv.Plan.PlanKits
import OnBytes.Tie.Pv.Plan.PlanLayoutFull
import OnBytes.Tie.Pv.Plan.PlanLayoutSmall

set_option autoImplicit false

namespace OnBytes.Model.Verify.TestTableFew

open OnBytes.Tie.Pv.Plan

/-- Four numbers of a plan's shape of tables: the answers, the coordinates of the record's point,
the logarithm of the code's length, and the bytes that the record's seeds take. -/
def four (p : Planned) : Nat × Nat × Nat × Nat :=
  let s := p.chains.tableShape
  (s.answers, s.cubeBits, s.code.logN, 24 * (s.answers * (s.cubeBits + 1)))

#guard ((planned (textOf policyF) (wordsFile scalesF) (some layoutF.toUTF8)).toOption.map four) ==
  some (1, 29, 32, 720)

#guard ((planned (textOf policyS) (wordsFile scalesS) (some layoutS.toUTF8)).toOption.map four) ==
  some (1, 19, 23, 480)

end OnBytes.Model.Verify.TestTableFew
