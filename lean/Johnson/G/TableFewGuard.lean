-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/TableFewGuard.lean: four numbers of the planner's shape of the stored tables, by
evaluation at the full-size example; and the library's typed copies of that example's three public
files, held against each other.

Two tests.
 1. At the plan that `OnBytes.Model.Verify.planned` returns: the stored tables' shape has one answer
    for each row, so the table has a record; the record's point has 29 coordinates; the code has
    2^32 positions; 24 times answers times (coordinates + 1) is 720. So `planned_table`
    (OnBytes/Model/Fit/TableFew.lean) and `seedsRoom` (OnBytes/K/Oracle/SeedsRoomAll.lean) are not
    idle there: the planner returns, and the table has a record.
 2. The library holds that example's three public files as typed values more than once. Byte for
    byte: `KitFull.policy` is `textOf policyF` (OnBytes/Tie/Pv/Plan/PlanKits.lean) and
    `OnBytes.K.Oracle.fullPolicy` (OnBytes/K/Oracle/SaysLinesFull.lean); `KitFull.layout` is
    `layoutF` (PlanLayoutFull.lean); `KitFull.scales` is `wordsFile scalesF` (PlanKits.lean).
Whence: Lean's evaluator, at the three shipped public files of prover/examples/target_full_f2, as
Johnson/G/KitFull.lean holds them. No other file is read. The first test's like at the library's two
written example configurations: OnBytes/Model/Fit/TestTableFew.lean.
Limits: evidence by evaluation at one example; no theorem. That any of the typed values is a file of
the repository is not tested here.

-/
import Johnson.G.KitFull
import OnBytes.K.Oracle.SaysLinesFull
import OnBytes.Model.Fit.TestTableFew

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes.Model.Verify OnBytes.Tie.Pv.Plan

#guard ((planned KitFull.policy.toUTF8 KitFull.scales (some KitFull.layout.toUTF8)).toOption.map
  TestTableFew.four) == some (1, 29, 32, 720)

#guard KitFull.policy.toUTF8 == textOf policyF &&
  KitFull.policy.toUTF8 == OnBytes.K.Oracle.fullPolicy &&
  KitFull.layout.toUTF8 == layoutF.toUTF8 && KitFull.scales == wordsFile scalesF

end Johnson.G
