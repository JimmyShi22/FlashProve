-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/LayoutRead/Values/All.lean: THE STORED FULL-SIZE LAYOUT FILE AS THE LAYOUT FILE's
READER IS TO RETURN IT: the fourteen pieces' written values (V01.lean to V14.lean) in a row: 99
groups, 5,419 blocks, in the file's order. Two definitions, one theorem.

  `values`: the fourteen. `LW`: their groups in a row, their blocks in a row.
  `LW_counts`: 99 and 5,419, by Lean's kernel.
Limits. THAT THE READER RETURNS LW AT THE FILE IS SAID IN lean/AtFullSide/LayoutRead/Full.lean, NOT
HERE.

-/
import Johnson.AtFull.LayoutRead.Values.V01
import Johnson.AtFull.LayoutRead.Values.V02
import Johnson.AtFull.LayoutRead.Values.V03
import Johnson.AtFull.LayoutRead.Values.V04
import Johnson.AtFull.LayoutRead.Values.V05
import Johnson.AtFull.LayoutRead.Values.V06
import Johnson.AtFull.LayoutRead.Values.V07
import Johnson.AtFull.LayoutRead.Values.V08
import Johnson.AtFull.LayoutRead.Values.V09
import Johnson.AtFull.LayoutRead.Values.V10
import Johnson.AtFull.LayoutRead.Values.V11
import Johnson.AtFull.LayoutRead.Values.V12
import Johnson.AtFull.LayoutRead.Values.V13
import Johnson.AtFull.LayoutRead.Values.V14

set_option autoImplicit false

namespace Johnson.AtFull.LayoutRead
open OnBytes.Plan

/-- The fourteen values. -/
def values : List LayoutLines :=
  [v01, v02, v03, v04, v05, v06, v07,
   v08, v09, v10, v11, v12, v13, v14]

/-- **The full-size layout file as the reader is to return it**: the values in a row. -/
def LW : LayoutLines := ⟨values.flatMap (·.groups), values.flatMap (·.blocks)⟩

/-- Its two lengths. -/
theorem LW_counts : LW.groups.length = 99 ∧ LW.blocks.length = 5419 := by decide +kernel

end Johnson.AtFull.LayoutRead

#print axioms Johnson.AtFull.LayoutRead.LW_counts
