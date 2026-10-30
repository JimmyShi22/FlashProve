-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/RowsAtBlocks.lean: WHERE THE TWO CLASSES OF ROWS THAT A SWITCH LAYS STAND, AT
THE TABLE's NUMBERS CLOSED OVER THE SUB-PROTOCOLS (`Numbers.atBlocks`,
Johnson/Desc/First/NumbersAtBlocks.lean), written out at a group that is not the first. Two
theorems. A file beside the table: it turns nothing of it.
Why. The switch's terms that end in `IM.Hands` take as debts what `Numbers.rowsAt m` is at the
classes "carried" and "position". At the numbers that count the field is `rowsAtPlan`
(Johnson/Desc/First/RowsAtPlan.lean), behind two layers of definitions and a case on "m == 0".
Here it is written out once, in the table's own terms: whoever pays the debts then has two plain
equations on numbers left.
  `atBlocks_carried`: from place 0: the carried claim and one row for each kept copy of the group
  in front.
  `atBlocks_position`: behind these: `positionRows` at the positions that the switch's own
  declared rounds sample.
Limits. By unfolding: nothing on what a switch's accepting lays. At the first group (m = 0) both
classes are empty: not said here. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.NumbersAtBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc OnBytes OnBytes.Model

variable {St Cl : Type} (N : Numbers) (s : Params.ReqShape) (links : List ModelPart)
  (bs : List (Block St Cl)) {m : Nat}

/-- The class "carried", at a group that is not the first. -/
theorem atBlocks_carried (hm : m ≠ 0) :
    (N.atBlocks s links bs).rowsAt m .carried = (0, 1 + (N.keptOf (m - 1)).length) := by
  rw [atBlocks_rowsAt]
  show (0, carriedRows N m) = _
  unfold carriedRows
  rw [if_neg (by simpa using hm)]

/-- The class "position", at a group that is not the first. -/
theorem atBlocks_position (hm : m ≠ 0) :
    (N.atBlocks s links bs).rowsAt m .position =
      (1 + (N.keptOf (m - 1)).length, positionRows s (possAt bs links.length m) m) := by
  rw [atBlocks_rowsAt]
  show (carriedRows N m, if m == 0 then 0 else positionRows s (possAt bs links.length m) m) = _
  unfold carriedRows
  rw [if_neg (by simpa using hm), if_neg (by simpa using hm)]

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.atBlocks_carried
#print axioms VerifiableInference.Desc.First.atBlocks_position
