-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/RowsAtLink.lean: THE ROWS OF THE ROUND THAT BATCHES A SEGMENT's CLAIMS, AT THE FULL
SIZE, AS WRITTEN NUMBERS BY THE SEGMENT's NUMBER. One definition with code, this file's own. NOTHING
IS PROVED IN THIS FILE. It imports nothing.

  `rowsAtLink l`   24,653,737 at 24 (the output head's segment); 14,166,783 at an odd l (attention);
                   32,005,923 at 0; 32,005,793 at the other even l (layers)

WHAT IT IS NOT. Data. That a plan or a declared round has these rows is said elsewhere:
Johnson/P1K8R/K9RowsByLink.lean (the declared rounds), Johnson/P1K8R/PlanRowsAtHead.lean (the
plans). Beyond 24 the number means nothing.

NEAR. `full_rows` (Johnson/Desc/First/Batch/Law/Condition.lean) has the 25 numbers as a list;
`closeAt` (OnBytes/Tie/Pv/Plan/PlanSizes.lean) as a table by segment.
-/

namespace P1K8

/-- **The written numbers, by the segment's number.** This file's own. -/
def rowsAtLink (l : Nat) : Nat :=
  if l = 24 then 24653737 else if l % 2 = 1 then 14166783 else if l = 0 then 32005923 else 32005793

end P1K8

#print axioms P1K8.rowsAtLink
