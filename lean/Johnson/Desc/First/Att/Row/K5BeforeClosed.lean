-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5BeforeClosed.lean: kind K5's row: ONE CLOSED FACT, BY LEAN's KERNEL: at
the written table of the first chain's stretches (Johnson.AtFull.Cut.cutWritten,
Johnson/AtFull/Cut/CutWrittenLit.lean) and the written roots (P5T.seedRoots,
Johnson/P5T/PlanSeatsFull.lean) the lot's "before" in its form by fields (beforeBy,
Johnson/Desc/First/Att/Row/K5RowTwins.lean) is [(1, 4 + 6 g)] at each of the twelve attention
segments: the column of the written cut (Johnson/Desc/Ok/PlanWritten/CutLit.lean). ONE DECISION,
ALONE IN ITS MODULE. Its negative twin: Johnson/Desc/First/Att/Row/K5BeforeClosedNo.lean.
IT SPEAKS OF WRITTEN VALUES: that these are the planner's at any public files is not said here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5RowTwins
import Johnson.AtFull.Cut.CutWrittenLit
import Johnson.P5T.PlanSeatsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row

/-- The written table's pairs (look, take). -/
def cutPairsW : List (String × ℕ) := Johnson.AtFull.Cut.cutWritten.map fun c => (c.look, c.take)

/-- The test: "before" at the twelve, off the written values. -/
def beforeAllB (want : ℕ → List (ℕ × ℕ)) : Bool :=
  (List.range 12).all fun g => decide (beforeBy cutPairsW (P5T.sumBelow P5T.seedRoots) ("A" ++ toString g) = some (want g))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **"before" AT THE TWELVE, AT THE WRITTEN VALUES.** -/
theorem before_closed : beforeAllB (fun g => [(1, 4 + 6 * g)]) = true := by decide +kernel

end H2K5.Row

#print axioms H2K5.Row.before_closed
