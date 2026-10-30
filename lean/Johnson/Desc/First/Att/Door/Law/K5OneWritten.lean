-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5OneWritten.lean: THE TEST "one" (`oneV`,
Johnson/Desc/First/Att/Door/Law/K5OneView.lean) ACCEPTS AT THE WRITTEN VALUES OF THE FULL SIZE, AT
ALL 24 LINKS IN FRONT OF THE HEAD's: one decision of Lean's kernel. Its negative test stands in a
module of its own (K5OneRejects.lean [not in this library]), so that each module holds one decision.

  `oneW l`: the test at link l at the written view of the public parameters' shape
    (`xShapeFull`), what the planner sends (`sentW`), the numbers and seats off the written seats
    (`numOfPlan seatsAllFull` · `psFull` · `arrOf seatsAllFull`). No letter.
  **`one_written`**: it accepts at every l < 24: by `decide +kernel`.
  The negative test `one_rejects` (K5OneRejects.lean [not in this library]): with arr one
  higher it rejects at every
    l < 24.
Is the test idle? Its last arm says yes where the place lies beyond the calls' list. The two facts
together answer: at link l the test accepts, and rejects when arr alone is turned: arr is read in
the first arm alone: so at each of the 24 links an entry meets that arm and is compared. (No count
of such entries is taken.)
Limits. The full size alone. Closed facts on written values: that a public part has these values is
another file's. Nothing on soundness. On hiding nothing.

-/
import Johnson.Desc.First.Att.Door.Law.K5OneView
import Johnson.Desc.First.Att.Door.Law.K5WrittenPlans
import Johnson.Goal.Meaning.NamedViewFull
import Johnson.P5T.PlanSeatsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open P5T (psFull seatsAllFull)
open Johnson.G (xShapeFull)

/-- The test at link l, at the written values. -/
def oneW (l : ℕ) : Bool :=
  oneV xShapeFull sentW (P5T.numOfPlan seatsAllFull) psFull (P5T.arrOf seatsAllFull) l

set_option maxRecDepth 1000000 in
/-- **THE TEST ACCEPTS AT THE WRITTEN VALUES, AT ALL 24 LINKS.** -/
theorem one_written : (List.range 24).all oneW = true := by decide +kernel

end H2K5.Door

#print axioms H2K5.Door.one_written
