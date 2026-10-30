-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanWrittenShapes.lean: THE HEAVIEST OF K4's COMMON TESTS AS A CLOSED FACT ON
WRITTEN VALUES: AN EXPERIMENT. `shapesTiedB` (Johnson/Road/K4/LayoutTiesB.lean) asks, of
every array of every segment of the layout, every segment's group and every member, that a member
which sits in the group under the array's message's number has that message's key of shape. Here it
is asked at the written values of Johnson/Road/K4/K4PlanWritten.lean, in the very form in which
`commonFastB` (Johnson/Road/K4/K4PlanFast.lean) asks it: the keys, the table "seat ↦ number" and the
25 groups as terms of their own. Three definitions and two theorems, each theorem by `decide
+kernel`.

  `keysW`, `tabW`, `tblW`: the written seats' keys; the table; the 25 groups.
  `shapesTied_written`: the test accepts.
  `shapesTied_written_no`: A NEGATIVE TEST: at one number for all messages it rejects.

Limits. K04_law IS NOT PROVED BY THIS. AN EXPERIMENT ON WHAT THE KERNEL BEARS. No theorem of this
file names Z.
-/
import Johnson.Road.K4.K4PlanWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.Road.K4.LayoutTies (shapesTiedB)
open Johnson.G (layoutFull)

/-- The written seats' keys, each once. -/
def keysW : List (ℕ × ℕ × ℕ) := seatKeys P5T.seatsAllFull

/-- Seat ↦ the place of its key. -/
def tabW : List ((ℕ × ℕ) × ℕ) := arrTab keysW P5T.seatsAllFull

/-- The 25 segments' groups. -/
def tblW : List (List (ℕ × ℕ)) := (List.range 25).map fun k => P5T.N0Full.group k

/-- **At the written values the tie of shapes accepts.** -/
theorem shapesTied_written :
    shapesTiedB proofSizedFull.codes proofSizedFull.request layoutFull
      (fun l k => keysW.idxOf (0, l, k)) (fun j t => (tabW.lookup (j, t)).getD keysW.length) listsW
      (fun k => tblW.getD k []) = true := by
  decide +kernel

/-- A negative test: at one number for all messages it rejects. -/
theorem shapesTied_written_no :
    shapesTiedB proofSizedFull.codes proofSizedFull.request layoutFull (fun _ _ => 0)
      (fun _ _ => 0) listsW (fun k => tblW.getD k []) = false := by
  decide +kernel

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.shapesTied_written
#print axioms OnBytes.Road.K4.shapesTied_written_no
