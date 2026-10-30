-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/RadOneWritten.lean: IN THE WRITTEN RADII OF THE FIRST PROOF CHAIN ONE SHAPE HAS
ONE RADIUS: the second half of the named condition `rowsRead` (Johnson/Goal/Skeleton/RowsRead.lean),
at the written list. A closed fact with its negative test, and two steps on lists.

  `radOne_written`: `P5T.radOneB` (Johnson/P5J/Rad3Seat3At.lean) accepts at `radsFull.flatten`
    (Johnson/HB/LLHARD/RadiiWritten.lean): 167 pairs of a shape and a radius. By an evaluation in
    Lean's kernel (`decide +kernel`).
  `radOne_rejects`: the negative test: with the first pair laid in front once more, its radius one
    higher, the test rejects.
  `radOne_of_radii`: so, at whatever rows R whose first proof chain's column of sampled shapes is
    the written list, the test accepts at what `rowsReadB` hands it.
  `rowsRead_of_radii`: so `rowsRead Z`, where the maker of the rows returns R at Z's three public
    files and R's column is the written list.

Limits. That the maker returns, and that its column is the written list, are premises here: the
second is `radii_in_scope`. Nothing on what a radius means. Nothing on soundness.

-/
import Johnson.HB.LLHARD.RadiiWritten
import Johnson.Goal.Skeleton.RowsRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open Johnson.G (radsFull SendRow)

set_option maxRecDepth 1000000 in
/-- **In the written radii one shape has one radius.** -/
theorem radOne_written : radOneB radsFull.flatten = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: the first pair once more, its radius one higher. -/
theorem radOne_rejects :
    radOneB ((radsFull.flatten.head?.map fun a => (a.1, a.2 + 1)).toList ++ radsFull.flatten) =
      false := by decide +kernel

/-- At rows whose column is the written list. -/
theorem radOne_of_radii {R : List SendRow} (h : (firstRows R).map (·.sampled) = radsFull) :
    radOneB ((firstRows R).flatMap (·.sampled)) = true := by
  rw [List.flatMap_def, h]
  exact radOne_written

/-- **The named condition, from a return of the maker and the written column.** -/
theorem rowsRead_of_radii {Z : VerifierAndGoals.PublicFiles} {R : List SendRow}
    (hR : Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R)
    (h : (firstRows R).map (·.sampled) = radsFull) : P5J.rowsRead Z :=
  P5J.rowsRead_iff.2 ⟨R, hR, radOne_of_radii h⟩

end P5T

#print axioms P5T.radOne_written
#print axioms P5T.radOne_rejects
#print axioms P5T.radOne_of_radii
#print axioms P5T.rowsRead_of_radii
