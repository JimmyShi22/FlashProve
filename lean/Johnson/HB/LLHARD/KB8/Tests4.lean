-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB8/Tests4.lean: closed statements on the written values of Written.lean in this
folder, by evaluations in Lean's kernel: the stored table's depth; the typed numbers behind the
places' formulas; the third chain's declared rounds.

Main names.
  `depth_full`: the index tree's depth in the typed sizes is 32.
  `decl_lengths`: the written declared rounds are 18,851, 68 and 30.
  `nums_typed`: rows, work and "the first fold sends its own mask" at the four places, as numbers.
  `third_full`: the own test's numbers give the third chain's 30 written declared rounds, whole
    (`H2U.roundsOfNums`, Johnson/Desc/K12/TestEntries.lean). `four_some`: all four give rounds.
  `depth_bent`, `nums_bent`, `third_bent`, `four_bent`: with 31 for 32, with 982 rows for 981, with
    one row more at "BAT", and with one stage alone, the tests say no.
  `third_bent_tree`, `third_bent_first`: two values typed by hand are bent: the first tree's number,
    and the trees of the first opening: no.

A name that ends in `_bent`: the same test with one value changed, at which it says no: so the test
is seen to be able to fail.

Limits. Both sides are written values (Written.lean says whence). Nothing on a description's blocks
here. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB8.Written

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB8

open OnBytes OnBytes.Params
open Lk6.AtPlan (keyFull)

/-- The depth of the index tree in the typed sizes of a key of full size. -/
theorem depth_full : keyFull.once.shape.fold.index.tree.a = 32 := by decide +kernel

/-- It is not 31: the test can fail. -/
theorem depth_bent : decide (keyFull.once.shape.fold.index.tree.a = 31) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The three written lists of declared rounds have 18,851, 68 and 30 rounds. -/
theorem decl_lengths :
    (declKeyFull.1.length, declKeyFull.2.1.length, declKeyFull.2.2.length) = (18851, 68, 30) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Not 18,850: the test can fail. -/
theorem decl_lengths_bent : decide ((declKeyFull.1.length, declKeyFull.2.1.length,
    declKeyFull.2.2.length) = (18850, 68, 30)) = false := by
  decide +kernel

/-- The numbers behind the formulas: rows, work, own mask, at the four places. -/
theorem nums_typed :
    [(rNums.rows, rNums.work, rNums.ownMask), (uNums.rows, uNums.work, uNums.ownMask),
      (oNums.rows, oNums.work, oNums.ownMask), (wNums.rows, wNums.work, wNums.ownMask)] =
    [(981, 32, false), (66, 32, false), (3, 32, true), (5, 32, false)] := by decide +kernel

/-- With 982 rows for 981 on the typed side the test says no. -/
theorem nums_bent : decide (
    [(rNums.rows, rNums.work, rNums.ownMask), (uNums.rows, uNums.work, uNums.ownMask),
      (oNums.rows, oNums.work, oNums.ownMask), (wNums.rows, wNums.work, wNums.ownMask)] =
    [(982, 32, false), (66, 32, false), (3, 32, true), (5, 32, false)]) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The own test's numbers give the third chain's written declared rounds.** -/
theorem third_full : H2U.roundsOfNums wNums = some declKeyFull.2.2 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- With one row more at "BAT" they do not. -/
theorem third_bent :
    decide (H2U.roundsOfNums { wNums with rows := 6 } = some declKeyFull.2.2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- With 6 for 7 as the first tree's number, a number typed by hand, they do not. -/
theorem third_bent_tree :
    decide (H2U.roundsOfNums { wNums with firstTree := 6 } = some declKeyFull.2.2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- With the last of the three trees of the first opening left out, a list typed by hand, they do
not. -/
theorem third_bent_first : decide (H2U.roundsOfNums { wNums with first := wNums.first.dropLast } =
    some declKeyFull.2.2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- All four places' numbers give rounds. -/
theorem four_some :
    ([rNums, uNums, oNums, wNums].all fun N => (H2U.roundsOfNums N).isSome) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Numbers with one stage alone give none: the test says no. -/
theorem four_bent : ([rNums, uNums, oNums, { wNums with stages := wNums.stages.take 1 }].all
    fun N => (H2U.roundsOfNums N).isSome) = false := by
  decide +kernel

end Johnson.KB8

#print axioms Johnson.KB8.depth_full
#print axioms Johnson.KB8.depth_bent
#print axioms Johnson.KB8.decl_lengths
#print axioms Johnson.KB8.decl_lengths_bent
#print axioms Johnson.KB8.nums_typed
#print axioms Johnson.KB8.third_full
#print axioms Johnson.KB8.third_bent
#print axioms Johnson.KB8.third_bent_tree
#print axioms Johnson.KB8.third_bent_first
#print axioms Johnson.KB8.four_some
#print axioms Johnson.KB8.nums_bent
#print axioms Johnson.KB8.four_bent
