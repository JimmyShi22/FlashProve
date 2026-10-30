-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/FrontClosed.lean: NO HYPOTHESIS. ONE CLOSED FACT ON TWO WRITTEN
LISTS, BY LEAN's KERNEL, with a negative test. Three definitions, and two statements with their
proofs.

What is here. At each of the twelve groups of layers, the written table of the first chain's
stretches (`Johnson.AtFull.Cut.cutWritten`, Johnson/AtFull/Cut/CutWrittenLit.lean) has a step of the
name by which the honest side counts the rounds in front of the layers' own rounds (the sub-protocol
K4), "G‹g›.2.call", and the rounds in front of that step are as many as the first 28 g + 4 rows of
the written cut of the first chain into sub-protocols state (`cutFirstFull`,
Johnson/Desc/Ok/PlanWritten/CutLit.lean). The name is made as `k4PubOf` (Honest/K4/Part.lean) makes
it of the parameters' name "G‹g›:3": `String.splitOn` is brought into a form that the kernel
evaluates by the library's `splitOn_eq` (Johnson/Unfolds/SplitOn.lean). The negative test: with one
round more on the right the test is false.

  `k4StepOf g`   the step's name, made as `k4PubOf` makes it
  `roundsWritten k`   how many rounds the first k rows of the written cut state
  `k4FrontFitAt d`   the test, with d rounds more on the right
  `k4_front_closed`   **the test is true**
  `k4_front_closed_no`   with one round more: false

Not shown here. IT SPEAKS OF WRITTEN VALUES: that these are the planner's at any public files is not
said here: Law/FrontCount.lean has that under a hypothesis on the public files. Two checks by Lean's
own kernel (`decide +kernel`), one for each statement; no independent checker has replayed them. The
full size alone. Nothing on soundness, on completeness or on any other property.

Kin. The library has a closed fact of the like make on the same written table, for the attention
segments' rows (sub-protocol K5): `before_closed` (Johnson/Desc/First/Att/Row/K5BeforeClosed.lean).
This file's test reads that file's `cutPairsW`, and `roundsBy`
(Johnson/Desc/First/Att/Row/K5RowTwins.lean). Sought: by statement, to the letter and up to the
bound letters, and by short name, among the theorems of the library and of files that are no part of
it yet, as they lay with the writer: no hit. Not sought: twins of the three definitions in other
letters.
No property is claimed.
-/
import Johnson.Desc.First.Att.Row.K5BeforeClosed
import Johnson.Desc.Ok.PlanWritten.CutLit
import Johnson.Unfolds.SplitOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4

/-- The name of the step of K4's stretch in group g, made of the parameters' name as `k4PubOf` makes
it. -/
def k4StepOf (g : Nat) : String := ((s!"{"G" ++ toString g}:3").splitOn ":").headD "" ++ ".2.call"

/-- How many rounds the first k rows of the written cut state. -/
def roundsWritten (k : Nat) : Nat :=
  ((VerifiableInference.PlanWritten.cutFirstFull.take k).map (·.2.2.1)).sum

/-- A TEST ON THE TWO WRITTEN LISTS, at the twelve groups. d: so many rounds more on the right. -/
def k4FrontFitAt (d : Nat) : Bool :=
  (List.range 12).all fun g =>
    decide (H2K5.Row.roundsBy H2K5.Row.cutPairsW (k4StepOf g) =
      some (roundsWritten (28 * g + 4) + d))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **THE TWO WRITTEN LISTS COUNT ALIKE, AT THE TWELVE GROUPS.** -/
theorem k4_front_closed : k4FrontFitAt 0 = true := by
  unfold k4FrontFitAt k4StepOf
  simp only [Johnson.Unfolds.splitOn_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A negative test: with one round more on the right the test is false. -/
theorem k4_front_closed_no : k4FrontFitAt 1 = false := by
  unfold k4FrontFitAt k4StepOf
  simp only [Johnson.Unfolds.splitOn_eq]
  decide +kernel

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4StepOf
#print axioms ProofFile.Honest.K4.roundsWritten
#print axioms ProofFile.Honest.K4.k4FrontFitAt
#print axioms ProofFile.Honest.K4.k4_front_closed
#print axioms ProofFile.Honest.K4.k4_front_closed_no
