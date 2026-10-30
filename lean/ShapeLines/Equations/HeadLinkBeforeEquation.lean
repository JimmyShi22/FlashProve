-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Equations/HeadLinkBeforeEquation.lean: the head's link: started from the written value
border337, members 337 to 348 of the run on shapes return a shape that equationTest accepts. That is
the shape before member 349, the one equation.
How. The link's first three closed lines (ShapeLines/Head/) give members 337 to 347 as one piece;
one further closed line gives member 348 and the test; RunsBetween.thenTested joins the two. The
line's statement equates a closed Bool with true: the Bool runs one member from the line's start and
hands what that member returns to the test. Its proof term is Eq.refl true; kernel_rfl leaves the
comparison of the two sides to Lean's kernel.
What it is for. The table's test at the member "the one equation" is oneV
(Johnson/AtFull/Shape/ValsBool.lean). By its own file's head, ProofFile.Honest.K9.oneShape
(Johnson/Desc/ProofFile/Honest/K9/EqShape.lean) is all that oneV still asks of the public data, as
one Bool on the chain's shape. It reads no field element, and a pass does not by itself give oneV.
The fact has the form RunsToTested (Johnson/AtFull/Shape/Lines/JoinTested.lean): the run returns
some shape, and the test accepts it. So no value is written for the shape before that member, which
lies inside a link, where components of the shape are long (ShapeLines/README.md). The fact's user
is the premise eqSizesYes (Johnson/Desc/ProofFile/Honest/K9/EqValuesJ.lean): unfolded, that premise
is this fact over the table's own steps (RunsToTested.atTable).
Limits. That the run from startShA reaches border337 is not said here: that follows only when all
pieces before are chained from startShA and the last of them ends at this very value. RunsToTested
speaks of every record that publicOfO returns at the stored full-size files and does not say that
there is one, nor which shape the run returns. Its run is the one over shapeL (LWn X₀), the text
of the table over a record of letters (Johnson/AtFull/Shape/TabLetters.lean); RunsToTested.atTable
and RunsToTested.atState take a fact from startShA to the table's own steps and to a state, under
the premise AtMgA and further premises. What a pass means is said in the head of
Johnson/Desc/ProofFile/Honest/K9/EqShape.lean. Alone the line can be true although the step
headBatchingLight, or the members before it, returned an error: where the step did, look and
lookHeard in the line's start are none. The line is stated under atXLC although its start holds, as
a term, the run of members 340 to 346 and the step at member 347, and members of that run read the
head's layout. No law says that member 348 leaves that term unopened. The line's run is written with
runOverLightTail, over the cells of Johnson/AtFull/Shape/Lines/TailLight.lean; at member 348 this is
the cell of shapeL (LWn X) itself, and it does not read the hint. The record in the line is the
one that atXLC gives to the test (Johnson/AtFull/Shape/AtX.lean,
Johnson/AtFull/Shape/AtXCounts.lean), not what publicOfO returns; runsToTested_of_line and
atXLC_all turn the line into a fact about the latter, by runFrom_eq_lightTail.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.JoinTested
import Johnson.Unfolds.KernelRfl
import AtFullSide.Layout.Size
import ShapeLines.ClosingHint
import ShapeLines.Equations.EquationTest
import Johnson.AtFull.Shape.Lines.Head.HeadLight
import ShapeLines.Head.HeadLinkFirstPiece
import ShapeLines.Head.HeadLinkSecondPiece
import ShapeLines.Head.HeadLinkBatching

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

-- The evaluation is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From border348LessPair with the look and lookHeard that the step headBatchingLight left, member
348 returns a shape that equationTest accepts. -/
theorem headLink_beforeEquation_line :
    atXLC (fun X =>
      testedB
        (runOverLightTail closingHint X 348 1
          (borderWithPairOfStep (fun X => headBatchingLight (LWn X))
            (borderWithPairOfRun closingHint 340 7 (fun _ => border340LessPair) border347LessPair)
            border348LessPair X))
        equationTest) = true := by
  kernel_rfl

/-- At every record that publicOfO returns at the stored full-size files: from border337, members
337 to 347 of the run on shapes return border348LessPair with the look and lookHeard that the step
headBatchingLight left. -/
theorem headLink_runsThroughBatching :
    RunsBetween 337 11 (fun _ => border337)
      (borderWithPairOfStep (fun X => headBatchingLight (LWn X))
        (borderWithPairOfRun closingHint 340 7 (fun _ => border340LessPair) border347LessPair)
        border348LessPair) :=
  ((runsBetween_of_whole closingHint 337 3 (fun _ => border337) border340LessPair
      fun _ hX => atXLC_all Johnson.Unfolds.Layout.lay_size headLink_firstPiece hX).chain
    (runsBetween_of_lessPair closingHint 340 7 (fun _ => border340LessPair) border347LessPair
      fun _ hX => atXHC_all Johnson.Unfolds.Layout.lay_size headLink_secondPiece hX)).chain
    (runsBetween_of_step 347 (fun X => headBatchingLight (LWn X))
      (fun X _ _ h => headBatchingLight_standsUnder (LWn X) h)
      (borderWithPairOfRun closingHint 340 7 (fun _ => border340LessPair) border347LessPair)
      border348LessPair
      fun _ hX => atXHC_all Johnson.Unfolds.Layout.lay_size headLink_batching hX)

/-- At every record that publicOfO returns at the stored full-size files: from border337, the twelve
members 337 to 348 of the run on shapes return a shape that equationTest accepts: the shape before
member 349, the one equation. -/
theorem headLink_testedBeforeEquation :
    RunsToTested 337 12 (fun _ => border337) equationTest :=
  headLink_runsThroughBatching.thenTested
    (runsToTested_of_line closingHint 348 1 _ equationTest
      fun _ hX => atXLC_all Johnson.Unfolds.Layout.lay_size headLink_beforeEquation_line hX)

end ShapeLines

#print axioms ShapeLines.headLink_beforeEquation_line
#print axioms ShapeLines.headLink_runsThroughBatching
#print axioms ShapeLines.headLink_testedBeforeEquation
