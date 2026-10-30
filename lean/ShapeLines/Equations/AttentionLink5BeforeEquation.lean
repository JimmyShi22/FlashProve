-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Equations/AttentionLink5BeforeEquation.lean: attention link 5: started from the written
value border71, members 71 to 80 of the run on shapes return a shape that equationTest accepts. That
is the shape before member 81, the one equation.
How. The link's first three closed lines (ShapeLines/Attention/) give members 71 to 79 as one piece,
by runsBetween_of_attentionFront; one further closed line gives member 80 and the test;
RunsBetween.thenTested joins the two. The line's statement equates a closed Bool with true: the Bool
runs one member from the line's start and hands what that member returns to the test. Its proof term
is Eq.refl true; kernel_rfl leaves the comparison of the two sides to Lean's kernel.
What it is for. The table's test at the member "the one equation" is oneV
(Johnson/AtFull/Shape/ValsBool.lean). By its own file's head, ProofFile.Honest.K9.oneShape
(Johnson/Desc/ProofFile/Honest/K9/EqShape.lean) is all that oneV still asks of the public data, as
one Bool on the chain's shape. It reads no field element, and a pass does not by itself give oneV.
The fact has the form RunsToTested (Johnson/AtFull/Shape/Lines/JoinTested.lean): the run returns
some shape, and the test accepts it. So no value is written for the shape before that member, which
lies inside a link, where components of the shape are long (ShapeLines/README.md). The fact's user
is the premise eqSizesYes (Johnson/Desc/ProofFile/Honest/K9/EqValuesJ.lean): unfolded, that premise
is this fact over the table's own steps (RunsToTested.atTable).
Limits. That the run from startShA reaches border71 is not said here: that follows only when all
pieces before are chained from startShA and the last of them ends at this very value. RunsToTested
speaks of every record that publicOfO returns at the stored full-size files and does not say that
there is one, nor which shape the run returns. Its run is the one over shapeL (LWn X₀), the text
of the table over a record of letters (Johnson/AtFull/Shape/TabLetters.lean); RunsToTested.atTable
and RunsToTested.atState take a fact from startShA to the table's own steps and to a state, under
the premise AtMgA and further premises. What a pass means is said in the head of
Johnson/Desc/ProofFile/Honest/K9/EqShape.lean. Alone the line can be true although the batching, or
the members before it, returned an error: where the batching's run did, look and lookHeard in the
line's start are none. These two are a term that holds the runs of members 71 to 79; a line that
opens them must bring the batching's run to its return. No law says that member 80 leaves them
unopened. The line's run is written with runOverLightTail, over the cells of
Johnson/AtFull/Shape/Lines/TailLight.lean; at member 80 this is the cell of shapeL (LWn X) itself,
and it does not read the hint. The record in the line is the one that atXLC gives to the test
(Johnson/AtFull/Shape/AtX.lean, Johnson/AtFull/Shape/AtXCounts.lean), not what publicOfO
returns; runsToTested_of_line and atXLC_all turn the line into a fact about the latter, by
runFrom_eq_lightTail.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.JoinTested
import Johnson.Unfolds.KernelRfl
import AtFullSide.Layout.Size
import ShapeLines.ClosingHint
import ShapeLines.Equations.EquationTest
import ShapeLines.Attention.Link5FirstPiece
import ShapeLines.Attention.Link5BatchingFront
import ShapeLines.Attention.Link5BatchingBack

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

-- The evaluation is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From border80LessPair with the look and lookHeard that the batching left, member 80 returns a
shape that equationTest accepts. -/
theorem attentionLink5_beforeEquation_line :
    atXLC (fun X =>
      testedB
        (runOverLightTail closingHint X 80 1
          (withLk border80LessPair (lkB closingHint 71 8 1 border71 border79LessPair X)))
        equationTest) = true := by
  kernel_rfl

/-- At every record that publicOfO returns at the stored full-size files: from border71, the ten
members 71 to 80 of the run on shapes return a shape that equationTest accepts: the shape before
member 81, the one equation. -/
theorem attentionLink5_testedBeforeEquation :
    RunsToTested 71 10 (fun _ => border71) equationTest :=
  (runsBetween_of_attentionFront closingHint Johnson.Unfolds.Layout.lay_size 71 8 (l := 5)
    (by decide) (by decide) (by decide) 6 border71 border79LessPair border80LessPair
    claimsBehindSixthRowOfLink5
    shapeBehindSixthRowOfLink5LessPair.1
    attentionLink5_firstPiece attentionLink5_batchingFront
    attentionLink5_batchingBack).thenTested
    (runsToTested_of_line closingHint 80 1 _ equationTest
      fun _ hX => atXLC_all Johnson.Unfolds.Layout.lay_size
        attentionLink5_beforeEquation_line hX)

end ShapeLines

#print axioms ShapeLines.attentionLink5_beforeEquation_line
#print axioms ShapeLines.attentionLink5_testedBeforeEquation
