-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Equations/LayersLink8BeforeEquation.lean: the layers' link 8: started from the written
value border113, members 113 to 122 of the run on shapes return a shape that equationTest accepts.
That is the shape before member 123, the one equation.
How. Sixteen of the link's closed lines (ShapeLines/Layers/) give members 113 to 121 as one piece,
by layersLink_runsThroughBatching
(Johnson/AtFull/Shape/Lines/Layers/LayersLinkRunsThroughBatching.lean); one further closed line
gives member 122 and the test; RunsBetween.thenTested joins the two. The line's statement equates a
closed Bool with true: the Bool runs one member from the line's start and hands what that member
returns to the test. Its proof term is Eq.refl true; kernel_rfl leaves the comparison of the two
sides to Lean's kernel.
What it is for. The table's test at the member "the one equation" is oneV
(Johnson/AtFull/Shape/ValsBool.lean). By its own file's head, ProofFile.Honest.K9.oneShape
(Johnson/Desc/ProofFile/Honest/K9/EqShape.lean) is all that oneV still asks of the public data, as
one Bool on the chain's shape. It reads no field element, and a pass does not by itself give oneV.
The fact has the form RunsToTested (Johnson/AtFull/Shape/Lines/JoinTested.lean): the run returns
some shape, and the test accepts it. So no value is written for the shape before that member, which
lies inside a link, where components of the shape are long (ShapeLines/README.md). The fact's user
is the premise eqSizesYes (Johnson/Desc/ProofFile/Honest/K9/EqValuesJ.lean): unfolded, that premise
is this fact over the table's own steps (RunsToTested.atTable).
Limits. That the run from startShA reaches border113 is not said here: that follows only when all
pieces before are chained from startShA and the last of them ends at this very value. RunsToTested
speaks of every record that publicOfO returns at the stored full-size files and does not say that
there is one, nor which shape the run returns. Its run is the one over shapeL (LWn X₀), the text
of the table over a record of letters (Johnson/AtFull/Shape/TabLetters.lean); RunsToTested.atTable
and RunsToTested.atState take a fact from startShA to the table's own steps and to a state, under
the premise AtMgA and further premises. What a pass means is said in the head of
Johnson/Desc/ProofFile/Honest/K9/EqShape.lean. Alone the line can be true although the run of member
121 returned an error: the layers' parts in the line's start are then the empty ones. These parts
are a term that holds the run of the table's own cell at member 121, which is the table's own
batching and not the light step, and in that run's start the runs of the members before, down to
member 113; a line that opens a part must bring the run of member 121 to its return. Whether this
line opens one is not said. The line's run is written with runOverLightTail, over the cells of
Johnson/AtFull/Shape/Lines/TailLight.lean; at member 122 this is the cell of shapeL (LWn X)
itself, and it does not read the hint. The record in the line is the one that atXLC gives to the
test (Johnson/AtFull/Shape/AtX.lean, Johnson/AtFull/Shape/AtXCounts.lean), not what publicOfO
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
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRunsThroughBatching
import ShapeLines.Layers.Plan4Lines
import ShapeLines.Layers.Link8MembersOneToThree
import ShapeLines.Layers.Link8OwnRoundsGuards
import ShapeLines.Layers.Link8MergeRecords
import ShapeLines.Layers.Link8AfterOwnRounds
import ShapeLines.Layers.Link8MembersFiveToEight
import ShapeLines.Layers.Link8Batching

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

open Johnson.AtFull.Shape.Layers

-- The evaluation is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From border122LessLayersParts with the layers' parts that member 121 left, member 122 returns a
shape that equationTest accepts. -/
theorem layersLink8_beforeEquation_line :
    atXLC (fun X =>
      testedB
        (runOverLightTail closingHint X 122 1 (startAfterBatching closingHint 8 layersBorders8 X))
        equationTest) = true := by
  kernel_rfl

/-- At every record that publicOfO returns at the stored full-size files: from border113, the ten
members 113 to 122 of the run on shapes return a shape that equationTest accepts: the shape before
member 123, the one equation. -/
theorem layersLink8_testedBeforeEquation :
    RunsToTested 113 10 (fun _ => border113) equationTest :=
  (show RunsBetween 113 9 (fun _ => border113)
      (startAfterBatching closingHint 8 layersBorders8) from
    layersLink_runsThroughBatching Johnson.Unfolds.Layout.lay_size closingHint 8
      (by decide) (by decide) layersBorders8 layersPlan4_lines
      layersLink8_membersOneToThree
      layersLink8_ownRoundsGuards
      layersLink8_mergeRecords
      layersLink8_afterOwnRounds
      layersLink8_membersFiveToEight
      layersLink8_batching).thenTested
    (runsToTested_of_line closingHint 122 1 _ equationTest
      fun _ hX => atXLC_all Johnson.Unfolds.Layout.lay_size
        layersLink8_beforeEquation_line hX)

end ShapeLines

#print axioms ShapeLines.layersLink8_beforeEquation_line
#print axioms ShapeLines.layersLink8_testedBeforeEquation
