-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Equations/LayersLink12BeforeEquation.lean: the layers' link 12: started from the written
value border169, members 169 to 178 of the run on shapes return a shape that equationTest accepts.
That is the shape before member 179, the one equation.
How. Sixteen of the link's closed lines (ShapeLines/Layers/) give members 169 to 177 as one piece,
by layersLink_runsThroughBatching
(Johnson/AtFull/Shape/Lines/Layers/LayersLinkRunsThroughBatching.lean); one further closed line
gives member 178 and the test; RunsBetween.thenTested joins the two. The line's statement equates a
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
Limits. That the run from startShA reaches border169 is not said here: that follows only when all
pieces before are chained from startShA and the last of them ends at this very value. RunsToTested
speaks of every record that publicOfO returns at the stored full-size files and does not say that
there is one, nor which shape the run returns. Its run is the one over shapeL (LWn X₀), the text
of the table over a record of letters (Johnson/AtFull/Shape/TabLetters.lean); RunsToTested.atTable
and RunsToTested.atState take a fact from startShA to the table's own steps and to a state, under
the premise AtMgA and further premises. What a pass means is said in the head of
Johnson/Desc/ProofFile/Honest/K9/EqShape.lean. Alone the line can be true although the run of member
177 returned an error: the layers' parts in the line's start are then the empty ones. These parts
are a term that holds the run of the table's own cell at member 177, which is the table's own
batching and not the light step, and in that run's start the runs of the members before, down to
member 169; a line that opens a part must bring the run of member 177 to its return. Whether this
line opens one is not said. The line's run is written with runOverLightTail, over the cells of
Johnson/AtFull/Shape/Lines/TailLight.lean; at member 178 this is the cell of shapeL (LWn X)
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
import ShapeLines.Layers.Plan6Lines
import ShapeLines.Layers.Link12MembersOneToThree
import ShapeLines.Layers.Link12OwnRoundsGuards
import ShapeLines.Layers.Link12MergeRecords
import ShapeLines.Layers.Link12AfterOwnRounds
import ShapeLines.Layers.Link12MembersFiveToEight
import ShapeLines.Layers.Link12Batching

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

open Johnson.AtFull.Shape.Layers

-- The evaluation is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From border178LessLayersParts with the layers' parts that member 177 left, member 178 returns a
shape that equationTest accepts. -/
theorem layersLink12_beforeEquation_line :
    atXLC (fun X =>
      testedB
        (runOverLightTail closingHint X 178 1 (startAfterBatching closingHint 12 layersBorders12 X))
        equationTest) = true := by
  kernel_rfl

/-- At every record that publicOfO returns at the stored full-size files: from border169, the ten
members 169 to 178 of the run on shapes return a shape that equationTest accepts: the shape before
member 179, the one equation. -/
theorem layersLink12_testedBeforeEquation :
    RunsToTested 169 10 (fun _ => border169) equationTest :=
  (show RunsBetween 169 9 (fun _ => border169)
      (startAfterBatching closingHint 12 layersBorders12) from
    layersLink_runsThroughBatching Johnson.Unfolds.Layout.lay_size closingHint 12
      (by decide) (by decide) layersBorders12 layersPlan6_lines
      layersLink12_membersOneToThree
      layersLink12_ownRoundsGuards
      layersLink12_mergeRecords
      layersLink12_afterOwnRounds
      layersLink12_membersFiveToEight
      layersLink12_batching).thenTested
    (runsToTested_of_line closingHint 178 1 _ equationTest
      fun _ hX => atXLC_all Johnson.Unfolds.Layout.lay_size
        layersLink12_beforeEquation_line hX)

end ShapeLines

#print axioms ShapeLines.layersLink12_beforeEquation_line
#print axioms ShapeLines.layersLink12_testedBeforeEquation
