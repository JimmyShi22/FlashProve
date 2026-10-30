-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Equations/EquationTestControls.lean: controls of this folder's twenty-five closed lines:
equationTest can say no. Three pairs of closed lines, one pair for each kind of link: the layers'
link 0, attention link 1, the head's link; and one line that shows a limit of the test.
What a pair is. The control is the link's own line with the count of members 0 in the place of 1,
and "false" in the place of "true": at the line's own start, which is the shape one member earlier,
the test says no. A run of no member returns its start by definition, so no error of the run can
make the line false. But a line under atXLC is false also where a maker of the record returns an
error (Johnson/AtFull/Shape/AtX.lean). So a control counts only beside its witness: the same line
under the test that accepts everything, which is true only if the makers return.
How. Each statement equates a closed Bool with a Bool; the proof term is Eq.refl of that Bool;
kernel_rfl leaves the comparison of the two sides to Lean's kernel.
Limits. A control shows that the test is not constantly true: it says no at three written starts. No
control runs a member, and the test reads none of the terms that a start carries: so what the
twenty-five lines do besides, run one member and hand on what it returns, no control does. The test
tells the tested shape from the shape one member before, not from the shape one member after: at the
layers' link 0 it accepts the shape after the one equation as well
(layersLink0_testAfterMember11_yes). So a pass does not say that the shape is the one before the one
equation and no other. The starts are those of the links' own lines, with all their limits
(ShapeLines/Equations/LayersLink0BeforeEquation.lean, AttentionLink1BeforeEquation.lean,
HeadLinkBeforeEquation.lean). The record in a line is the one that atXLC gives to the test
(Johnson/AtFull/Shape/AtX.lean, Johnson/AtFull/Shape/AtXCounts.lean), not what publicOfO returns. No
fact of this library calls these seven lines.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.JoinTested
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import Johnson.AtFull.Shape.Lines.Head.HeadLight
import Johnson.Unfolds.KernelRfl
import ShapeLines.ClosingHint
import ShapeLines.Layers.NoHint
import ShapeLines.Equations.EquationTest
import ShapeLines.Layers.Link0Borders
import ShapeLines.Borders.Border15
import ShapeLines.Borders.Border23LessPair
import ShapeLines.Borders.Border24LessPair
import ShapeLines.Borders.Border340LessPair
import ShapeLines.Borders.Border347LessPair
import ShapeLines.Borders.Border348LessPair

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

open Johnson.AtFull.Shape.Layers

-- The evaluation is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- A control: from border10LessLayersParts with the layers' parts that member 9 left, with no
member run, equationTest says no: that is the shape before member 10, one member earlier than the
shape that the link's own line tests. -/
theorem layersLink0_testBeforeMember10_no :
    atXLC (fun X =>
      testedB
        (runOverLightTail noHint X 10 0
          (startAfterBatching noHint 0 layersBorders0 X))
        equationTest) = false := by
  kernel_rfl

-- The evaluation is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- The witness beside it: the same line under the test that accepts everything is true. So the
makers of the record return, and the control's "false" is the test's. -/
theorem layersLink0_testBeforeMember10_returns :
    atXLC (fun X =>
      testedB
        (runOverLightTail noHint X 10 0
          (startAfterBatching noHint 0 layersBorders0 X))
        (fun _ => true)) = true := by
  kernel_rfl

-- The evaluation is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- A control: from border24LessPair with the look and lookHeard that the batching left, with no
member run, equationTest says no: that is the shape before member 24, one member earlier than the
shape that the link's own line tests. -/
theorem attentionLink1_testBeforeMember24_no :
    atXLC (fun X =>
      testedB
        (runOverLightTail closingHint X 24 0
          (withLk border24LessPair (lkB closingHint 15 8 1 border15 border23LessPair X)))
        equationTest) = false := by
  kernel_rfl

-- The evaluation is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- The witness beside it: the same line under the test that accepts everything is true. So the
makers of the record return, and the control's "false" is the test's. -/
theorem attentionLink1_testBeforeMember24_returns :
    atXLC (fun X =>
      testedB
        (runOverLightTail closingHint X 24 0
          (withLk border24LessPair (lkB closingHint 15 8 1 border15 border23LessPair X)))
        (fun _ => true)) = true := by
  kernel_rfl

-- The evaluation is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- A control: from border348LessPair with the look and lookHeard that the step headBatchingLight
left, with no member run, equationTest says no: that is the shape before member 348, one member
earlier than the shape that the link's own line tests. -/
theorem headLink_testBeforeMember348_no :
    atXLC (fun X =>
      testedB
        (runOverLightTail closingHint X 348 0
          (borderWithPairOfStep (fun X => headBatchingLight (LWn X))
            (borderWithPairOfRun closingHint 340 7 (fun _ => border340LessPair) border347LessPair)
            border348LessPair X))
        equationTest) = false := by
  kernel_rfl

-- The evaluation is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- The witness beside it: the same line under the test that accepts everything is true. So the
makers of the record return, and the control's "false" is the test's. -/
theorem headLink_testBeforeMember348_returns :
    atXLC (fun X =>
      testedB
        (runOverLightTail closingHint X 348 0
          (borderWithPairOfStep (fun X => headBatchingLight (LWn X))
            (borderWithPairOfRun closingHint 340 7 (fun _ => border340LessPair) border347LessPair)
            border348LessPair X))
        (fun _ => true)) = true := by
  kernel_rfl

-- The evaluation is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From border10LessLayersParts with the layers' parts that member 9 left, members 10 and 11 return
a shape that equationTest accepts too: the shape after member 11, the one equation. -/
theorem layersLink0_testAfterMember11_yes :
    atXLC (fun X =>
      testedB
        (runOverLightTail noHint X 10 2
          (startAfterBatching noHint 0 layersBorders0 X))
        equationTest) = true := by
  kernel_rfl

end ShapeLines

#print axioms ShapeLines.layersLink0_testBeforeMember10_no
#print axioms ShapeLines.layersLink0_testBeforeMember10_returns
#print axioms ShapeLines.attentionLink1_testBeforeMember24_no
#print axioms ShapeLines.attentionLink1_testBeforeMember24_returns
#print axioms ShapeLines.headLink_testBeforeMember348_no
#print axioms ShapeLines.headLink_testBeforeMember348_returns
#print axioms ShapeLines.layersLink0_testAfterMember11_yes
