-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/LastChain/LastRunControls.lean: three controls of the closed line last_run_at_border358
(ShapeLines/LastChain/LastRunAtBorder358.lean), and one line on a limit of it.
  lastRunControl_startHandsNothing    handedOf startShA is none: at the shape from which the run
                                      over the first chain starts, the line's match takes its last
                                      arm.
  lastRunControl_weightsMarkFalse     with the mark on the pending row's weights set to false,
                                      lastRunClosed is false: the run returns an error.
  lastRunControl_statementMarkFalse   with the mark on the statement set to false, the same.
  lastRunControl_withoutMask          with the mask set to none the run returns all the same.
How. Each statement is an equation with a closed left side; the proof term is Eq.refl of the right
side; kernel_rfl leaves the comparison of the two sides to Lean's kernel. In the second and third
control the arm for a missing end is true: so "false" there says that both ends are some value, that
realSized is some value, and that the run returns an error.
Limits. The first control says nothing of lastRunClosed. The second and third show that the line's
yes depends on the two marks, which handedOf sets to true whatever the value is. By the guards' text
both errors are the first member's (gSecond, E2E/KeyShapeSecond.lean): no control makes one of the
three later guards return an error. The fourth line shows that the yes does not depend on the mask.
No fact of this library calls these four.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import ShapeLines.LastChain.LastRunAtBorder358
import Johnson.AtFull.Shape.RuleAtTable

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open AtFullSide.LaterThreads
open Johnson.AtFull.Shape (startShA)

-- The limit of heartbeats is lifted for the comparison.
set_option maxHeartbeats 0 in
/-- A control: startShA has no end to hand. -/
theorem lastRunControl_startHandsNothing : handedOf startShA = none := by
  kernel_rfl

-- The limit of heartbeats is lifted for the comparison.
set_option maxHeartbeats 0 in
/-- A control: with the mark on the pending row's weights set to false the run returns an error. -/
theorem lastRunControl_weightsMarkFalse :
    (match handedOf border358, writtenSharedEnd with
      | some a, some b => lastRunClosed (doorShape { a with weights := false } b)
      | _, _ => true) = false := by
  kernel_rfl

-- The limit of heartbeats is lifted for the comparison.
set_option maxHeartbeats 0 in
/-- A control: with the mark on the statement set to false the run returns an error. -/
theorem lastRunControl_statementMarkFalse :
    (match handedOf border358, writtenSharedEnd with
      | some a, some b => lastRunClosed (doorShape { a with tidy := false } b)
      | _, _ => true) = false := by
  kernel_rfl

-- The limit of heartbeats is lifted for the comparison.
set_option maxHeartbeats 0 in
/-- A limit: with the mask set to none the run returns as well. -/
theorem lastRunControl_withoutMask :
    (match handedOf border358, writtenSharedEnd with
      | some a, some b => lastRunClosed (doorShape { a with mask := none } b)
      | _, _ => false) = true := by
  kernel_rfl

end ShapeLines

#print axioms ShapeLines.lastRunControl_startHandsNothing
#print axioms ShapeLines.lastRunControl_weightsMarkFalse
#print axioms ShapeLines.lastRunControl_statementMarkFalse
#print axioms ShapeLines.lastRunControl_withoutMask
