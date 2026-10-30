-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Door/EndLines.lean: THE CLOSED LINE AT THE WRITTEN BORDER 358 THAT
Johnson/AtFull/Shape/Scope/EndAtScope.lean ASKS, AND ITS CONTROL. Evaluated by the kernel. The lines take
seconds; the two modules of the border that this file imports take some 530 s.

Limits. border358 is a written value: nothing here ties it to the run. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.EndLaws
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.AtFull.Shape.RuleAtTable
import ShapeLines.Borders.Border358

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Scope

/-- What the third chain's start asks, at the written shape and the written border. -/
theorem endOk_358 :
    endOk VerifiableInference.PlanWritten.proofSizedFull.batch.shape border358 = true := by
  decide +kernel

/-- A control: endOk says no at the first border. -/
theorem endOk_start :
    endOk VerifiableInference.PlanWritten.proofSizedFull.batch.shape startShA = false := by
  decide +kernel

end ShapeLines

#print axioms ShapeLines.endOk_358
#print axioms ShapeLines.endOk_start
