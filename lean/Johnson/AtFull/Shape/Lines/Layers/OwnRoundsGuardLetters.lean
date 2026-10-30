-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/OwnRoundsGuardLetters.lean: at the layout yFull the host's count
of the padding keys is the layout's own: (laidLayers P == some P.y.fo.pub) = true. One law; nothing
is evaluated.

Why. The step of the layers' own rounds has two guards that read no shape (k4PubB,
Johnson/AtFull/Shape/TabLetters.lean). The second follows from two laws of the library at the layout
yFull (laid_of_y, Johnson/AtFull/K3X/LaidAtFull.lean; counts_yFull, CountsAtFull.lean in the same
folder), so that no closed Bool need count the padding keys.

  **laidLayersTest_atFullLayout**   P.y = yFull gives (laidLayers P == some P.y.fo.pub) = true.

Limits. An implication. That what publicOfO returns at the stored full-size files has the layout
yFull is y_at_zFull (Johnson/AtFull/Shape/AtXCounts.lean). Only the full-size layout is covered.
Nothing on the first guard, k4PlanB. Nothing says that a step returns. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.LettersNumerals
import Johnson.AtFull.Shape.AtXCounts
import Johnson.AtFull.K3X.LaidAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open OnBytes.Road.K4.Trial.Values (yFull)
open VerifiableInference.Desc.First.Look (laidLayers)

/-- **At the layout yFull the host's count of the padding keys is the layout's own**:
by two laws of the library; nothing is evaluated. -/
theorem laidLayersTest_atFullLayout {P : Layer.Pub} (hy : P.y = yFull) :
    (laidLayers P == some P.y.fo.pub) = true := by
  rw [Johnson.AtFull.K3X.laid_of_y hy, hy, Johnson.AtFull.K3X.counts_yFull]
  exact beq_self_eq_true _

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.laidLayersTest_atFullLayout
