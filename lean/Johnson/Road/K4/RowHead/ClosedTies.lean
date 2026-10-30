-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/RowHead/ClosedTies.lean: THE PARAMETER FILE's SCAN HAS THE NUMERALS OF
ClosedAt.lean.

What is here. Five facts that tie the scan in closed form (Pv v, Johnson/Road/K4/RowHead/Twins.lean)
to numerals, each AS AN EQUATION and not as a test. The variable v stands in all five, and y in
weightsIs. Each is closed by kernel_rfl (Johnson/Unfolds/KernelRfl.lean).

  `shapeIs`     the layers' shape is shapeL at its own three free constants.
  `vocabIs`, `colsIs`, `setIs`   the vocabulary's size; the weights' column bits; the settings.
  `weightsIs`   the shape of the committed weights, at any layout.

Limits. Only for the parameter files whose scan is Pv v at some eight free numbers v (the full-size
model).
No property is claimed.
-/
import Johnson.Road.K4.RowHead.ClosedAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Closed
open OnBytes OnBytes.Model
open OnBytes.Road.K4 (Pv)

/-- The layers' shape is shapeL at its own three free constants. -/
theorem shapeIs (v : VerifierAndGoals.FreeLines) :
    Verify.layerShape (Pv v) =
      shapeL (Verify.layerShape (Pv v)).eps1 (Verify.layerShape (Pv v)).eps2
        (Verify.layerShape (Pv v)).epsF := by
  kernel_rfl

/-- The size of the vocabulary. -/
theorem vocabIs (v : VerifierAndGoals.FreeLines) : (Pv v).h.V = 202048 := by
  kernel_rfl

/-- The column bits of the committed weights. -/
theorem colsIs (v : VerifierAndGoals.FreeLines) : (Pv v).lkW = 18 := by
  kernel_rfl

/-- The run's settings. -/
theorem setIs (v : VerifierAndGoals.FreeLines) : (Pv v).settings = setRef := by
  kernel_rfl

/-- The shape of the committed weights, at any layout y. -/
theorem weightsIs (v : VerifierAndGoals.FreeLines) (y : Layer.Lay) :
    Verify.weightShape (Pv v) y =
      { D := 2048, L := 48, d := 5120, dh := 128, dkv := y.dkv, dq := y.dq, f := 16384, fe := 8192,
        NE := 128, V := 202048 } := by
  kernel_rfl

end OnBytes.Road.K4.Closed

#print axioms OnBytes.Road.K4.Closed.shapeIs
#print axioms OnBytes.Road.K4.Closed.vocabIs
#print axioms OnBytes.Road.K4.Closed.colsIs
#print axioms OnBytes.Road.K4.Closed.setIs
#print axioms OnBytes.Road.K4.Closed.weightsIs
