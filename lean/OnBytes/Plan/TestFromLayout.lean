-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/TestFromLayout.lean: a test of OnBytes/Plan/FromLayout.lean. It runs when this file
compiles.

OnBytes/Plan/TestKeyOneTime.lean derives the parameter bytes of the first chain of the key of the
example prover/examples/target_small_f2_roomy, in another form, from a list of units that was
read back from the expected bytes. Here that list is held against the layout that follows from the
example's shape. So the two tests together lead from the example's shape and lines to the bytes.

No module of the program imports this file. It holds no theorem.
-/
import OnBytes.Plan.FromLayout
import OnBytes.Plan.TestKeyOneTime
import OnBytes.Model.TestWeights

namespace OnBytes.Plan.TestFromLayout

/-- The layout of the example's matrix. -/
def layout : Option Model.WsLay := (Model.WsLay.build Model.TestWeights.smallKit 11).toOption

#guard layout.map unitsOfLayout == some TestKeyOneTime.units
#guard layout.any layoutOk
#guard layout.bind (shapeOfLayout · 11) == TestKeyOneTime.shape && TestKeyOneTime.shape.isSome

end OnBytes.Plan.TestFromLayout
