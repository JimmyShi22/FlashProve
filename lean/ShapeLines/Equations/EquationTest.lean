-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Equations/EquationTest.lean: the test that this folder's lines evaluate:
ProofFile.Honest.K9.oneShape (Johnson/Desc/ProofFile/Honest/K9/EqShape.lean) at the first component of a
shape.
A definition and nothing more. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K9.EqShape
import Johnson.AtFull.Shape.FrameForm

set_option autoImplicit false

namespace ShapeLines
open Johnson.AtFull.Shape

/-- ProofFile.Honest.K9.oneShape at the chain's shape, the first component of a shape. -/
def equationTest (x : ShA) : Bool := ProofFile.Honest.K9.oneShape x.1

end ShapeLines

#print axioms ShapeLines.equationTest
