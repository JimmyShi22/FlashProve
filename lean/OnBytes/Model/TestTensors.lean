-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestTensors.lean: tests of OnBytes/Model/Tensors.lean.

The tests run when this file is compiled. The program does not import this file. Each function is
run on small numbers or on a point of three coordinates. The expected numbers of clamp, clampBound,
tenCell, headFeat and blockRow were worked out by hand from the definitions in
verifier/src/vf_attention_shape.h. The other expected values are expressions in eqTab and blockRow
that follow those definitions. They show where a point is cut and how the rows are ordered, not what
eqTab gives. A refusal is seen as none: its name is not compared. The file holds no theorem.
-/
import OnBytes.Model.Tensors

namespace OnBytes.Model.TestTensors

#guard clamp == 2047 && clampBound == 2048

-- limb 1, layer 2, feature 4 of a tensor of 3 layers of 5 features that begins at feature 10
#guard tenCell ⟨10, 2, 3, 5⟩ 1 2 4 == 39
-- limb 1, layer 1: with the limbs inside the layers the answer would be 29
#guard tenCell ⟨10, 2, 3, 5⟩ 1 1 4 == 34

-- a tensor of 12 features has 3 heads of 4 features
#guard (headFeat ⟨0, 1, 1, 12⟩ 2 4).toOption == some 8
#guard (headFeat ⟨0, 1, 1, 12⟩ 3 4).toOption == none
#guard (headFeat ⟨0, 1, 1, 12⟩ 0 5).toOption == none
#guard (headFeat ⟨0, 1, 1, 12⟩ 0 0).toOption == none
#guard (headFeat ⟨0, 1, 1, 12⟩ 5 1).toOption == some 5

-- token 1 of the feature with low bits 2, at 3 tokens
#guard blockRow 2 1 3 == 7

/-- A point of three coordinates. -/
def pointOfThree : Array E := #[E.mk3 2 0 0, E.mk3 3 1 0, E.mk3 5 0 7]

#guard (List.range 2).all fun c2 => (List.range 3).all fun tk =>
  (blockRows (pointOfThree.extract 0 2) pointOfThree).getD (blockRow c2 tk 3) zeroE ==
    mulE (pointOfThree.getD c2 zeroE) (pointOfThree.getD tk zeroE)
#guard longPoint (pointOfThree.extract 0 1) (pointOfThree.extract 1 3) == pointOfThree
-- one coordinate for the feature's low bit, two for the token
#guard (List.range 2).all fun c2 => (List.range 4).all fun tk =>
  (longPhi pointOfThree 1 2).getD (blockRow c2 tk 4) zeroE ==
    mulE ((eqTab (pointOfThree.extract 0 1)).getD c2 zeroE)
      ((eqTab (pointOfThree.extract 1 3)).getD tk zeroE)
#guard (cutLast pointOfThree 1).toOption ==
  some (pointOfThree.extract 0 2, pointOfThree.extract 2 3)
#guard (cutLast pointOfThree 3).toOption == some (#[], pointOfThree)
#guard (cutLast pointOfThree 4).toOption == none
#guard (lastOf pointOfThree 2).toOption == some (pointOfThree.extract 1 3)
#guard (hiTab pointOfThree 1 2).toOption == some (eqTab (pointOfThree.extract 0 2))
#guard (hiTab pointOfThree 1 1).toOption == none
#guard (hiTab pointOfThree 4 0).toOption == none

end OnBytes.Model.TestTensors
