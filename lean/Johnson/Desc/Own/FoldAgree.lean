-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/FoldAgree.lean: the three tests of Johnson/Desc/Own/Fold.lean say yes exactly where
the program `verify-on-bytes`'s tests do, at all arguments. Statements and proofs. No block's text
imports this file.
  `foldShapeFits_agrees`, `foldMaskFits_agrees`, `foldRowFits_agrees`.

-/
import Johnson.Desc.Own.Fold
import Johnson.Desc.Own.ShapesAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

theorem foldShapeFits_agrees (S : Statement) (F : FoldShape) :
    foldShapeOk S F = foldShapeFits S F := rfl

theorem foldMaskFits_agrees (S : Statement) (F : FoldShape) (fresh : Nat) :
    foldMaskOk S F fresh = foldMaskFits S F fresh := rfl

theorem foldRowFits_agrees (S : Statement) (F : FoldShape) (row : GroupRow) :
    foldRowOk S F row = foldRowFits S F row := by
  unfold foldRowOk foldRowFits
  simp only [formFits_agrees]
  rfl

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.foldShapeFits_agrees
#print axioms VerifiableInference.Desc.Own.foldMaskFits_agrees
#print axioms VerifiableInference.Desc.Own.foldRowFits_agrees
