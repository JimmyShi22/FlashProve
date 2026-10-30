-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/LaidInsidePlan.lean: the three tests under which the seats lie inside their
messages and off their pads (Johnson/Goal/Meaning/LaidInside.lean), out of the conjunction of four
in which the programs ask them of a plan. One theorem.

The programs test a first query's codes, shape and layout by Codes.lengthsOk, reqOk, "the shape's
number of answers is the plan's samples" and reqLayoutOk, one after the other. This file names these
four Bools and no caller of them, so that it stands whatever text asks them.

  three_of_four   (codes.lengthsOk && reqOk codes shape && shape.answers == n &&
    reqLayoutOk codes shape layout) = true gives codes.lengthsOk = true, reqShapeOk shape = true and
    reqLayoutOk codes shape layout = true.

Object, user, letters. Object: the four Bools (OnBytes/Iop/Ground.lean, Req.lean, ReqRows.lean).
User: none in the library yet; it is shaped for whoever has a block's own test on the plan as that
conjunction. Letters: all free.

What is not claimed. That the conjunction holds at any plan. Nothing on soundness, nothing on
hiding. The program does not import this file.
-/
import Johnson.Goal.Meaning.LaidInside

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning

open OnBytes
open OnBytes.Params (ReqLayout ReqShape)

/-- **The conjunction of four holds the three tests.** -/
theorem three_of_four {codes : Codes} {shape : ReqShape} {layout : ReqLayout} {n : Nat}
    (h : (codes.lengthsOk && reqOk codes shape && shape.answers == n &&
      reqLayoutOk codes shape layout) = true) :
    codes.lengthsOk = true ∧ reqShapeOk shape = true ∧ reqLayoutOk codes shape layout = true := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, shapeOk_of_reqOk h.1.1.2, h.2⟩

end Meaning

#print axioms Meaning.three_of_four
