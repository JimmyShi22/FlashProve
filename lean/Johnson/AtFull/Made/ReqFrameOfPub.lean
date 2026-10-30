-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ReqFrameOfPub.lean: THE PREMISE b₂ OF THE LEDGER OF THE PLANNER's SECOND HALF,
TO THE LETTER, WITH ITS THIRD EQUATION PAID: `Plan.reqFrame declared file X.P.frame.answers = some
(reqLinksW, layoutFull)` at a public part as at the full size (`H2K.Sizes.PubFull X`,
Johnson/Desc/K12/Law/Sizes/StageSizesAtScope.lean: its field frame says that the lines are the
written ones, whose number of answers is 1), where declared has `declaredW`'s moments and file = LW.
One theorem, one call of `reqFrame_of_three` (Johnson/AtFull/Made/ReqFrameAtWritten.lean).
What shows `PubFull X` in scope: `H2K.Sizes.pubFull_of_steps`
(Johnson/Desc/K12/Law/Sizes/PublicOAtScope.lean).
Limits: those of the files that are called. Two premises stay: the declared moments and the file's
value. Nothing on soundness. On hiding nothing.

-/
import Johnson.AtFull.Made.ReqFrameAtWritten
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes.Plan
open OnBytes.Model.Stages (FrameLink)
open OnBytes.Model.Verify (Public)
open Johnson.AtFull.LayoutRead (LW)
open Johnson.G (layoutFull)

/-- **b₂, at a public part as at the full size.** -/
theorem reqFrame_of_pub {X : Public} (P : H2K.Sizes.PubFull X) {declared : Array FrameLink}
    {file : LayoutLines} (hd : declared.map (·.moment) = declaredW.map (·.moment))
    (hf : file = LW) : reqFrame declared file X.P.frame.answers = some (reqLinksW, layoutFull) :=
  reqFrame_of_three hd hf (by rw [P.frame]; rfl)

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.reqFrame_of_pub
