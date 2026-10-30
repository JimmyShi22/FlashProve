-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ReqFrameAtWritten.lean: THE REQUEST's FRAME OUT OF THE LAYOUT FILE's VALUE, AT
THE FULL SIZE: `Plan.reqFrame` (OnBytes/Plan/ReqFrame.lean) RETURNS, AND WHAT: at the written
declared arrays, the layout file's written value and 1 answer it gives the written links and the
written layout `Johnson.G.layoutFull`. One decision of Lean's kernel; then the premise b₂ of the
ledger of the planner's second half, from three equations.

  **`reqFrame_written`**: `reqFrame declaredW LW 1 = some (reqLinksW, layoutFull)`: by
    `decide +kernel` (99 steps of `takeGroup`, 5,419 of `takeBlock`).
  **`reqFrame_of_three`**: so `reqFrame declared file answers = some (reqLinksW, layoutFull)`
    wherever declared has `declaredW`'s moments, link by link (`reqFrame_reads`,
    Johnson/AtFull/Made/ReqFrameReads.lean), file = LW and answers = 1.
Limits. The full size alone. `declaredW` and `LW` are WRITTEN values: that `declareLinks` returns
the one and `layoutRead` the other at any public files is not said here (DeclaredLit.lean's and
Johnson/AtFull/LayoutRead/Values/All.lean's heads say whence they are). Nothing on soundness. On
hiding nothing.

-/
import Johnson.AtFull.LayoutRead.Values.All
import Johnson.G.LayoutLit
import Johnson.AtFull.Made.DeclaredLit
import Johnson.AtFull.Made.ReqFrameReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes.Plan OnBytes.Params
open OnBytes.Model.Stages (FrameLink)
open Johnson.AtFull.LayoutRead (LW)
open Johnson.G (layoutFull)

set_option maxRecDepth 1000000 in
/-- **THE FRAME AT THE WRITTEN VALUES.** -/
theorem reqFrame_written : reqFrame declaredW LW 1 = some (reqLinksW, layoutFull) := by
  decide +kernel

/-- **THE LEDGER's PREMISE b₂, FROM THREE EQUATIONS.** -/
theorem reqFrame_of_three {declared : Array FrameLink} {file : LayoutLines} {answers : Nat}
    (hd : declared.map (·.moment) = declaredW.map (·.moment)) (hf : file = LW)
    (ha : answers = 1) : reqFrame declared file answers = some (reqLinksW, layoutFull) := by
  rw [reqFrame_reads hd, hf, ha]
  exact reqFrame_written

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.reqFrame_written
#print axioms Johnson.AtFull.Made.reqFrame_of_three
