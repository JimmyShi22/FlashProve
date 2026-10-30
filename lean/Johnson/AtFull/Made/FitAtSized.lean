-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/FitAtSized.lean: THE PREMISE c₃ OF `chainsOf_of_parts`
(Johnson/AtFull/Made/Ledger.lean) AT z := `writtenSized`: `linksFit` returns at the written sizes'
codes, request and column bits and at the shapes' layout. Two closed ties by Lean's kernel, and a
joining. A law file; no running text imports it. Nothing on codes as such.

  `codes_tie`, `kCol_tie`: two ties between written terms of different files. Called:
    `request_shape_written` (Johnson/Goal/Numbers/RequestWritten.lean), `linksFit_at`
    (LinksFitFull.lean).
  `fit_at_sized`: the entries' views are `viewFull` · shapes.layout = `layoutFull` ⊢ c₃.

Limits. BOTH PREMISES ARE PREMISES: the first is owed by whoever shows what `declareLinks` returns,
the second by whoever shows what `Plan.reqFrame` returns at the layout file. Nothing on soundness.

-/
import Johnson.AtFull.Made.LinksFitFull
import Johnson.Goal.Written.Made
import Johnson.Goal.Numbers.RequestWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.Params
open VerifiableInference.PlanWritten VerifiableInference.PlanWritten.Joined
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (layoutFull proofCodesWritten)

set_option maxRecDepth 1000000 in
/-- The written sizes' codes are the written sendings' codes. -/
theorem codes_tie : proofSizedFull.codes = proofCodesWritten := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The committed table has 2 ^ 18 columns in the written sizes. -/
theorem kCol_tie : proofSizedFull.batch.shape.kCol = 18 := by decide +kernel

/-- **c₃ at z := writtenSized**: the links fit the written sizes and the shapes' layout, where the
entries' views and the layout are the written ones. -/
theorem fit_at_sized {links : Array LinkH} {shapes : Shapes}
    (hv : links.toList.map Johnson.AtFull.Made.viewOf = viewFull)
    (hL : shapes.layout = layoutFull) :
    linksFit links writtenSized.proof.codes writtenSized.proof.request shapes.layout
      writtenSized.proof.batch.shape.kCol = .ok () := by
  show linksFit links proofSizedFull.codes proofSizedFull.request shapes.layout
    proofSizedFull.batch.shape.kCol = .ok ()
  rw [codes_tie, request_shape_written, kCol_tie, hL]
  exact linksFit_at hv

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.codes_tie
#print axioms Johnson.AtFull.Made.kCol_tie
#print axioms Johnson.AtFull.Made.fit_at_sized
