-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/Every/RowsK1.lean: ONE CLOSED FACT BY LEAN's KERNEL, ALONE IN ITS FILE:
fiveAt: the key file's shared plan (Johnson/Desc/Ok/FormRules.lean; Johnson/Bridge/PlanFiveNat.lean,
PlanOkNat.lean), at the joined written term (MW.lean). Alone: asked together in one process the
conjuncts want much memory (measured outside this tree). Its negative test: NoRowsK1.lean.
Limits. That the planner's «made» is that term at any public files is not said.
Nothing on soundness.

-/
import Johnson.AtFull.ProofPlan.Every.MW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofPlan.Every
open Johnson.Bridge.OkNat

set_option maxRecDepth 1000000 in
theorem rowsK1 :
    rowsOk (entriesAt MW.key 1) (keySharedSlots radW topW MW) = true := by
  decide +kernel

end Johnson.AtFull.ProofPlan.Every

#print axioms Johnson.AtFull.ProofPlan.Every.rowsK1
