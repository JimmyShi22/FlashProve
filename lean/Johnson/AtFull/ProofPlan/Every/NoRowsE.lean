-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/Every/NoRowsE.lean: A NEGATIVE TEST, BY LEAN's KERNEL, ALONE IN ITS FILE:
THE TEST CAN FAIL: the entry file's plan's rowsOk: the radius one higher: the letter is tight
upward: it rejects. The bent copies: Bends.lean. The test's yes at the unbent term: RowsE.lean.
Limits. One bend. Nothing on soundness.

-/
import Johnson.AtFull.ProofPlan.Every.Bends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofPlan.Every
open Johnson.Bridge.OkNat

set_option maxRecDepth 1000000 in
theorem rowsE_no :
    rowsOk MW.entry.plan.entries (entrySlots (radW + 1) topW MW) = false := by
  decide +kernel

end Johnson.AtFull.ProofPlan.Every

#print axioms Johnson.AtFull.ProofPlan.Every.rowsE_no
