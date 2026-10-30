-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/Every/NoBats.lean: A NEGATIVE TEST, BY LEAN's KERNEL, ALONE IN ITS FILE:
THE TEST CAN FAIL: batsOk: each entry's drawn field elements one more: it rejects. The bent copies:
Bends.lean. The test's yes at the unbent term: Bats.lean.
Limits. One bend. The clause on the entry's form rejects it; sizes, radius and list are not reached:
this shows that the test can reject, and no more. Nothing on soundness.
-/
import Johnson.AtFull.ProofPlan.Every.Bends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofPlan.Every
open Johnson.Bridge.OkNat

set_option maxRecDepth 1000000 in
theorem bats_no :
    batsOk MWdraw = false := by
  decide +kernel

end Johnson.AtFull.ProofPlan.Every

#print axioms Johnson.AtFull.ProofPlan.Every.bats_no
