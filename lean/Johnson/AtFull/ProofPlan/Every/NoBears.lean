-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/Every/NoBears.lean: A NEGATIVE TEST, BY LEAN's KERNEL, ALONE IN ITS FILE:
THE TEST CAN FAIL: bearsAt: the most requests in a batch set to 2 ^ 64 (no bend of the radius or of
an entry that was tried fells it: at 64 requests it has much room): it rejects. The bent copies:
Bends.lean. The test's yes at the unbent term: Bears.lean.
Limits. One bend. At 2 ^ 64 requests one term of the comparison is too large wherever v + klo >= 1:
this shows that the test can reject, and no more. Nothing on soundness.
-/
import Johnson.AtFull.ProofPlan.Every.Bends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofPlan.Every
open Johnson.Bridge.OkNat

set_option maxRecDepth 1000000 in
theorem bears_no :
    bearsAt radW MWreq = false := by
  decide +kernel

end Johnson.AtFull.ProofPlan.Every

#print axioms Johnson.AtFull.ProofPlan.Every.bears_no
