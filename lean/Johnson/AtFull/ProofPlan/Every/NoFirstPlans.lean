-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/Every/NoFirstPlans.lean: A NEGATIVE TEST, BY LEAN's KERNEL, ALONE IN ITS
FILE: THE TEST CAN FAIL: firstPlansOk: each entry's rows one higher: it rejects. The bent copies:
Bends.lean. The test's yes at the unbent term: FirstPlans.lean.
Limits. One bend. The bent input is rejected by one clause of the test at every value: this shows
that the test can reject, and no more. Nothing on soundness.
-/
import Johnson.AtFull.ProofPlan.Every.Bends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofPlan.Every
open Johnson.Bridge.OkNat

set_option maxRecDepth 1000000 in
theorem firstPlans_no :
    Johnson.Desc.Ok.firstPlansOk MWrows = false := by
  decide +kernel

end Johnson.AtFull.ProofPlan.Every

#print axioms Johnson.AtFull.ProofPlan.Every.firstPlans_no
