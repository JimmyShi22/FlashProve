-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/Every/NoSends.lean: A NEGATIVE TEST, BY LEAN's KERNEL, ALONE IN ITS FILE:
THE TEST CAN FAIL: sendsOk: the bound on the lists one lower: the letter is tight: it rejects. The
bent copies: Bends.lean. The test's yes at the unbent term: Sends.lean.
Limits. One bend. Nothing on soundness.

-/
import Johnson.AtFull.ProofPlan.Every.Bends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofPlan.Every
open Johnson.Bridge.OkNat

set_option maxRecDepth 1000000 in
theorem sends_no :
    sendsOk (topW - 1) MW = false := by
  decide +kernel

end Johnson.AtFull.ProofPlan.Every

#print axioms Johnson.AtFull.ProofPlan.Every.sends_no
