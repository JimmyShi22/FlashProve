-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/K5/G5.lean: the head's example: ONE CLOSED FACT BY LEAN's KERNEL: at the attention's
plan of group 5, as publicOfO lays it into its value at the stored full-size files (`atOwn`), the
test `k5Q3` accepts (Johnson/AtFull/K5/AtOwn.lean): 162 rounds · planOkOwn · claimsOkAtQ.

Limits. Two limits are raised in this file (maxRecDepth 1000000; maxHeartbeats 4000000 at the
theorem). The fourth part of the lot's test at a plan, the test on the padding keys, is not here.
Nothing on soundness.
-/
import Johnson.AtFull.K5.AtOwn

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.K5

set_option maxHeartbeats 4000000 in
theorem g5 : atOwn 5 k5Q3 = true := by decide +kernel

end Johnson.AtFull.K5

#print axioms Johnson.AtFull.K5.g5
