-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/Every/LenPoints.lean: ONE CLOSED FACT BY LEAN's KERNEL: NOT IDLE: the list
of points over whose first bearsAt says «all», and over which pointsOk runs, has two members, at the
joined written term (MW.lean). Why: a test that says «all» over an empty list accepts for nothing.
Limits. A count. Nothing on soundness.

-/
import Johnson.AtFull.ProofPlan.Every.MW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofPlan.Every
open Johnson.Bridge.OkNat

set_option maxRecDepth 1000000 in
theorem len_points :
    (planPoints radW MW).length = 2 := by
  decide +kernel

end Johnson.AtFull.ProofPlan.Every

#print axioms Johnson.AtFull.ProofPlan.Every.len_points
