-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/KeyRowsLater.lean: TWO SMALL CLOSED FACTS OF r5, DECIDED BY LEAN's KERNEL, the first
with a bent twin that must say false: the shared chain's 12 rows at the typed sizes keyFull are the
written list W₂ (Johnson/RunOne/Sound/KeyPlacesInScope.lean); the written list of the last chain's
declared rounds (Johnson.KB8.declKeyFull.2.2) has 30 members. (That these 30 are the proximity
test's own rounds, and that the last chain's three other sub-protocols have none, is not said here:
Johnson.KB8.third_full and IMR/KeyRows.lean's third_rows say it.) sharedRowsOf: IMR/KeyRows.lean.
No soundness.
-/
import Johnson.IMR.KeyRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open Johnson.KB8
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Sound (W₂)

set_option maxRecDepth 1000000 in
theorem shared_rows_list : sharedRowsOf keyFull rsU.length [rsO.length] = W₂ := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: with the two tests' numbers exchanged the comparison says no. -/
theorem shared_rows_bent : ¬ sharedRowsOf keyFull rsO.length [rsU.length] = W₂ := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem third_len : declKeyFull.2.2.length = 30 := by decide +kernel

end IM

#print axioms IM.shared_rows_list
#print axioms IM.shared_rows_bent
#print axioms IM.third_len
