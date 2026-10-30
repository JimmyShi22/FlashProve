-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/KeyRowsFirst.lean: ONE CLOSED FACT OF
r5, ALONE IN ITS FILE, DECIDED BY LEAN's KERNEL, with a bent twin that must say false: the first
chain's 19 rows (place, number of rounds) at the typed sizes keyFull, the two lookups' numbers of
rounds off the plain lists (Johnson.KB8.lookList: 9,581 and 9,220 rounds), ARE THE WRITTEN LIST W₁
(Johnson/RunOne/Sound/KeyPlacesInScope.lean). firstRowsOf: IMR/KeyRows.lean. No soundness.

-/
import Johnson.IMR.KeyRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open Johnson.KB8
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Sound (W₁)

set_option maxRecDepth 1000000 in
theorem first_rows_list : firstRowsOf (fun x => (lookList keyFull.set x).length) keyFull.ranges.x
    keyFull.once.shape keyFull.once.input keyFull.codes rsR.length = W₁ := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: with one round more at the ranges' test the comparison says no. -/
theorem first_rows_bent : ¬ firstRowsOf (fun x => (lookList keyFull.set x).length)
    keyFull.ranges.x keyFull.once.shape keyFull.once.input keyFull.codes (rsR.length + 1) = W₁ := by
  decide +kernel

end IM

#print axioms IM.first_rows_list
#print axioms IM.first_rows_bent
