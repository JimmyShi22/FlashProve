-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/Every/LenEntries.lean: ONE CLOSED FACT BY LEAN's KERNEL: NOT IDLE: the five
later plans' numbers of entries: no rowsOk runs over an empty list, at the joined written term
(MW.lean). Why: a test that says «all» over an empty list accepts for nothing.
Limits. A count. Nothing on soundness.

-/
import Johnson.AtFull.ProofPlan.Every.MW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofPlan.Every
open Johnson.Bridge.OkNat

set_option maxRecDepth 1000000 in
theorem len_entries :
    ((entriesAt MW.proof 1).length, (entriesAt MW.proof 2).length, (entriesAt MW.key 1).length,
      (entriesAt MW.key 2).length, MW.entry.plan.entries.length) = (68, 30, 68, 30, 42) := by
  decide +kernel

end Johnson.AtFull.ProofPlan.Every

#print axioms Johnson.AtFull.ProofPlan.Every.len_entries
