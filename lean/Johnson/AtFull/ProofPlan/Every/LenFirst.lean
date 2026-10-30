-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/Every/LenFirst.lean: ONE CLOSED FACT BY LEAN's KERNEL: NOT IDLE: the two
first plans have entries: firstPlansOk's rulesOk runs over no empty list (their lengths, some 48 and
19 thousand by the evaluator, are not counted here: the count overflowed Lean's stack), at the
joined written term (MW.lean). Why: a test that says «all» over an empty list accepts for nothing.
Limits. A count. Nothing on soundness.

-/
import Johnson.AtFull.ProofPlan.Every.MW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofPlan.Every
open Johnson.Bridge.OkNat

set_option maxRecDepth 1000000 in
theorem len_first :
    ((entriesAt MW.proof 0).isEmpty, (entriesAt MW.key 0).isEmpty) = (false, false) := by
  decide +kernel

end Johnson.AtFull.ProofPlan.Every

#print axioms Johnson.AtFull.ProofPlan.Every.len_first
