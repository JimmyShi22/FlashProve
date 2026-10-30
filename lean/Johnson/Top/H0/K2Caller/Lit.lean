-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/Lit.lean: the records of Row.lean at the switches of a proof's first chain,
written out for both examples, 5 and 25; Lean's kernel evaluates the test at each different one: it
says yes; so the promise of Row.lean holds at each.

The records stand in LitRows.lean, the evaluations in LitSmall.lean and LitFull.lean; this file
joins them, so that whoever imports it has all their names.
  k02_small, k02_full: K02At at the two lists
That the test can say no at these records is LitCanFail.lean's and LitCanFailFull.lean's.
Limits: those of LitRows.lean and Row.lean: the theorems speak of written numbers. Nothing on
soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.LitSmall
import Johnson.Top.H0.K2Caller.LitFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller

/-- **The promise at the 5 switches of the small example.** -/
theorem k02_small : K02At tableSmallLit := k02At _ tableSmallLit_ok

/-- **The promise at the 25 switches of the full example.** -/
theorem k02_full : K02At tableFullLit := k02At _ tableFullLit_ok

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.tableSmallLit_ok
#print axioms VerifiableInference.Desc.First.K2Caller.tableFullLit_ok
#print axioms VerifiableInference.Desc.First.K2Caller.k02_small
#print axioms VerifiableInference.Desc.First.K2Caller.k02_full
