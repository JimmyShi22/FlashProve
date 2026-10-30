-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/LinShapeCaps.lean: three numbers of the shape of the test on the table are small
where the shape passes its own test.

"LinShape.ok" (OnBytes/Iop/Lin.lean) tests, among other things, kLo ≤ 30, kRow ≤ 30 and
kCol ≤ 60. kRow is the rounded-up logarithm of the matrix's number of rows, which no line of the
parameter file says: its bound comes from this test.

Main theorem: linShape_caps.

Limits. The other clauses of the test are not drawn. That a shape passes the test is a premise here:
"sized" (OnBytes/Params/Configure.lean) runs linOk, which holds this test, on the shapes of a
proof's and of a key's test on the table ("sized_tests", "linOk_ok",
OnBytes/Params/Fit/TreesSized.lean). The program does not import this file.


-/
import OnBytes.Iop.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

/-- **Three numbers of a shape that passes its own test.** -/
theorem linShape_caps {S : LinShape} (h : S.ok = true) :
    S.kLo ≤ 30 ∧ S.kRow ≤ 30 ∧ S.kCol ≤ 60 := by
  unfold LinShape.ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.1.2⟩

end OnBytes.Params

#print axioms OnBytes.Params.linShape_caps
