-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstFive.lean: THE NAMED TEST "five" BESIDE THE SHARED TABLE's CONSTANT
(Sh.testsO, Johnson/Desc/K14/Law/SharedConstTests.lean: the one numbering gives five numbers to W,
the index masks, o_u, o_omega and o_sp) IS THE TEST THAT THE LIBRARY's WALK EVALUATES: P5T.harrB at
the five names (Johnson/Desc/K14/Law/LedgerFiveApartOwed.lean): ONE Bool, by unfolding. So that
walk's accept pays the constant's row.

  Sh.five_is_harrB    the equation
What is not claimed. That the test accepts. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstTests
import Johnson.Desc.K14.Law.LedgerFiveApartOwed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Sh

variable {Xi P₀ P₁ Cells Tok : Type} (A : ShPlan Xi) (O : ShOpen P₀ P₁ Cells Tok A.Q)

/-- **One Bool.** -/
theorem five_is_harrB :
    P5T.harrB O.arr (fiveTen (nums A O)) fiveAll = decide (fiveNums A O).Nodup := rfl

end Desc.K14.Law.Sh

#print axioms Desc.K14.Law.Sh.five_is_harrB
