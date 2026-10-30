-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Plan/TestPlanSizesFull.lean: the tests of OnBytes/Tie/Pv/Plan/TestPlanSizes.lean at
the full-size example, and the lengths of that example's three files as they are written out here.

Limits: a line "#guard" is evaluated by Lean's interpreter when this file is compiled. It is no
theorem, and it says nothing of other files. The program does not import this file.

-/
import OnBytes.Tie.Pv.Plan.TestPlanSizes
import OnBytes.Tie.Pv.Plan.PlanLayoutFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Plan

-- the files' lengths
#guard ((textOf policyF).size, (wordsFile scalesF).size, layoutF.utf8ByteSize) ==
  (2629, 2784, 224975)

-- the five tests
#guard tests true (textOf policyF) (wordsFile scalesF) layoutF.toUTF8 matches
  .ok [true, true, true, true, true]

end OnBytes.Tie.Pv.Plan
