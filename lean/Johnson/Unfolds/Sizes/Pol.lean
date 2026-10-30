-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Sizes/Pol.lean: a closed fact by Lean's kernel, alone in its file: the size of the
stored full-size example's parameter file (`VerifierAndGoals.storedPublicFiles`, Ladder/Stored.lean). Ladder/Guards.lean
has the number in a `#guard`, by the evaluator.

-/
import Ladder.Stored

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds

theorem size_pol : VerifierAndGoals.storedPublicFiles.pol.size = 2629 := by
  decide +kernel

end Johnson.Unfolds

#print axioms Johnson.Unfolds.size_pol
