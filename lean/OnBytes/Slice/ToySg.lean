-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ToySg.lean: the three stages of the proximity test at the small test configuration
(OnBytes/Slice/README.md, "More terms").

OnBytes/Slice/Stage.lean writes a stage's number of row variables as h + g. This file has the three
stages in that form.

Main definitions: `toySg1`, `toySg2`, `toySg3`.


Not claimed. Nothing on the codes of these stages: their distances are in
OnBytes/Slice/Numbers.lean.
-/
import Fmt.M3Items
import Fmt.M3Dec
import Fmt.ParamsRead
import Fmt.Rules5Fast
import OnBytes.Slice.Stage

set_option autoImplicit false

namespace OnBytes.Slice

/-- The first stage: three row variables, no mask variable, 63 positions. -/
def toySg1 : Sg := ⟨⟨13, 512, 63⟩, ⟨13, 16, 63⟩, 0, 3, 63⟩

/-- The second stage: two row variables, one of them a mask variable, 43 positions. -/
def toySg2 : Sg := ⟨⟨13, 128, 43⟩, ⟨13, 128, 43⟩, 1, 1, 43⟩

/-- The third stage: no row variable, 41 positions. -/
def toySg3 : Sg := ⟨⟨15, 128, 41⟩, ⟨15, 512, 41⟩, 0, 0, 41⟩

end OnBytes.Slice

