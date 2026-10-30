-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5FrontNamed.lean: NO RUN OF THE DRY RUNS' FIRST WRITTEN LIST BEARS THE
NAME
`Fmt.recordName`, which `Fmt.Plan.rounds` (Fmt/Rules4.lean) leaves out of a plan's entries. One
decision of Lean's kernel over 17,108 runs.
Limits. The full size alone. A closed fact. Nothing on soundness. On hiding nothing.

-/
import Johnson.Desc.First.Att.Row.K5FrontSameDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row

set_option maxRecDepth 1000000 in
/-- No run bears the name that a plan's rounds leave out. -/
theorem named_written : (runsD.all fun x => x.2.name != Fmt.recordName) = true := by decide +kernel

end H2K5.Row

#print axioms H2K5.Row.named_written
