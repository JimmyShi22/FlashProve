-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/EntryWireK.lean: the number of blocks of a verifier's message at the two settings, as
numbers, by evaluation in Lean's kernel (`XD.K`, Run/PlanQXRun.lean: the greatest number over the
rounds; the wire has one block more).

-/
import OnBytes.Slice.EntryWireNums

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Run _root_.Run.PQ

/-- The description's number of blocks at the small files is 99. -/
theorem sr_K : srD.K = 99 := by decide +kernel

/-- The description's number of blocks at the full size is 140. -/
theorem fr_K : frD.K = 140 := by decide +kernel

end OnBytes.Slice
