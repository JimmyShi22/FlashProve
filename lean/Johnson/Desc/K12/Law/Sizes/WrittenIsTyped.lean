-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/WrittenIsTyped.lean: two written values agree: in the written sizes of a
proof's chains at the full size (`proofSizedFull`, Johnson/Desc/Ok/PlanWritten/SizedLit.lean) the
stages of the four proximity tests and the setting are the typed lists and the typed setting of
Johnson/Desc/K12/Law/Sizes/StagesFull.lean. Five closed statements, each by an evaluation in Lean's
kernel. No definition.

Why. Laws on the proximity test's four places are stated at the typed lists (`szLFull`, `szUFull`,
`szOFull`, `szWFull`) and the typed setting (`setAt`). A test that holds what the planner sized for
a proof against `proofSizedFull`, whole, gives with these five the premises of those laws; above
all `last_written`: the stages of the first chain's last test, which otherwise stand under a closed
premise (`LayoutGroupsAre`, LastAtScope.lean; proved in AtFullSide/LayoutRead/GroupsPaid.lean).
Main names: `last_written`, `folded_written`, `omega_written`, `own_written`, `set_written`.
Limits. Two written values are compared: nothing says that the planner makes either at any files.
The two were laid by two programs from prints of one planner: their agreement is no second witness.
No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.Desc.K12.Law.Sizes.StagesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Sizes
open VerifiableInference.PlanWritten (proofSizedFull)
open H2K.Member (szLFull szUFull szOFull szWFull setAt)

/-- **The stages of the first chain's last test.** -/
theorem last_written : proofSizedFull.last.stages = szLFull := by decide +kernel

/-- The stages of the folded row's test. -/
theorem folded_written : proofSizedFull.batch.folded.stages = szUFull := by decide +kernel

/-- The stages of Omega's test. -/
theorem omega_written : proofSizedFull.batch.omega.stages = szOFull := by decide +kernel

/-- The stages of the request's own test. -/
theorem own_written : proofSizedFull.batch.own.stages = szWFull := by decide +kernel

/-- The setting. -/
theorem set_written : proofSizedFull.set = setAt := by decide +kernel

end H2K.Sizes

#print axioms H2K.Sizes.last_written
#print axioms H2K.Sizes.folded_written
#print axioms H2K.Sizes.omega_written
#print axioms H2K.Sizes.own_written
#print axioms H2K.Sizes.set_written
