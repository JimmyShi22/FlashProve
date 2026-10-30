-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SwitchRowsOfSized.lean: WHERE THE PLANNER's SIZES OF A PROOF's CHAINS ARE THE WRITTEN
VALUE `proofSizedFull` (Johnson/Desc/Ok/PlanWritten/SizedLit.lean), the record of the code switch
that `rowOf` makes of them and of the planner's record of a group is the written record of that
switch, at each of the 25, with all that follows (`RowsWritten`, Johnson/G/SwitchRowsAtScope.lean).
NO PREMISE ON THE LAYOUT FILE.

Why. `rows_of_eight` asks eight equations on fields of the sizes. At the written value the eight are
closed facts on written values, each said by Lean's kernel in three other files: seven fields in
Johnson/Goal/Numbers/ProofSizesOfWritten.lean (`seven_of_sized`), the codes in
Johnson/Desc/Ok/PlanWritten/SizedTestLaws.lean (`codes_written`), the last test's stages in
Johnson/Desc/K12/Law/Sizes/WrittenIsTyped.lean (`last_written`).
  `rows_of_sized`: the first sentence above.
  `rows_written_full`: at the written value itself: no premise.
  `frames_some_full`: there neither list is short: that statement is idle at none of the 25.
  `rows_of_pinnedAt`: where the test `sizedPinnedAt` says yes at what the planner has made and the
  scan's key is the full size's: by `sized_of_pinnedAt`.
Limits. That a description asks that test, and that in scope the scan's key is the full size's at
the record of which the seated blocks' numbers are made, is not shown here. sub is a free letter.
lo, l and kept are laid as the written record's. All written values come of prints of one planner.
Nothing on the running text of a block; nothing on soundness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.G.SwitchRowsAtScope
import Johnson.Goal.Numbers.ProofSizesOfWritten
import Johnson.Desc.Ok.PlanWritten.SizedTestLaws
import Johnson.Desc.K12.Law.Sizes.WrittenIsTyped

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Params OnBytes.Plan
open VerifiableInference.PlanWritten

/- Lean compares this name and does not open it. -/
attribute [local irreducible] proofSizedFull

/-- **WHERE THE SIZES ARE THE WRITTEN VALUE.** -/
theorem rows_of_sized {z : ProofSized} (h : z = proofSizedFull) (sub : Subproofs) :
    RowsWritten z sub := by
  obtain ⟨e1, -, e5, e6, e7, e8, e9⟩ := VerifierAndGoals.Sizes.seven_of_sized h
  exact rows_of_eight z sub e1 (by rw [h]; exact codes_written)
    (by rw [h]; exact H2K.Sizes.last_written) e5 e6 e7 e8 e9

/-- At the written value itself. -/
theorem rows_written_full (sub : Subproofs) : RowsWritten proofSizedFull sub :=
  rows_of_sized rfl sub

/-- **It is idle at none of the 25**: at the written value the planner's list has a record, and the
written table one, at each switch. -/
theorem frames_some_full (sub : Subproofs) :
    ∀ i, i < 25 → ∃ f R, (framesOf proofSizedFull sub)[i + 1]? = some f ∧
      VerifiableInference.Desc.First.K2Caller.tableFullLit[i]? = some R := by
  obtain ⟨-, -, e5, e6, e7, e8, e9⟩ := VerifierAndGoals.Sizes.seven_of_sized (z := proofSizedFull) rfl
  exact frames_some proofSizedFull sub e6 e7 e8 e9 (by rw [e5]) H2K.Sizes.last_written

/-- **Where the test on the sizing says yes** at what the planner has made, and the scan's key is
the full size's. -/
theorem rows_of_pinnedAt {P : OnBytes.Model.PolScan} {made : Configured}
    (h : sizedPinnedAt P made = true) (hk : keyOfScan P = fullKey) (sub : Subproofs) :
    RowsWritten made.sized.proof sub :=
  rows_of_sized (sized_of_pinnedAt h hk) sub

end Johnson.G

#print axioms Johnson.G.rows_of_sized
#print axioms Johnson.G.rows_written_full
#print axioms Johnson.G.frames_some_full
#print axioms Johnson.G.rows_of_pinnedAt
