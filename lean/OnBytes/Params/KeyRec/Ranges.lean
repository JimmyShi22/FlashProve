-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Ranges.lean: the stages of the ranges' test of a key of full size are what the
planner's routines solve: the turns of the files beside, joined by the laws on the
iterations (OnBytes/Params/SolveSteps.lean, SizedForward.lean).

Main names.
  keyR2_solved, keyR3_solved, keyR4_solved, keyR_later, keyR_stages, keyR1_solved, keyR_test.

Limits. No evaluation of weight is made here. Closed statements at the typed values alone. That the
typed load and shape are those of the sizing of a key is not said here (see
Johnson/Goal/PlanValues/KeySizesAtPlan.lean). That a round which holds in the planner's reckoning
has a small error is not said: under the rule johnson the planner prices a closeness round by an
assumed theorem. Nothing on soundness. For proofs only; the program does not import this file.

-/
import OnBytes.Params.KeyRec.Ranges1
import OnBytes.Params.KeyRec.Ranges2
import OnBytes.Params.KeyRec.Ranges3
import OnBytes.Params.KeyRec.Ranges4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace OnBytes.Params

/-- Stage 2 as it is solved. -/
theorem keyR2_solved : solveStageFrom recordSet .once keyR1.main.r
    (laterShape recordSet keyR1 ⟨4, 3, 19, 17⟩) 32 0 = some ⟨keyR2, 39⟩ := by
  rw [keyR2_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ keyR2_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 39 _ _ keyR2_turn2))

/-- Stage 3 as it is solved. -/
theorem keyR3_solved : solveStageFrom recordSet .once keyR2.main.r
    (laterShape recordSet keyR2 ⟨3, 3, 17, 17⟩) 32 0 = some ⟨keyR3, 33⟩ := by
  rw [keyR3_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ keyR3_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 33 _ _ keyR3_turn2))

/-- Stage 4 as it is solved. -/
theorem keyR4_solved : solveStageFrom recordSet .once keyR3.main.r
    (laterShape recordSet keyR3 ⟨0, 0, 20, 20⟩) 32 0 = some ⟨keyR4, 25⟩ := by
  rw [keyR4_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ keyR4_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 25 _ _ keyR4_turn2))

/-- The later stages follow from the first group, one step of `solveLater` after the other. -/
theorem keyR_later : solveLater recordSet .once keyR1
    [⟨4, 3, 19, 17⟩, ⟨3, 3, 17, 17⟩, ⟨0, 0, 20, 20⟩] = some keyRStages.tail := by
  rw [solveLater_step (by decide) keyR2_solved, solveLater_step (by decide) keyR3_solved,
    solveLater_step (by decide) keyR4_solved]
  decide

/-- **The stages of the test on the group of the multiplicities.** -/
theorem keyR_stages : solveStages recordSet .once keyR1 49 recordLines.onceRanges.stages
    = some keyRStages :=
  solveStages_of (by decide) keyR_later

/-- The first group as it is solved. -/
theorem keyR1_solved : solveGroup recordSet .once ⟨23, 1, 981⟩ id keyRShape1 =
    some ⟨keyR1, 49⟩ := by
  unfold solveGroup
  exact (solveGroupFrom_more _ _ _ _ _ 31 0 _ _ keyR1_turn1).trans
    ((solveGroupFrom_settled _ _ _ _ _ 30 49 _ _ keyR1_turn2 rfl))

/-- **The test of the proof of the ranges as it is solved**, at the typed load and shape. -/
theorem keyR_test : solveTest recordSet .once recordLines.onceRanges ⟨23, 1, 981⟩ id keyRShape1 =
    some ⟨keyR1, 49, keyRStages⟩ :=
  solveTest_of (x := ⟨keyR1, 49⟩) keyR1_solved keyR_stages

end OnBytes.Params

#print axioms OnBytes.Params.keyR_later
#print axioms OnBytes.Params.keyR_stages
#print axioms OnBytes.Params.keyR1_solved
#print axioms OnBytes.Params.keyR_test
