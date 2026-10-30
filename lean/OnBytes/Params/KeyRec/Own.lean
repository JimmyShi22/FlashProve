-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Own.lean: the stages of the own test of a key of full size are what the
planner's routines solve: the turns of the files beside, joined by the laws on the
iterations (OnBytes/Params/SolveSteps.lean, SizedForward.lean).

Main names.
  keyW2_solved, keyW3_solved, keyW4_solved, keyW5_solved, keyW_later, keyW_stages.

Limits. No evaluation of weight is made here. Closed statements at the typed values alone. That the
first group is what the sizing of a key solves is not said here (see
OnBytes/Params/KeyRec/Once.lean). That a round which holds in the planner's reckoning has a small
error is not said: under the rule johnson the planner prices a closeness round by an assumed
theorem. Nothing on soundness. For proofs only; the program does not import this file.

-/
import OnBytes.Params.KeyRec.Own2
import OnBytes.Params.KeyRec.Own3
import OnBytes.Params.KeyRec.Own4
import OnBytes.Params.KeyRec.Own5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace OnBytes.Params

/-- Stage 2 as it is solved. -/
theorem keyW2_solved : solveStageFrom recordSet .once keyW1.main.r
    (laterShape recordSet keyW1 ⟨4, 3, 18, 15⟩) 32 0 = some ⟨keyW2, 49⟩ := by
  rw [keyW2_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ keyW2_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 49 _ _ keyW2_turn2))

/-- Stage 3 as it is solved. -/
theorem keyW3_solved : solveStageFrom recordSet .once keyW2.main.r
    (laterShape recordSet keyW2 ⟨3, 3, 15, 14⟩) 32 0 = some ⟨keyW3, 49⟩ := by
  rw [keyW3_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ keyW3_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 49 _ _ keyW3_turn2))

/-- Stage 4 as it is solved. -/
theorem keyW4_solved : solveStageFrom recordSet .once keyW3.main.r
    (laterShape recordSet keyW3 ⟨3, 3, 13, 13⟩) 32 0 = some ⟨keyW4, 41⟩ := by
  rw [keyW4_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ keyW4_turn1).trans
    ((solveStageFrom_more _ _ _ _ 30 39 _ _ keyW4_turn2).trans
    ((solveStageFrom_settled _ _ _ _ 29 41 _ _ keyW4_turn3)))

/-- Stage 5 as it is solved. -/
theorem keyW5_solved : solveStageFrom recordSet .once keyW4.main.r
    (laterShape recordSet keyW4 ⟨0, 0, 15, 15⟩) 32 0 = some ⟨keyW5, 29⟩ := by
  rw [keyW5_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ keyW5_turn1).trans
    ((solveStageFrom_more _ _ _ _ 30 28 _ _ keyW5_turn2).trans
    ((solveStageFrom_settled _ _ _ _ 29 29 _ _ keyW5_turn3)))

/-- The later stages follow from the first group, one step of `solveLater` after the other. -/
theorem keyW_later : solveLater recordSet .once keyW1
    [⟨4, 3, 18, 15⟩, ⟨3, 3, 15, 14⟩, ⟨3, 3, 13, 13⟩, ⟨0, 0, 15, 15⟩] = some keyWStages.tail := by
  rw [solveLater_step (by decide) keyW2_solved, solveLater_step (by decide) keyW3_solved,
    solveLater_step (by decide) keyW4_solved, solveLater_step (by decide) keyW5_solved]
  decide

/-- **The stages of the test on the own group.** -/
theorem keyW_stages : solveStages recordSet .once keyW1 49 recordLines.onceOwn.stages
    = some keyWStages :=
  solveStages_of (by decide) keyW_later

end OnBytes.Params

#print axioms OnBytes.Params.keyW_later
#print axioms OnBytes.Params.keyW_stages
