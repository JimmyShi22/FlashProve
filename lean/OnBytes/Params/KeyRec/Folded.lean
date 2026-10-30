-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Folded.lean: the stages of the folded row's test of a key of full size are
what the planner's routines solve: the turns of the files beside, joined by the laws on the
iterations (OnBytes/Params/SolveSteps.lean, SizedForward.lean).

Main names.
  keyU2_solved, keyU3_solved, keyU4_solved, keyU5_solved, keyU_later, keyU_stages.

Limits. No evaluation of weight is made here. Closed statements at the typed values alone. That the
first group is what the sizing of a key solves is not said here (see
OnBytes/Params/KeyRec/Once.lean). That a round which holds in the planner's reckoning has a small
error is not said: under the rule johnson the planner prices a closeness round by an assumed
theorem. Nothing on soundness. For proofs only; the program does not import this file.

-/
import OnBytes.Params.KeyRec.Folded2
import OnBytes.Params.KeyRec.Folded3
import OnBytes.Params.KeyRec.Folded4
import OnBytes.Params.KeyRec.Folded5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace OnBytes.Params

/-- Stage 2 as it is solved. -/
theorem keyU2_solved : solveStageFrom recordSet .once keyU1.main.r
    (laterShape recordSet keyU1 ⟨5, 2, 21, 12⟩) 32 0 = some ⟨keyU2, 52⟩ := by
  rw [keyU2_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ keyU2_turn1).trans
    ((solveStageFrom_more _ _ _ _ 30 49 _ _ keyU2_turn2).trans
    ((solveStageFrom_settled _ _ _ _ 29 52 _ _ keyU2_turn3)))

/-- Stage 3 as it is solved. -/
theorem keyU3_solved : solveStageFrom recordSet .once keyU2.main.r
    (laterShape recordSet keyU2 ⟨4, 2, 17, 12⟩) 32 0 = some ⟨keyU3, 52⟩ := by
  rw [keyU3_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ keyU3_turn1).trans
    ((solveStageFrom_more _ _ _ _ 30 49 _ _ keyU3_turn2).trans
    ((solveStageFrom_settled _ _ _ _ 29 52 _ _ keyU3_turn3)))

/-- Stage 4 as it is solved. -/
theorem keyU4_solved : solveStageFrom recordSet .once keyU3.main.r
    (laterShape recordSet keyU3 ⟨4, 2, 13, 12⟩) 32 0 = some ⟨keyU4, 52⟩ := by
  rw [keyU4_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ keyU4_turn1).trans
    ((solveStageFrom_more _ _ _ _ 30 49 _ _ keyU4_turn2).trans
    ((solveStageFrom_settled _ _ _ _ 29 52 _ _ keyU4_turn3)))

/-- Stage 5 as it is solved. -/
theorem keyU5_solved : solveStageFrom recordSet .once keyU4.main.r
    (laterShape recordSet keyU4 ⟨0, 0, 14, 14⟩) 32 0 = some ⟨keyU5, 49⟩ := by
  rw [keyU5_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ keyU5_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 49 _ _ keyU5_turn2))

/-- The later stages follow from the first group, one step of `solveLater` after the other. -/
theorem keyU_later : solveLater recordSet .once keyU1
    [⟨5, 2, 21, 12⟩, ⟨4, 2, 17, 12⟩, ⟨4, 2, 13, 12⟩, ⟨0, 0, 14, 14⟩] = some keyUStages.tail := by
  rw [solveLater_step (by decide) keyU2_solved, solveLater_step (by decide) keyU3_solved,
    solveLater_step (by decide) keyU4_solved, solveLater_step (by decide) keyU5_solved]
  decide

/-- **The stages of the test on the folded row's group.** -/
theorem keyU_stages : solveStages recordSet .once keyU1 97 recordLines.onceFolded.stages
    = some keyUStages :=
  solveStages_of (by decide) keyU_later

end OnBytes.Params

#print axioms OnBytes.Params.keyU_later
#print axioms OnBytes.Params.keyU_stages
