-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Omega.lean: the stages of Omega's test of a key of full size are what the
planner's routines solve: the turns of the files beside, joined by the laws on the
iterations (OnBytes/Params/SolveSteps.lean, SizedForward.lean).

Main names.
  keyO2_solved, keyO3_solved, keyO4_solved, keyO_later, keyO_stages.

Limits. No evaluation of weight is made here. Closed statements at the typed values alone. That the
first group is what the sizing of a key solves is not said here (see
OnBytes/Params/KeyRec/Once.lean). That a round which holds in the planner's reckoning has a small
error is not said: under the rule johnson the planner prices a closeness round by an assumed
theorem. Nothing on soundness. For proofs only; the program does not import this file.

-/
import OnBytes.Params.KeyRec.Omega2
import OnBytes.Params.KeyRec.Omega3
import OnBytes.Params.KeyRec.Omega4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace OnBytes.Params

/-- Stage 2 as it is solved. -/
theorem keyO2_solved : solveStageFrom recordSet .once keyO1.main.r
    (laterShape recordSet keyO1 ⟨4, 3, 18, 14⟩) 32 0 = some ⟨keyO2, 49⟩ := by
  rw [keyO2_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ keyO2_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 49 _ _ keyO2_turn2))

/-- Stage 3 as it is solved. -/
theorem keyO3_solved : solveStageFrom recordSet .once keyO2.main.r
    (laterShape recordSet keyO2 ⟨4, 3, 14, 13⟩) 32 0 = some ⟨keyO3, 49⟩ := by
  rw [keyO3_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ keyO3_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 49 _ _ keyO3_turn2))

/-- Stage 4 as it is solved. -/
theorem keyO4_solved : solveStageFrom recordSet .once keyO3.main.r
    (laterShape recordSet keyO3 ⟨0, 0, 15, 15⟩) 32 0 = some ⟨keyO4, 39⟩ := by
  rw [keyO4_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ keyO4_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 39 _ _ keyO4_turn2))

/-- The later stages follow from the first group, one step of `solveLater` after the other. -/
theorem keyO_later : solveLater recordSet .once keyO1
    [⟨4, 3, 18, 14⟩, ⟨4, 3, 14, 13⟩, ⟨0, 0, 15, 15⟩] = some keyOStages.tail := by
  rw [solveLater_step (by decide) keyO2_solved, solveLater_step (by decide) keyO3_solved,
    solveLater_step (by decide) keyO4_solved]
  decide

/-- **The stages of the test on Omega's group.** -/
theorem keyO_stages : solveStages recordSet .once keyO1 49 recordLines.onceOmega.stages
    = some keyOStages :=
  solveStages_of (by decide) keyO_later

end OnBytes.Params

#print axioms OnBytes.Params.keyO_later
#print axioms OnBytes.Params.keyO_stages
