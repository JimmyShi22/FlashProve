-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/TurnsOFull.lean: at the lines typed for the full-size parameter file
(Params.recordLines), the stages of Omega's test in a proof file's chains are the typed list
szOFull, each stage by evaluations of the planner in Lean's kernel.

The way is that of OnBytes/Params/KeyStagesRecordFolded.lean: every turn of the iteration that
solves a stage has a closed statement of its own, proved by decide +kernel, with the turn's answer
typed; each stage's shape is typed too; the statements are joined by the laws of
OnBytes/Params/SolveSteps.lean and SizedForward.lean. The typed values were printed by Lean's
evaluator and laid in by a program; each is checked by the kernel in its own statement, so none is
taken on trust.
Main names:
  `gO1` and so on: the stages' groups. `O_later`, `O_stages`: the stages.
Limits: that the first group is what the sizing of a proof solves is not said here. That a round
which holds in the planner's reckoning has a small error is not said: under the rule johnson the
planner prices a closeness round by an assumed theorem. Nothing on soundness. Nothing on hiding. For
proofs only; no program imports this file.
-/
import OnBytes.Params.EntryStagesRecord
import Johnson.Desc.K12.Law.Sizes.StagesFull

set_option autoImplicit false

namespace H2K.Sizes
open OnBytes.Params H2K.Member

/-- The group of stage 1 of Omega's test. -/
def gO1 : GroupSize :=
  ⟨⟨22, 262144, 3571, true⟩, ⟨13, 64, 152, true⟩, 4, 0, 1, .johnson, 159⟩

/-- The group of stage 2. -/
def gO2 : GroupSize :=
  ⟨⟨18, 16384, 51, true⟩, ⟨14, 512, 51, true⟩, 4, 3, 1, .johnson, 277⟩

/-- The group of stage 3. -/
def gO3 : GroupSize :=
  ⟨⟨14, 1024, 51, true⟩, ⟨13, 256, 51, true⟩, 4, 3, 1, .johnson, 489⟩

/-- The group of stage 4. -/
def gO4 : GroupSize :=
  ⟨⟨15, 1024, 41, true⟩, ⟨15, 1024, 41, true⟩, 0, 0, 1, .johnson, 299⟩

/-- The shape from which stage 2 is solved. -/
def shO2 : GroupSize :=
  ⟨⟨18, 16384, 0, true⟩, ⟨14, 512, 0, true⟩, 4, 3, 1, .johnson, 0⟩

/-- It is the shape that laterShape makes. -/
theorem O2_shape : laterShape recordSet gO1 ⟨4, 3, 18, 14⟩ = shO2 := by
  decide +kernel

/-- Turn 1 of stage 2, from 0 positions. -/
theorem O2_turn1 : turn recordSet .shared
    ⟨stageCubeBits shO2, 1, 4 + 3 * max gO1.main.r 1024⟩ shO2
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨18, 16384, 0, true⟩, ⟨14, 512, 0, true⟩, 4, 3, 1, .johnson, 277⟩ 51 := by
  decide +kernel

/-- Turn 2 of stage 2, from 51 positions. -/
theorem O2_turn2 : turn recordSet .shared
    ⟨stageCubeBits shO2, 1, 4 + 3 * max gO1.main.r 1024⟩ shO2
    (tailFor 51) (tailFor 51) 51 =
      .settled gO2 51 := by
  decide +kernel

/-- Stage 2 as it is solved. -/
theorem O2_solved : solveStageFrom recordSet .shared gO1.main.r
    (laterShape recordSet gO1 ⟨4, 3, 18, 14⟩) 32 0 = some ⟨gO2, 51⟩ := by
  rw [O2_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ O2_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 51 _ _ O2_turn2))

/-- The shape from which stage 3 is solved. -/
def shO3 : GroupSize :=
  ⟨⟨14, 1024, 0, true⟩, ⟨13, 256, 0, true⟩, 4, 3, 1, .johnson, 0⟩

/-- It is the shape that laterShape makes. -/
theorem O3_shape : laterShape recordSet gO2 ⟨4, 3, 14, 13⟩ = shO3 := by
  decide +kernel

/-- Turn 1 of stage 3, from 0 positions. -/
theorem O3_turn1 : turn recordSet .shared
    ⟨stageCubeBits shO3, 1, 4 + 3 * max gO2.main.r 1024⟩ shO3
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨14, 1024, 0, true⟩, ⟨13, 256, 0, true⟩, 4, 3, 1, .johnson, 482⟩ 51 := by
  decide +kernel

/-- Turn 2 of stage 3, from 51 positions. -/
theorem O3_turn2 : turn recordSet .shared
    ⟨stageCubeBits shO3, 1, 4 + 3 * max gO2.main.r 1024⟩ shO3
    (tailFor 51) (tailFor 51) 51 =
      .settled gO3 51 := by
  decide +kernel

/-- Stage 3 as it is solved. -/
theorem O3_solved : solveStageFrom recordSet .shared gO2.main.r
    (laterShape recordSet gO2 ⟨4, 3, 14, 13⟩) 32 0 = some ⟨gO3, 51⟩ := by
  rw [O3_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ O3_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 51 _ _ O3_turn2))

/-- The shape from which stage 4 is solved. -/
def shO4 : GroupSize :=
  ⟨⟨15, 1024, 0, true⟩, ⟨15, 1024, 0, true⟩, 0, 0, 1, .johnson, 0⟩

/-- It is the shape that laterShape makes. -/
theorem O4_shape : laterShape recordSet gO3 ⟨0, 0, 15, 15⟩ = shO4 := by
  decide +kernel

/-- Turn 1 of stage 4, from 0 positions. -/
theorem O4_turn1 : turn recordSet .shared
    ⟨stageCubeBits shO4, 1, 4 + 3 * max gO3.main.r 1024⟩ shO4
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨15, 1024, 0, true⟩, ⟨15, 1024, 0, true⟩, 0, 0, 1, .johnson, 296⟩ 41 := by
  decide +kernel

/-- Turn 2 of stage 4, from 41 positions. -/
theorem O4_turn2 : turn recordSet .shared
    ⟨stageCubeBits shO4, 1, 4 + 3 * max gO3.main.r 1024⟩ shO4
    (tailFor 41) (tailFor 41) 41 =
      .settled gO4 41 := by
  decide +kernel

/-- Stage 4 as it is solved. -/
theorem O4_solved : solveStageFrom recordSet .shared gO3.main.r
    (laterShape recordSet gO3 ⟨0, 0, 15, 15⟩) 32 0 = some ⟨gO4, 41⟩ := by
  rw [O4_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ O4_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 41 _ _ O4_turn2))

/-- The later stages follow from the first group, one step of solveLater after the other. -/
theorem O_later : solveLater recordSet .shared gO1
    [⟨4, 3, 18, 14⟩, ⟨4, 3, 14, 13⟩, ⟨0, 0, 15, 15⟩] = some szOFull.tail := by
  rw [solveLater_step (by decide) O2_solved, solveLater_step (by decide) O3_solved, solveLater_step
    (by decide) O4_solved]
  decide

/-- **The stages of Omega's test.** -/
theorem O_stages : solveStages recordSet .shared gO1 51 recordLines.omega.stages
    = some szOFull :=
  solveStages_of (by decide) O_later

end H2K.Sizes

#print axioms H2K.Sizes.O_later
#print axioms H2K.Sizes.O_stages
