-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/TurnsUFull.lean: at the lines typed for the full-size parameter file
(Params.recordLines), the stages of the folded row's test in a proof file's chains are the typed
list szUFull, each stage by evaluations of the planner in Lean's kernel.

The way is that of OnBytes/Params/KeyStagesRecordFolded.lean: every turn of the iteration that
solves a stage has a closed statement of its own, proved by decide +kernel, with the turn's answer
typed; each stage's shape is typed too; the statements are joined by the laws of
OnBytes/Params/SolveSteps.lean and SizedForward.lean. The typed values were printed by Lean's
evaluator and laid in by a program; each is checked by the kernel in its own statement, so none is
taken on trust.
Main names:
  `gU1` and so on: the stages' groups. `U_later`, `U_stages`: the stages.
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

/-- The group of stage 1 of the folded row's test. -/
def gU1 : GroupSize :=
  ⟨⟨24, 4194304, 101, true⟩, ⟨13, 64, 152, true⟩, 7, 0, 1, .johnson, 182⟩

/-- The group of stage 2. -/
def gU2 : GroupSize :=
  ⟨⟨21, 131072, 54, true⟩, ⟨12, 256, 54, true⟩, 5, 2, 1, .johnson, 168⟩

/-- The group of stage 3. -/
def gU3 : GroupSize :=
  ⟨⟨17, 8192, 54, true⟩, ⟨12, 256, 54, true⟩, 4, 2, 1, .johnson, 293⟩

/-- The group of stage 4. -/
def gU4 : GroupSize :=
  ⟨⟨13, 512, 54, true⟩, ⟨12, 256, 54, true⟩, 4, 2, 1, .johnson, 510⟩

/-- The group of stage 5. -/
def gU5 : GroupSize :=
  ⟨⟨14, 512, 51, true⟩, ⟨14, 1024, 51, true⟩, 0, 0, 1, .johnson, 489⟩

/-- The shape from which stage 2 is solved. -/
def shU2 : GroupSize :=
  ⟨⟨21, 131072, 0, true⟩, ⟨12, 256, 0, true⟩, 5, 2, 1, .johnson, 0⟩

/-- It is the shape that laterShape makes. -/
theorem U2_shape : laterShape recordSet gU1 ⟨5, 2, 21, 12⟩ = shU2 := by
  decide +kernel

/-- Turn 1 of stage 2, from 0 positions. -/
theorem U2_turn1 : turn recordSet .shared
    ⟨stageCubeBits shU2, 1, 4 + 3 * max gU1.main.r 1024⟩ shU2
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨21, 131072, 0, true⟩, ⟨12, 256, 0, true⟩, 5, 2, 1, .johnson, 168⟩ 51 := by
  decide +kernel

/-- Turn 2 of stage 2, from 51 positions. -/
theorem U2_turn2 : turn recordSet .shared
    ⟨stageCubeBits shU2, 1, 4 + 3 * max gU1.main.r 1024⟩ shU2
    (tailFor 51) (tailFor 51) 51 =
      .more ⟨⟨21, 131072, 51, true⟩, ⟨12, 256, 51, true⟩, 5, 2, 1, .johnson, 167⟩ 54 := by
  decide +kernel

/-- Turn 3 of stage 2, from 54 positions. -/
theorem U2_turn3 : turn recordSet .shared
    ⟨stageCubeBits shU2, 1, 4 + 3 * max gU1.main.r 1024⟩ shU2
    (tailFor 54) (tailFor 54) 54 =
      .settled gU2 54 := by
  decide +kernel

/-- Stage 2 as it is solved. -/
theorem U2_solved : solveStageFrom recordSet .shared gU1.main.r
    (laterShape recordSet gU1 ⟨5, 2, 21, 12⟩) 32 0 = some ⟨gU2, 54⟩ := by
  rw [U2_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ U2_turn1).trans
    ((solveStageFrom_more _ _ _ _ 30 51 _ _ U2_turn2).trans
    ((solveStageFrom_settled _ _ _ _ 29 54 _ _ U2_turn3)))

/-- The shape from which stage 3 is solved. -/
def shU3 : GroupSize :=
  ⟨⟨17, 8192, 0, true⟩, ⟨12, 256, 0, true⟩, 4, 2, 1, .johnson, 0⟩

/-- It is the shape that laterShape makes. -/
theorem U3_shape : laterShape recordSet gU2 ⟨4, 2, 17, 12⟩ = shU3 := by
  decide +kernel

/-- Turn 1 of stage 3, from 0 positions. -/
theorem U3_turn1 : turn recordSet .shared
    ⟨stageCubeBits shU3, 1, 4 + 3 * max gU2.main.r 1024⟩ shU3
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨17, 8192, 0, true⟩, ⟨12, 256, 0, true⟩, 4, 2, 1, .johnson, 306⟩ 51 := by
  decide +kernel

/-- Turn 2 of stage 3, from 51 positions. -/
theorem U3_turn2 : turn recordSet .shared
    ⟨stageCubeBits shU3, 1, 4 + 3 * max gU2.main.r 1024⟩ shU3
    (tailFor 51) (tailFor 51) 51 =
      .more ⟨⟨17, 8192, 51, true⟩, ⟨12, 256, 51, true⟩, 4, 2, 1, .johnson, 292⟩ 54 := by
  decide +kernel

/-- Turn 3 of stage 3, from 54 positions. -/
theorem U3_turn3 : turn recordSet .shared
    ⟨stageCubeBits shU3, 1, 4 + 3 * max gU2.main.r 1024⟩ shU3
    (tailFor 54) (tailFor 54) 54 =
      .settled gU3 54 := by
  decide +kernel

/-- Stage 3 as it is solved. -/
theorem U3_solved : solveStageFrom recordSet .shared gU2.main.r
    (laterShape recordSet gU2 ⟨4, 2, 17, 12⟩) 32 0 = some ⟨gU3, 54⟩ := by
  rw [U3_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ U3_turn1).trans
    ((solveStageFrom_more _ _ _ _ 30 51 _ _ U3_turn2).trans
    ((solveStageFrom_settled _ _ _ _ 29 54 _ _ U3_turn3)))

/-- The shape from which stage 4 is solved. -/
def shU4 : GroupSize :=
  ⟨⟨13, 512, 0, true⟩, ⟨12, 256, 0, true⟩, 4, 2, 1, .johnson, 0⟩

/-- It is the shape that laterShape makes. -/
theorem U4_shape : laterShape recordSet gU3 ⟨4, 2, 13, 12⟩ = shU4 := by
  decide +kernel

/-- Turn 1 of stage 4, from 0 positions. -/
theorem U4_turn1 : turn recordSet .shared
    ⟨stageCubeBits shU4, 1, 4 + 3 * max gU3.main.r 1024⟩ shU4
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨13, 512, 0, true⟩, ⟨12, 256, 0, true⟩, 4, 2, 1, .johnson, 530⟩ 51 := by
  decide +kernel

/-- Turn 2 of stage 4, from 51 positions. -/
theorem U4_turn2 : turn recordSet .shared
    ⟨stageCubeBits shU4, 1, 4 + 3 * max gU3.main.r 1024⟩ shU4
    (tailFor 51) (tailFor 51) 51 =
      .more ⟨⟨13, 512, 51, true⟩, ⟨12, 256, 51, true⟩, 4, 2, 1, .johnson, 509⟩ 54 := by
  decide +kernel

/-- Turn 3 of stage 4, from 54 positions. -/
theorem U4_turn3 : turn recordSet .shared
    ⟨stageCubeBits shU4, 1, 4 + 3 * max gU3.main.r 1024⟩ shU4
    (tailFor 54) (tailFor 54) 54 =
      .settled gU4 54 := by
  decide +kernel

/-- Stage 4 as it is solved. -/
theorem U4_solved : solveStageFrom recordSet .shared gU3.main.r
    (laterShape recordSet gU3 ⟨4, 2, 13, 12⟩) 32 0 = some ⟨gU4, 54⟩ := by
  rw [U4_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ U4_turn1).trans
    ((solveStageFrom_more _ _ _ _ 30 51 _ _ U4_turn2).trans
    ((solveStageFrom_settled _ _ _ _ 29 54 _ _ U4_turn3)))

/-- The shape from which stage 5 is solved. -/
def shU5 : GroupSize :=
  ⟨⟨14, 512, 0, true⟩, ⟨14, 1024, 0, true⟩, 0, 0, 1, .johnson, 0⟩

/-- It is the shape that laterShape makes. -/
theorem U5_shape : laterShape recordSet gU4 ⟨0, 0, 14, 14⟩ = shU5 := by
  decide +kernel

/-- Turn 1 of stage 5, from 0 positions. -/
theorem U5_turn1 : turn recordSet .shared
    ⟨stageCubeBits shU5, 1, 4 + 3 * max gU4.main.r 1024⟩ shU5
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨14, 512, 0, true⟩, ⟨14, 1024, 0, true⟩, 0, 0, 1, .johnson, 482⟩ 51 := by
  decide +kernel

/-- Turn 2 of stage 5, from 51 positions. -/
theorem U5_turn2 : turn recordSet .shared
    ⟨stageCubeBits shU5, 1, 4 + 3 * max gU4.main.r 1024⟩ shU5
    (tailFor 51) (tailFor 51) 51 =
      .settled gU5 51 := by
  decide +kernel

/-- Stage 5 as it is solved. -/
theorem U5_solved : solveStageFrom recordSet .shared gU4.main.r
    (laterShape recordSet gU4 ⟨0, 0, 14, 14⟩) 32 0 = some ⟨gU5, 51⟩ := by
  rw [U5_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ U5_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 51 _ _ U5_turn2))

/-- The later stages follow from the first group, one step of solveLater after the other. -/
theorem U_later : solveLater recordSet .shared gU1
    [⟨5, 2, 21, 12⟩, ⟨4, 2, 17, 12⟩, ⟨4, 2, 13, 12⟩, ⟨0, 0, 14, 14⟩] = some szUFull.tail := by
  rw [solveLater_step (by decide) U2_solved, solveLater_step (by decide) U3_solved, solveLater_step
    (by decide) U4_solved, solveLater_step (by decide) U5_solved]
  decide

/-- **The stages of the folded row's test.** -/
theorem U_stages : solveStages recordSet .shared gU1 101 recordLines.folded.stages
    = some szUFull :=
  solveStages_of (by decide) U_later

end H2K.Sizes

#print axioms H2K.Sizes.U_later
#print axioms H2K.Sizes.U_stages
