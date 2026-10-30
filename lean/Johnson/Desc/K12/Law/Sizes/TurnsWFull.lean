-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/TurnsWFull.lean: at the lines typed for the full-size parameter file
(Params.recordLines), the stages of the request's own test in a proof file's chains are the typed
list szWFull, each stage by evaluations of the planner in Lean's kernel.

The way is that of OnBytes/Params/KeyStagesRecordFolded.lean: every turn of the iteration that
solves a stage has a closed statement of its own, proved by decide +kernel, with the turn's answer
typed; each stage's shape is typed too; the statements are joined by the laws of
OnBytes/Params/SolveSteps.lean and SizedForward.lean. The typed values were printed by Lean's
evaluator and laid in by a program; each is checked by the kernel in its own statement, so none is
taken on trust.
Main names:
  `gW1` and so on: the stages' groups. `W_later`, `W_stages`: the stages.
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

/-- The group of stage 1 of the request's own test. -/
def gW1 : GroupSize :=
  ⟨⟨22, 262144, 3571, true⟩, ⟨13, 256, 55, true⟩, 5, 1, 1, .johnson, 159⟩

/-- The group of stage 2. -/
def gW2 : GroupSize :=
  ⟨⟨18, 16384, 55, true⟩, ⟨15, 1024, 55, true⟩, 4, 3, 1, .johnson, 277⟩

/-- The group of stage 3. -/
def gW3 : GroupSize :=
  ⟨⟨15, 2048, 55, true⟩, ⟨14, 512, 55, true⟩, 3, 3, 1, .johnson, 423⟩

/-- The group of stage 4. -/
def gW4 : GroupSize :=
  ⟨⟨13, 256, 46, true⟩, ⟨13, 256, 46, true⟩, 3, 3, 1, .johnson, 378⟩

/-- The group of stage 5. -/
def gW5 : GroupSize :=
  ⟨⟨15, 256, 44, true⟩, ⟨15, 1024, 44, true⟩, 0, 0, 1, .johnson, 345⟩

/-- The shape from which stage 2 is solved. -/
def shW2 : GroupSize :=
  ⟨⟨18, 16384, 0, true⟩, ⟨15, 1024, 0, true⟩, 4, 3, 1, .johnson, 0⟩

/-- It is the shape that laterShape makes. -/
theorem W2_shape : laterShape recordSet gW1 ⟨4, 3, 18, 15⟩ = shW2 := by
  decide +kernel

/-- Turn 1 of stage 2, from 0 positions. -/
theorem W2_turn1 : turn recordSet .request
    ⟨stageCubeBits shW2, 1, 4 + 3 * max gW1.main.r 1024⟩ shW2
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨18, 16384, 0, true⟩, ⟨15, 1024, 0, true⟩, 4, 3, 1, .johnson, 277⟩ 55 := by
  decide +kernel

/-- Turn 2 of stage 2, from 55 positions. -/
theorem W2_turn2 : turn recordSet .request
    ⟨stageCubeBits shW2, 1, 4 + 3 * max gW1.main.r 1024⟩ shW2
    (tailFor 55) (tailFor 55) 55 =
      .settled gW2 55 := by
  decide +kernel

/-- Stage 2 as it is solved. -/
theorem W2_solved : solveStageFrom recordSet .request gW1.main.r
    (laterShape recordSet gW1 ⟨4, 3, 18, 15⟩) 32 0 = some ⟨gW2, 55⟩ := by
  rw [W2_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ W2_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 55 _ _ W2_turn2))

/-- The shape from which stage 3 is solved. -/
def shW3 : GroupSize :=
  ⟨⟨15, 2048, 0, true⟩, ⟨14, 512, 0, true⟩, 3, 3, 1, .johnson, 0⟩

/-- It is the shape that laterShape makes. -/
theorem W3_shape : laterShape recordSet gW2 ⟨3, 3, 15, 14⟩ = shW3 := by
  decide +kernel

/-- Turn 1 of stage 3, from 0 positions. -/
theorem W3_turn1 : turn recordSet .request
    ⟨stageCubeBits shW3, 1, 4 + 3 * max gW2.main.r 1024⟩ shW3
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨15, 2048, 0, true⟩, ⟨14, 512, 0, true⟩, 3, 3, 1, .johnson, 420⟩ 55 := by
  decide +kernel

/-- Turn 2 of stage 3, from 55 positions. -/
theorem W3_turn2 : turn recordSet .request
    ⟨stageCubeBits shW3, 1, 4 + 3 * max gW2.main.r 1024⟩ shW3
    (tailFor 55) (tailFor 55) 55 =
      .settled gW3 55 := by
  decide +kernel

/-- Stage 3 as it is solved. -/
theorem W3_solved : solveStageFrom recordSet .request gW2.main.r
    (laterShape recordSet gW2 ⟨3, 3, 15, 14⟩) 32 0 = some ⟨gW3, 55⟩ := by
  rw [W3_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ W3_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 55 _ _ W3_turn2))

/-- The shape from which stage 4 is solved. -/
def shW4 : GroupSize :=
  ⟨⟨13, 256, 0, true⟩, ⟨13, 256, 0, true⟩, 3, 3, 1, .johnson, 0⟩

/-- It is the shape that laterShape makes. -/
theorem W4_shape : laterShape recordSet gW3 ⟨3, 3, 13, 13⟩ = shW4 := by
  decide +kernel

/-- Turn 1 of stage 4, from 0 positions. -/
theorem W4_turn1 : turn recordSet .request
    ⟨stageCubeBits shW4, 1, 4 + 3 * max gW3.main.r 1024⟩ shW4
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨13, 256, 0, true⟩, ⟨13, 256, 0, true⟩, 3, 3, 1, .johnson, 360⟩ 44 := by
  decide +kernel

/-- Turn 2 of stage 4, from 44 positions. -/
theorem W4_turn2 : turn recordSet .request
    ⟨stageCubeBits shW4, 1, 4 + 3 * max gW3.main.r 1024⟩ shW4
    (tailFor 44) (tailFor 44) 44 =
      .more ⟨⟨13, 256, 44, true⟩, ⟨13, 256, 44, true⟩, 3, 3, 1, .johnson, 378⟩ 46 := by
  decide +kernel

/-- Turn 3 of stage 4, from 46 positions. -/
theorem W4_turn3 : turn recordSet .request
    ⟨stageCubeBits shW4, 1, 4 + 3 * max gW3.main.r 1024⟩ shW4
    (tailFor 46) (tailFor 46) 46 =
      .settled gW4 46 := by
  decide +kernel

/-- Stage 4 as it is solved. -/
theorem W4_solved : solveStageFrom recordSet .request gW3.main.r
    (laterShape recordSet gW3 ⟨3, 3, 13, 13⟩) 32 0 = some ⟨gW4, 46⟩ := by
  rw [W4_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ W4_turn1).trans
    ((solveStageFrom_more _ _ _ _ 30 44 _ _ W4_turn2).trans
    ((solveStageFrom_settled _ _ _ _ 29 46 _ _ W4_turn3)))

/-- The shape from which stage 5 is solved. -/
def shW5 : GroupSize :=
  ⟨⟨15, 256, 0, true⟩, ⟨15, 1024, 0, true⟩, 0, 0, 1, .johnson, 0⟩

/-- It is the shape that laterShape makes. -/
theorem W5_shape : laterShape recordSet gW4 ⟨0, 0, 15, 15⟩ = shW5 := by
  decide +kernel

/-- Turn 1 of stage 5, from 0 positions. -/
theorem W5_turn1 : turn recordSet .request
    ⟨stageCubeBits shW5, 1, 4 + 3 * max gW4.main.r 1024⟩ shW5
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨15, 256, 0, true⟩, ⟨15, 1024, 0, true⟩, 0, 0, 1, .johnson, 341⟩ 44 := by
  decide +kernel

/-- Turn 2 of stage 5, from 44 positions. -/
theorem W5_turn2 : turn recordSet .request
    ⟨stageCubeBits shW5, 1, 4 + 3 * max gW4.main.r 1024⟩ shW5
    (tailFor 44) (tailFor 44) 44 =
      .settled gW5 44 := by
  decide +kernel

/-- Stage 5 as it is solved. -/
theorem W5_solved : solveStageFrom recordSet .request gW4.main.r
    (laterShape recordSet gW4 ⟨0, 0, 15, 15⟩) 32 0 = some ⟨gW5, 44⟩ := by
  rw [W5_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ W5_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 44 _ _ W5_turn2))

/-- The later stages follow from the first group, one step of solveLater after the other. -/
theorem W_later : solveLater recordSet .request gW1
    [⟨4, 3, 18, 15⟩, ⟨3, 3, 15, 14⟩, ⟨3, 3, 13, 13⟩, ⟨0, 0, 15, 15⟩] = some szWFull.tail := by
  rw [solveLater_step (by decide) W2_solved, solveLater_step (by decide) W3_solved, solveLater_step
    (by decide) W4_solved, solveLater_step (by decide) W5_solved]
  decide

/-- **The stages of the request's own test.** -/
theorem W_stages : solveStages recordSet .request gW1 55 recordLines.own.stages
    = some szWFull :=
  solveStages_of (by decide) W_later

end H2K.Sizes

#print axioms H2K.Sizes.W_later
#print axioms H2K.Sizes.W_stages
