-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/TurnsLFull.lean: at the lines typed for the full-size parameter file
(Params.recordLines), the stages of the first chain's last test in a proof file's chains are the
typed list szLFull, each stage by evaluations of the planner in Lean's kernel.

The way is that of OnBytes/Params/KeyStagesRecordFolded.lean: every turn of the iteration that
solves a stage has a closed statement of its own, proved by decide +kernel, with the turn's answer
typed; each stage's shape is typed too; the statements are joined by the laws of
OnBytes/Params/SolveSteps.lean and SizedForward.lean. The typed values were printed by Lean's
evaluator and laid in by a program; each is checked by the kernel in its own statement, so none is
taken on trust.
Main names:
  `gL1` and so on: the stages' groups. `L_later`, `L_stages`: the stages.
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

/-- The group of stage 1 of the first chain's last test. -/
def gL1 : GroupSize :=
  ⟨⟨23, 4194304, 219, true⟩, ⟨17, 8192, 219, true⟩, 1, 0, 1, .johnson, 258⟩

/-- The group of stage 2. -/
def gL2 : GroupSize :=
  ⟨⟨22, 262144, 55, true⟩, ⟨17, 4096, 55, true⟩, 4, 3, 1, .johnson, 158⟩

/-- The group of stage 3. -/
def gL3 : GroupSize :=
  ⟨⟨19, 32768, 55, true⟩, ⟨16, 2048, 55, true⟩, 3, 3, 1, .johnson, 241⟩

/-- The group of stage 4. -/
def gL4 : GroupSize :=
  ⟨⟨16, 4096, 55, true⟩, ⟨15, 1024, 55, true⟩, 3, 3, 1, .johnson, 367⟩

/-- The group of stage 5. -/
def gL5 : GroupSize :=
  ⟨⟨13, 256, 46, true⟩, ⟨13, 256, 46, true⟩, 4, 4, 1, .johnson, 378⟩

/-- The group of stage 6. -/
def gL6 : GroupSize :=
  ⟨⟨15, 256, 44, true⟩, ⟨15, 1024, 44, true⟩, 0, 0, 1, .johnson, 345⟩

/-- The shape from which stage 2 is solved. -/
def shL2 : GroupSize :=
  ⟨⟨22, 262144, 0, true⟩, ⟨17, 4096, 0, true⟩, 4, 3, 1, .johnson, 0⟩

/-- It is the shape that laterShape makes. -/
theorem L2_shape : laterShape recordSet gL1 ⟨4, 3, 22, 17⟩ = shL2 := by
  decide +kernel

/-- Turn 1 of stage 2, from 0 positions. -/
theorem L2_turn1 : turn recordSet .request
    ⟨stageCubeBits shL2, 1, 4 + 3 * max gL1.main.r 1024⟩ shL2
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨22, 262144, 0, true⟩, ⟨17, 4096, 0, true⟩, 4, 3, 1, .johnson, 158⟩ 55 := by
  decide +kernel

/-- Turn 2 of stage 2, from 55 positions. -/
theorem L2_turn2 : turn recordSet .request
    ⟨stageCubeBits shL2, 1, 4 + 3 * max gL1.main.r 1024⟩ shL2
    (tailFor 55) (tailFor 55) 55 =
      .settled gL2 55 := by
  decide +kernel

/-- Stage 2 as it is solved. -/
theorem L2_solved : solveStageFrom recordSet .request gL1.main.r
    (laterShape recordSet gL1 ⟨4, 3, 22, 17⟩) 32 0 = some ⟨gL2, 55⟩ := by
  rw [L2_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ L2_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 55 _ _ L2_turn2))

/-- The shape from which stage 3 is solved. -/
def shL3 : GroupSize :=
  ⟨⟨19, 32768, 0, true⟩, ⟨16, 2048, 0, true⟩, 3, 3, 1, .johnson, 0⟩

/-- It is the shape that laterShape makes. -/
theorem L3_shape : laterShape recordSet gL2 ⟨3, 3, 19, 16⟩ = shL3 := by
  decide +kernel

/-- Turn 1 of stage 3, from 0 positions. -/
theorem L3_turn1 : turn recordSet .request
    ⟨stageCubeBits shL3, 1, 4 + 3 * max gL2.main.r 1024⟩ shL3
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨19, 32768, 0, true⟩, ⟨16, 2048, 0, true⟩, 3, 3, 1, .johnson, 241⟩ 55 := by
  decide +kernel

/-- Turn 2 of stage 3, from 55 positions. -/
theorem L3_turn2 : turn recordSet .request
    ⟨stageCubeBits shL3, 1, 4 + 3 * max gL2.main.r 1024⟩ shL3
    (tailFor 55) (tailFor 55) 55 =
      .settled gL3 55 := by
  decide +kernel

/-- Stage 3 as it is solved. -/
theorem L3_solved : solveStageFrom recordSet .request gL2.main.r
    (laterShape recordSet gL2 ⟨3, 3, 19, 16⟩) 32 0 = some ⟨gL3, 55⟩ := by
  rw [L3_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ L3_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 55 _ _ L3_turn2))

/-- The shape from which stage 4 is solved. -/
def shL4 : GroupSize :=
  ⟨⟨16, 4096, 0, true⟩, ⟨15, 1024, 0, true⟩, 3, 3, 1, .johnson, 0⟩

/-- It is the shape that laterShape makes. -/
theorem L4_shape : laterShape recordSet gL3 ⟨3, 3, 16, 15⟩ = shL4 := by
  decide +kernel

/-- Turn 1 of stage 4, from 0 positions. -/
theorem L4_turn1 : turn recordSet .request
    ⟨stageCubeBits shL4, 1, 4 + 3 * max gL3.main.r 1024⟩ shL4
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨16, 4096, 0, true⟩, ⟨15, 1024, 0, true⟩, 3, 3, 1, .johnson, 365⟩ 55 := by
  decide +kernel

/-- Turn 2 of stage 4, from 55 positions. -/
theorem L4_turn2 : turn recordSet .request
    ⟨stageCubeBits shL4, 1, 4 + 3 * max gL3.main.r 1024⟩ shL4
    (tailFor 55) (tailFor 55) 55 =
      .settled gL4 55 := by
  decide +kernel

/-- Stage 4 as it is solved. -/
theorem L4_solved : solveStageFrom recordSet .request gL3.main.r
    (laterShape recordSet gL3 ⟨3, 3, 16, 15⟩) 32 0 = some ⟨gL4, 55⟩ := by
  rw [L4_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ L4_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 55 _ _ L4_turn2))

/-- The shape from which stage 5 is solved. -/
def shL5 : GroupSize :=
  ⟨⟨13, 256, 0, true⟩, ⟨13, 256, 0, true⟩, 4, 4, 1, .johnson, 0⟩

/-- It is the shape that laterShape makes. -/
theorem L5_shape : laterShape recordSet gL4 ⟨4, 4, 13, 13⟩ = shL5 := by
  decide +kernel

/-- Turn 1 of stage 5, from 0 positions. -/
theorem L5_turn1 : turn recordSet .request
    ⟨stageCubeBits shL5, 1, 4 + 3 * max gL4.main.r 1024⟩ shL5
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨13, 256, 0, true⟩, ⟨13, 256, 0, true⟩, 4, 4, 1, .johnson, 360⟩ 44 := by
  decide +kernel

/-- Turn 2 of stage 5, from 44 positions. -/
theorem L5_turn2 : turn recordSet .request
    ⟨stageCubeBits shL5, 1, 4 + 3 * max gL4.main.r 1024⟩ shL5
    (tailFor 44) (tailFor 44) 44 =
      .more ⟨⟨13, 256, 44, true⟩, ⟨13, 256, 44, true⟩, 4, 4, 1, .johnson, 378⟩ 46 := by
  decide +kernel

/-- Turn 3 of stage 5, from 46 positions. -/
theorem L5_turn3 : turn recordSet .request
    ⟨stageCubeBits shL5, 1, 4 + 3 * max gL4.main.r 1024⟩ shL5
    (tailFor 46) (tailFor 46) 46 =
      .settled gL5 46 := by
  decide +kernel

/-- Stage 5 as it is solved. -/
theorem L5_solved : solveStageFrom recordSet .request gL4.main.r
    (laterShape recordSet gL4 ⟨4, 4, 13, 13⟩) 32 0 = some ⟨gL5, 46⟩ := by
  rw [L5_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ L5_turn1).trans
    ((solveStageFrom_more _ _ _ _ 30 44 _ _ L5_turn2).trans
    ((solveStageFrom_settled _ _ _ _ 29 46 _ _ L5_turn3)))

/-- The shape from which stage 6 is solved. -/
def shL6 : GroupSize :=
  ⟨⟨15, 256, 0, true⟩, ⟨15, 1024, 0, true⟩, 0, 0, 1, .johnson, 0⟩

/-- It is the shape that laterShape makes. -/
theorem L6_shape : laterShape recordSet gL5 ⟨0, 0, 15, 15⟩ = shL6 := by
  decide +kernel

/-- Turn 1 of stage 6, from 0 positions. -/
theorem L6_turn1 : turn recordSet .request
    ⟨stageCubeBits shL6, 1, 4 + 3 * max gL5.main.r 1024⟩ shL6
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨15, 256, 0, true⟩, ⟨15, 1024, 0, true⟩, 0, 0, 1, .johnson, 341⟩ 44 := by
  decide +kernel

/-- Turn 2 of stage 6, from 44 positions. -/
theorem L6_turn2 : turn recordSet .request
    ⟨stageCubeBits shL6, 1, 4 + 3 * max gL5.main.r 1024⟩ shL6
    (tailFor 44) (tailFor 44) 44 =
      .settled gL6 44 := by
  decide +kernel

/-- Stage 6 as it is solved. -/
theorem L6_solved : solveStageFrom recordSet .request gL5.main.r
    (laterShape recordSet gL5 ⟨0, 0, 15, 15⟩) 32 0 = some ⟨gL6, 44⟩ := by
  rw [L6_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ L6_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 44 _ _ L6_turn2))

/-- The later stages follow from the first group, one step of solveLater after the other. -/
theorem L_later : solveLater recordSet .request gL1
    [⟨4, 3, 22, 17⟩, ⟨3, 3, 19, 16⟩, ⟨3, 3, 16, 15⟩, ⟨4, 4, 13, 13⟩, ⟨0, 0, 15, 15⟩] = some
      szLFull.tail := by
  rw [solveLater_step (by decide) L2_solved, solveLater_step (by decide) L3_solved, solveLater_step
    (by decide) L4_solved, solveLater_step (by decide) L5_solved, solveLater_step (by decide)
    L6_solved]
  decide

/-- **The stages of the first chain's last test.** -/
theorem L_stages : solveStages recordSet .request gL1 219 recordLines.link.stages
    = some szLFull :=
  solveStages_of (by decide) L_later

/-- The shape from which the links' group is solved. -/
def linkShapeFull : GroupSize :=
  ⟨⟨23, 4194304, 0, false⟩, ⟨17, 8192, 0, true⟩, 8, 0, 16, .johnson, 0⟩

/-- The load for which it is solved. -/
def linkLoadFull : GroupLoad := ⟨31, 12, 61450⟩

/-- The links' group. -/
def gLink : GroupSize :=
  ⟨⟨23, 4194304, 219, false⟩, ⟨17, 8192, 219, true⟩, 8, 0, 16, .johnson, 258⟩

/-- Turn 1 of the links' group, from 0 positions. -/
theorem link_turn1 : turn recordSet .request linkLoadFull linkShapeFull
    (tailFor (id 0)) (tailFor 0) 0 =
      .more ⟨⟨23, 4194304, 0, false⟩, ⟨17, 8192, 0, true⟩, 8, 0, 16, .johnson, 258⟩ 219 := by
  decide +kernel

/-- Turn 2 of the links' group, from 219 positions. -/
theorem link_turn2 : turn recordSet .request linkLoadFull linkShapeFull
    (tailFor (id 219)) (tailFor 219) 219 =
      .settled gLink 219 := by
  decide +kernel

/-- **The links' group as it is solved**, at the typed load and shape. -/
theorem link_solved : solveGroup recordSet .request linkLoadFull id linkShapeFull =
    some ⟨gLink, 219⟩ := by
  unfold solveGroup
  exact (solveGroupFrom_more _ _ _ _ _ 31 0 _ _ link_turn1).trans
    ((solveGroupFrom_settled _ _ _ _ _ 30 219 _ _ link_turn2 rfl))

end H2K.Sizes

#print axioms H2K.Sizes.L_later
#print axioms H2K.Sizes.L_stages
#print axioms H2K.Sizes.link_solved
