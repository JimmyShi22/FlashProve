-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryStagesRecord.lean: at the lines typed for the full-size parameter file of the
setting "record with work", the parts of an entry's sizes, each by an evaluation of the planner in
Lean's kernel.

The setting: all eight groups up to the Johnson radius, proof of work before the draws of positions
(20, 28, 32 bits), and a stored table with a record. `recordLines` is a value typed for what the
first 32 lines of prover/examples/target_full_f2/policy.txt say (a test holds it against a copy:
OnBytes/K/Left/TestSaysLines.lean, not here). Typed besides: the table as sized (`recordTable`:
a record of one answer, the two derived integers 24 and 24), the five groups and stages of the
proximity test in an entry's chain (`recordG1` to `recordG5`, `recordStages`: all under the rule
`johnson`, with the integers m = 182, 182, 318, 570, 348), the link's shape, the chain's codes, and
the plan's 42 entries, of which the first is the entry RECORD. Each theorem is one closed statement
on the planner, proved by `decide +kernel`, at once or turn by turn (see below): the table
(`record_table`, `record_admitted`, `record_index`), the columns of a link (`record_first`,
`record_further`: 62 and 62), the shape and the load from which the first group is solved
(`record_shape1`, `record_load`), the first group (`record_group`), the four later stages
(`record_stage2` to `record_stage5`), the numbering of the codes (`record_numbering`), the link's
shape (`record_linkShape`), and the finished plan: the routine `finishHeld` answers on the typed
sizes, and the plan has the typed entries (`record_finish`); `finishHeld` returns a plan only if
`Planned.holds` says yes of it (`finishHeld_holds`), so every round of this plan holds in the
planner's reckoning. That reckoning counts a round's proof of work toward the target: six entries
have 32 bits of work (LINK, the four CS, BASE). OnBytes/Params/EntryParamsRecord.lean puts them
together.

How the first group and the later stages are proved. Each is an iteration of turns
(`solveGroupFrom`, `solveStageFrom`, OnBytes/Params/Group.lean), and Lean, as measured, holds
several GiB of memory while it checks one evaluation of a whole iteration: the more, the
longer the single evaluation runs. So each turn has a closed statement of its own
(`record_group_turn1` to `record_stage5_turn3`), proved by `decide +kernel`, with the turn's answer
typed; each later stage's shape is typed too (`recordShape2` to `recordShape5`, with
`record_stage2_shape` and its like); and the theorem is joined from these by the laws of
OnBytes/Params/SolveSteps.lean. The typed middle values were printed by Lean's evaluator and laid in
by a program; each is checked by the kernel in its own statement, so none is taken on trust.

Main definitions: `recordLines`, `recordSet`, `recordTable`, `recordG1` to `recordG5`,
`recordStages`, `recordShape1`, `recordLink`, `recordCodes`, `recordEntries`, `recordPlan`.
Main theorems: `record_table`, `record_admitted`, `record_first`, `record_further`, `record_index`,
`record_shape1`, `record_load`, `record_group`, `record_stage2`, `record_stage3`, `record_stage4`,
`record_stage5`, `record_numbering`, `record_linkShape`, `record_finish`.
What is not claimed: that the example's parameter file says `recordLines` (nothing in OnBytes/ reads
that folder). That a round which holds in the planner's reckoning has a small error: under the rule
`johnson` the planner prices a closeness round by an assumed theorem (ePrint 2025/2055, Theorem
4.6), of which nothing is proved here, and no law here says that the planner's interval for a square
root encloses the root: that law is `Bound.enclR_sqrt` (OnBytes/Params/SqrtLaws.lean), for an
interval that is not marked bad, and what the planner's agreement, distance and count at an integer
m enclose is said in OnBytes/Params/JohnsonLaws.lean; this file uses neither. Which rounds hold
without their work is not drawn.
Nothing on a key's or a proof's sizes. The typed values were printed by Lean's evaluator and laid in
by a program; the theorems check them. For proofs only; the program, that is the Lean text
`verify-on-bytes`, does not import this file.

-/
import OnBytes.Params.SolveSteps

set_option autoImplicit false

namespace OnBytes.Params

/-- A value typed for what the first 32 lines of the full-size parameter file of the setting "record
with work" say. -/
def recordLines : Lines where
  sec := 128
  reading := 1
  rowcost := 1
  slots := 64
  answers := 1
  workField := ⟨0, 0, 0⟩
  workSample := ⟨0, 0, 0⟩
  workCloseness := ⟨0, 0, 0⟩
  workPositions := ⟨20, 28, 32⟩
  workSmallness := ⟨0, 0, 0⟩
  salt := 40
  listed := 0
  link := ⟨23, 22, 17, 13,
    [⟨4, 3, 22, 17⟩, ⟨3, 3, 19, 16⟩, ⟨3, 3, 16, 15⟩, ⟨4, 4, 13, 13⟩, ⟨0, 0, 15, 15⟩]⟩
  folded := ⟨24, 22, 13, 6,
    [⟨5, 2, 21, 12⟩, ⟨4, 2, 17, 12⟩, ⟨4, 2, 13, 12⟩, ⟨0, 0, 14, 14⟩]⟩
  omega := ⟨22, 18, 13, 6,
    [⟨4, 3, 18, 14⟩, ⟨4, 3, 14, 13⟩, ⟨0, 0, 15, 15⟩]⟩
  own := ⟨22, 18, 13, 8,
    [⟨4, 3, 18, 15⟩, ⟨3, 3, 15, 14⟩, ⟨3, 3, 13, 13⟩, ⟨0, 0, 15, 15⟩]⟩
  onceFolded := ⟨24, 22, 13, 6,
    [⟨5, 2, 21, 12⟩, ⟨4, 2, 17, 12⟩, ⟨4, 2, 13, 12⟩, ⟨0, 0, 14, 14⟩]⟩
  onceOmega := ⟨22, 18, 13, 6,
    [⟨4, 3, 18, 14⟩, ⟨4, 3, 14, 13⟩, ⟨0, 0, 15, 15⟩]⟩
  onceOwn := ⟨22, 18, 13, 8,
    [⟨4, 3, 18, 15⟩, ⟨3, 3, 15, 14⟩, ⟨3, 3, 13, 13⟩, ⟨0, 0, 15, 15⟩]⟩
  onceRanges := ⟨22, 18, 16, 12,
    [⟨4, 3, 19, 17⟩, ⟨3, 3, 17, 17⟩, ⟨0, 0, 20, 20⟩]⟩
  rangesPart := 18
  tableRowsLog := 11
  tableLogN := 32
  tableData := 402653184
  tableRandom := 44040191
  blockLog := 18

/-- The setting of these lines. -/
def recordSet : Setting := settingOf recordLines

/-- The table as it is sized at these lines. -/
def recordTable : TableSize := ⟨⟨32, 402653184, 44040191, false⟩, 11, 1, ⟨0, 0, 24, 24⟩⟩

/-- The group of stage 1 of the test in an entry's chain. -/
def recordG1 : GroupSize :=
  ⟨⟨24, 4194304, 97, true⟩, ⟨13, 64, 97, true⟩, 8, 0, 1, .johnson, 182⟩

/-- The group of stage 2 of the test in an entry's chain. -/
def recordG2 : GroupSize :=
  ⟨⟨21, 131072, 49, true⟩, ⟨12, 128, 49, true⟩, 5, 2, 1, .johnson, 182⟩

/-- The group of stage 3 of the test in an entry's chain. -/
def recordG3 : GroupSize :=
  ⟨⟨17, 8192, 49, true⟩, ⟨12, 128, 49, true⟩, 4, 2, 1, .johnson, 318⟩

/-- The group of stage 4 of the test in an entry's chain. -/
def recordG4 : GroupSize :=
  ⟨⟨13, 512, 50, true⟩, ⟨12, 128, 50, true⟩, 4, 2, 1, .johnson, 570⟩

/-- The group of stage 5 of the test in an entry's chain. -/
def recordG5 : GroupSize :=
  ⟨⟨14, 512, 40, true⟩, ⟨14, 512, 40, true⟩, 0, 0, 1, .johnson, 348⟩

/-- The five stages of that test. -/
def recordStages : List StageSize :=
  [⟨recordG1, 97, 0⟩, ⟨recordG2, 49, 93⟩, ⟨recordG3, 49, 109⟩, ⟨recordG4, 50, 109⟩,
    ⟨recordG5, 40, 106⟩]

/-- The shape from which the first group is solved. -/
def recordShape1 : GroupSize :=
  ⟨⟨24, 4194304, 0, true⟩, ⟨13, 64, 0, true⟩, 8, 0, 1, .johnson, 0⟩

/-- The link's shape. -/
def recordLink : LinkShape :=
  ⟨⟨⟨32, 402653184, 44040191⟩, 11, 1, 40⟩, 62, 62, 0, 0, 107, true, 0, true, [⟨1, 1, 5, 2⟩, ⟨2, 1,
  4, 2⟩, ⟨3, 2, 4, 2⟩, ⟨4, 3, 0, 0⟩], ⟨true⟩⟩

/-- The chain's codes. -/
def recordCodes : Codes :=
  ⟨#[⟨24, 4194304, 97⟩, ⟨21, 131072, 49⟩, ⟨17, 8192, 49⟩, ⟨13, 512, 50⟩, ⟨14, 512, 40⟩], #[⟨13,
  64, 97⟩, ⟨12, 128, 49⟩, ⟨12, 128, 50⟩, ⟨14, 512, 40⟩]⟩

/-- The plan's 42 entries. -/
def recordEntries : List Fmt.Entry :=
  [⟨"RECORD", 1, 0, 0, 0, 0, 30, 1, 0, 0, 0, 0⟩, ⟨"LINK point", 1, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0⟩,
  ⟨"SEND seed", 1, 0, 32, 1, 0, 30, 1, 0, 0, 0, 0⟩, ⟨"SEND answer", 1, 0, 48, 0, 2, 0, 0, 0, 0, 0,
  0⟩, ⟨"LINK", 1, 32, 0, 0, 0, 0, 0, 124, 32, 0, 0⟩, ⟨"LINK phi", 1, 0, 0, 0, 0, 29, 0, 0, 0, 0,
  0⟩, ⟨"BAT", 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 129⟩, ⟨"FOLD epsilon", 1, 0, 24, 0, 0, 1, 0, 0, 0, 0,
  0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0,
  0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0,
  0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0,
  0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1,
  0, 0, 0, 0, 0⟩, ⟨"SEND seed", 1, 0, 32, 1, 0, 24, 1, 0, 0, 0, 0⟩, ⟨"CS", 1, 32, 24, 0, 1, 1, 0,
  97, 24, 0, 293⟩, ⟨"FOLD epsilon", 1, 0, 24, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0,
  0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48,
  0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0,
  48, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"SEND seed", 1, 0, 32, 1, 0, 19, 1, 0, 0, 0, 0⟩, ⟨"CS", 1, 32, 24,
  0, 1, 1, 0, 49, 21, 0, 149⟩, ⟨"FOLD epsilon", 1, 0, 24, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round",
  1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
  ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0,
  0⟩, ⟨"SEND seed", 1, 0, 32, 1, 0, 15, 1, 0, 0, 0, 0⟩, ⟨"CS", 1, 32, 24, 0, 1, 1, 0, 49, 17, 0,
  149⟩, ⟨"FOLD epsilon", 1, 0, 24, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0,
  0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1,
  0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"SEND seed", 1, 0, 32, 1, 0,
  11, 1, 0, 0, 0, 0⟩, ⟨"CS", 1, 32, 24, 0, 1, 1, 0, 50, 13, 0, 152⟩, ⟨"BASE lambda", 1, 0, 24, 0,
  0, 1, 0, 0, 0, 0, 0⟩, ⟨"BASE", 1, 32, 26496, 0, 0, 0, 0, 40, 14, 0, 0⟩]

/-- The plan typed for an entry's chain. -/
def recordPlan : Fmt.Plan := ⟨.two, 40, 8, 0, 1, 1, recordEntries⟩

/-- The table as `deriveTable` sizes it. -/
theorem record_table : deriveTable recordSet recordLines = some recordTable := by decide +kernel

/-- The table is admitted at its analysis. -/
theorem record_admitted :
    tableAdmitted recordTable (tableAnalysis recordSet recordTable) = true := by decide +kernel

/-- The columns of the first table in a link. -/
theorem record_first : scopePositions recordSet .once
    (tableAnalysis recordSet recordTable).later.agree = 62 := by decide +kernel

/-- The columns of the further table in a link. -/
theorem record_further :
    scopePositions recordSet .once (tableAnalysis recordSet recordTable).once.agree = 62 := by
  decide +kernel

/-- The two tests of `linkSized` on the index's shape pass. -/
theorem record_index : (decide (40 < (indexShapeOf recordSet recordTable).v) ||
    decide ((indexShapeOf recordSet recordTable).code.ell ≤
      3 * (indexShapeOf recordSet recordTable).answers)) = false := by decide +kernel

/-- The shape from which `linkSized` has the first group solved. -/
theorem record_shape1 : shapeOf recordLines.onceFolded (1 + clog2 (linRowsOf
    (foldedEntries (indexShapeOf recordSet recordTable) + recordSet.samples)
    (2 ^ recordLines.onceFolded.logL) true)) true = recordShape1 := by decide +kernel

/-- The load under which it is solved. -/
theorem record_load : (⟨stageCubeBits recordShape1, 2,
    2 * (indexShapeOf recordSet recordTable).answers + 62 + 62 + 1 + 2 * recordSet.samples⟩ :
      GroupLoad) = ⟨31, 2, 129⟩ := by decide +kernel

/-- Turn 1 of the first group, from 0 positions. -/
theorem record_group_turn1 : turn recordSet .once ⟨31, 2, 129⟩ recordShape1
    (tailFor (id 0)) (tailFor 0) 0 =
      .more ⟨⟨24, 4194304, 0, true⟩, ⟨13, 64, 0, true⟩, 8, 0, 1, .johnson, 182⟩ 97 := by
  decide +kernel

/-- Turn 2 of the first group, from 97 positions. -/
theorem record_group_turn2 : turn recordSet .once ⟨31, 2, 129⟩ recordShape1
    (tailFor (id 97)) (tailFor 97) 97 =
      .settled recordG1 97 := by
  decide +kernel

/-- The first group as it is solved. -/
theorem record_group : solveGroup recordSet .once ⟨31, 2, 129⟩ id recordShape1 =
    some ⟨recordG1, 97⟩ := by
  unfold solveGroup
  exact (solveGroupFrom_more _ _ _ _ _ 31 0 _ _ record_group_turn1).trans
    ((solveGroupFrom_settled _ _ _ _ _ 30 97 _ _ record_group_turn2 rfl))

/-- The shape from which stage 2 is solved. -/
def recordShape2 : GroupSize :=
  ⟨⟨21, 131072, 0, true⟩, ⟨12, 128, 0, true⟩, 5, 2, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem record_stage2_shape : laterShape recordSet recordG1 ⟨5, 2, 21, 12⟩ = recordShape2 := by
  decide +kernel

/-- Turn 1 of stage 2, from 0 positions. -/
theorem record_stage2_turn1 : turn recordSet .once
    ⟨stageCubeBits recordShape2, 1, 4 + 3 * max recordG1.main.r 1024⟩ recordShape2
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨21, 131072, 0, true⟩, ⟨12, 128, 0, true⟩, 5, 2, 1, .johnson, 182⟩ 49 := by
  decide +kernel

/-- Turn 2 of stage 2, from 49 positions. -/
theorem record_stage2_turn2 : turn recordSet .once
    ⟨stageCubeBits recordShape2, 1, 4 + 3 * max recordG1.main.r 1024⟩ recordShape2
    (tailFor 49) (tailFor 49) 49 =
      .settled recordG2 49 := by
  decide +kernel

/-- Stage 2 as it is solved. -/
theorem record_stage2 : solveStageFrom recordSet .once recordG1.main.r
    (laterShape recordSet recordG1 ⟨5, 2, 21, 12⟩) 32 0 = some ⟨recordG2, 49⟩ := by
  rw [record_stage2_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ record_stage2_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 49 _ _ record_stage2_turn2))

/-- The shape from which stage 3 is solved. -/
def recordShape3 : GroupSize :=
  ⟨⟨17, 8192, 0, true⟩, ⟨12, 128, 0, true⟩, 4, 2, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem record_stage3_shape : laterShape recordSet recordG2 ⟨4, 2, 17, 12⟩ = recordShape3 := by
  decide +kernel

/-- Turn 1 of stage 3, from 0 positions. -/
theorem record_stage3_turn1 : turn recordSet .once
    ⟨stageCubeBits recordShape3, 1, 4 + 3 * max recordG2.main.r 1024⟩ recordShape3
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨17, 8192, 0, true⟩, ⟨12, 128, 0, true⟩, 4, 2, 1, .johnson, 318⟩ 49 := by
  decide +kernel

/-- Turn 2 of stage 3, from 49 positions. -/
theorem record_stage3_turn2 : turn recordSet .once
    ⟨stageCubeBits recordShape3, 1, 4 + 3 * max recordG2.main.r 1024⟩ recordShape3
    (tailFor 49) (tailFor 49) 49 =
      .settled recordG3 49 := by
  decide +kernel

/-- Stage 3 as it is solved. -/
theorem record_stage3 : solveStageFrom recordSet .once recordG2.main.r
    (laterShape recordSet recordG2 ⟨4, 2, 17, 12⟩) 32 0 = some ⟨recordG3, 49⟩ := by
  rw [record_stage3_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ record_stage3_turn1).trans
    ((solveStageFrom_settled _ _ _ _ 30 49 _ _ record_stage3_turn2))

/-- The shape from which stage 4 is solved. -/
def recordShape4 : GroupSize :=
  ⟨⟨13, 512, 0, true⟩, ⟨12, 128, 0, true⟩, 4, 2, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem record_stage4_shape : laterShape recordSet recordG3 ⟨4, 2, 13, 12⟩ = recordShape4 := by
  decide +kernel

/-- Turn 1 of stage 4, from 0 positions. -/
theorem record_stage4_turn1 : turn recordSet .once
    ⟨stageCubeBits recordShape4, 1, 4 + 3 * max recordG3.main.r 1024⟩ recordShape4
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨13, 512, 0, true⟩, ⟨12, 128, 0, true⟩, 4, 2, 1, .johnson, 554⟩ 49 := by
  decide +kernel

/-- Turn 2 of stage 4, from 49 positions. -/
theorem record_stage4_turn2 : turn recordSet .once
    ⟨stageCubeBits recordShape4, 1, 4 + 3 * max recordG3.main.r 1024⟩ recordShape4
    (tailFor 49) (tailFor 49) 49 =
      .more ⟨⟨13, 512, 49, true⟩, ⟨12, 128, 49, true⟩, 4, 2, 1, .johnson, 569⟩ 50 := by
  decide +kernel

/-- Turn 3 of stage 4, from 50 positions. -/
theorem record_stage4_turn3 : turn recordSet .once
    ⟨stageCubeBits recordShape4, 1, 4 + 3 * max recordG3.main.r 1024⟩ recordShape4
    (tailFor 50) (tailFor 50) 50 =
      .settled recordG4 50 := by
  decide +kernel

/-- Stage 4 as it is solved. -/
theorem record_stage4 : solveStageFrom recordSet .once recordG3.main.r
    (laterShape recordSet recordG3 ⟨4, 2, 13, 12⟩) 32 0 = some ⟨recordG4, 50⟩ := by
  rw [record_stage4_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ record_stage4_turn1).trans
    ((solveStageFrom_more _ _ _ _ 30 49 _ _ record_stage4_turn2).trans
    ((solveStageFrom_settled _ _ _ _ 29 50 _ _ record_stage4_turn3)))

/-- The shape from which stage 5 is solved. -/
def recordShape5 : GroupSize :=
  ⟨⟨14, 512, 0, true⟩, ⟨14, 512, 0, true⟩, 0, 0, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem record_stage5_shape : laterShape recordSet recordG4 ⟨0, 0, 14, 14⟩ = recordShape5 := by
  decide +kernel

/-- Turn 1 of stage 5, from 0 positions. -/
theorem record_stage5_turn1 : turn recordSet .once
    ⟨stageCubeBits recordShape5, 1, 4 + 3 * max recordG4.main.r 1024⟩ recordShape5
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨14, 512, 0, true⟩, ⟨14, 512, 0, true⟩, 0, 0, 1, .johnson, 340⟩ 39 := by
  decide +kernel

/-- Turn 2 of stage 5, from 39 positions. -/
theorem record_stage5_turn2 : turn recordSet .once
    ⟨stageCubeBits recordShape5, 1, 4 + 3 * max recordG4.main.r 1024⟩ recordShape5
    (tailFor 39) (tailFor 39) 39 =
      .more ⟨⟨14, 512, 39, true⟩, ⟨14, 512, 39, true⟩, 0, 0, 1, .johnson, 348⟩ 40 := by
  decide +kernel

/-- Turn 3 of stage 5, from 40 positions. -/
theorem record_stage5_turn3 : turn recordSet .once
    ⟨stageCubeBits recordShape5, 1, 4 + 3 * max recordG4.main.r 1024⟩ recordShape5
    (tailFor 40) (tailFor 40) 40 =
      .settled recordG5 40 := by
  decide +kernel

/-- Stage 5, the last, as it is solved. -/
theorem record_stage5 : solveStageFrom recordSet .once recordG4.main.r
    (laterShape recordSet recordG4 ⟨0, 0, 14, 14⟩) 32 0 = some ⟨recordG5, 40⟩ := by
  rw [record_stage5_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ record_stage5_turn1).trans
    ((solveStageFrom_more _ _ _ _ 30 39 _ _ record_stage5_turn2).trans
    ((solveStageFrom_settled _ _ _ _ 29 40 _ _ record_stage5_turn3)))

/-- The numbering of the codes of the typed stages, from an empty list of codes. -/
theorem record_numbering : ioppStages recordStages {} =
    (⟨0, 0, 8, 0⟩ :: recordLink.later, recordCodes) := by decide +kernel

/-- The link's shape as `linkSized` puts it together. -/
theorem record_linkShape : (⟨indexShapeOf recordSet recordTable, 62, 62, 0, 0,
    linRowsOf (foldedEntries (indexShapeOf recordSet recordTable) + recordSet.samples)
      (2 ^ recordLines.onceFolded.logL) true,
    true, 0, true, recordLink.later, ⟨true⟩⟩ : LinkShape) = recordLink := by decide +kernel

/-- The plan of an entry's chain at the typed sizes is finished and holds, and has the typed entries
and the setting's four numbers. -/
theorem record_finish : ((finishHeld recordSet .once
    (linkPlan ⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩)).toOption.any fun P =>
      decide (P.rounds.map (·.entry) = recordEntries) && decide (P.set.saltBytes = 40) &&
        decide (P.set.nonceBytes = 8) && decide (P.set.positionBytes = 0) &&
        decide (P.set.samples = 1)) = true := by decide +kernel

end OnBytes.Params
