-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryStagesRecordSmall.lean: at the lines typed for the small parameter file of the
setting "record with work", the parts of an entry's sizes, each by an evaluation of the planner in
Lean's kernel.

The like of OnBytes/Params/EntryStagesRecord.lean, whose head describes the setting, at the small
example. `smallRecordLines` is a value typed for what the first 32 lines of
prover/examples/target_small_f2_roomy/policy.txt say (a test holds it against a copy of the file: a
test that is not in this library). Typed besides: the table as sized (`smallRecordTable`: 2 ^ 8 rows
of length 2 ^ 23, a record of one answer, the two derived integers 82 and 82), the three groups and
stages of the proximity test in an entry's chain (`smallRecordG1` to `smallRecordG3`,
`smallRecordStages`: all under the rule `johnson`, with the integers m = 483, 600, 600), the link's
shape, the chain's codes, and the plan's 25 entries, of which the first is the entry RECORD. Each
theorem is one closed statement on the planner, proved by `decide +kernel`, at once or turn by turn
(see below): the table (`small_record_table`, `small_record_admitted`, `small_record_index`), the
columns of a link (`small_record_first`, `small_record_further`: 51 and 51), the shape and the load
from which the first group is solved (`small_record_shape1`, `small_record_load`), the first group
(`small_record_group`), the two later stages (`small_record_stage2`, `small_record_stage3`), the
numbering of the codes (`small_record_numbering`), the link's shape (`small_record_linkShape`), and
the finished plan (`small_record_finish`): `finishHeld` returns a plan only if `Planned.holds` says
yes of it, so every round of this plan holds in the planner's reckoning. That reckoning counts a
round's proof of work toward the target: four entries have 32 bits of work (LINK, the two CS, BASE).
OnBytes/Params/EntryParamsRecordSmall.lean puts them together.

How the first group and the later stages are proved. Each is an iteration of turns
(`solveGroupFrom`, `solveStageFrom`, OnBytes/Params/Group.lean), and Lean, when it was measured,
held several GiB of memory while it checked one evaluation of a whole iteration: the more, the
longer the single evaluation ran. So each turn has a closed statement of its own
(`small_record_group_turn1` to `small_record_stage3_turn3`), proved by `decide +kernel`, with the
turn's answer typed; each later stage's shape is typed too (`smallRecordShape2` to
`smallRecordShape3`, with `small_record_stage2_shape` and its like); and the theorem is joined from
these by the laws of OnBytes/Params/SolveSteps.lean. The typed middle values were printed by Lean's
evaluator and laid in by a program; each is checked by the kernel in its own statement, so none is
taken on trust.

Why this file imports OnBytes/Params/EntryStagesRecord.lean. It uses nothing of that file. The line
stands so that a build never checks the two files at one time: each holds several GiB of memory
while Lean checks it, and nothing else orders them.

Main definitions: `smallRecordLines`, `smallRecordSet`, `smallRecordTable`, `smallRecordG1` to
`smallRecordG3`, `smallRecordStages`, `smallRecordShape1`, `smallRecordLink`, `smallRecordCodes`,
`smallRecordEntries`, `smallRecordPlan`.
Main theorems: `small_record_table`, `small_record_admitted`, `small_record_first`,
`small_record_further`, `small_record_index`, `small_record_shape1`, `small_record_load`,
`small_record_group`, `small_record_stage2`, `small_record_stage3`, `small_record_numbering`,
`small_record_linkShape`, `small_record_finish`.
What is not claimed: what the head of OnBytes/Params/EntryStagesRecord.lean does not claim, read at
the small example. The typed values were printed by Lean's evaluator and laid in by a program; the
theorems check them. For proofs only; the program, that is the Lean port built from OnBytes/, does
not import this file.

-/
import OnBytes.Params.SolveSteps
import OnBytes.Params.EntryStagesRecord

set_option autoImplicit false

namespace OnBytes.Params

/-- A value typed for what the first 32 lines of the small parameter file of the setting "record
with work" say. -/
def smallRecordLines : Lines where
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
  link := ⟨18, 17, 17, 13,
    [⟨4, 3, 17, 17⟩, ⟨3, 3, 16, 16⟩, ⟨3, 3, 15, 15⟩, ⟨0, 0, 15, 15⟩]⟩
  folded := ⟨17, 15, 13, 6,
    [⟨4, 2, 14, 12⟩, ⟨0, 0, 14, 14⟩]⟩
  omega := ⟨18, 14, 13, 6,
    [⟨4, 3, 14, 13⟩, ⟨0, 0, 15, 15⟩]⟩
  own := ⟨18, 14, 13, 8,
    [⟨4, 3, 14, 13⟩, ⟨0, 0, 15, 15⟩]⟩
  onceFolded := ⟨17, 15, 13, 6,
    [⟨4, 2, 14, 12⟩, ⟨0, 0, 14, 14⟩]⟩
  onceOmega := ⟨18, 14, 13, 6,
    [⟨4, 3, 14, 13⟩, ⟨0, 0, 15, 15⟩]⟩
  onceOwn := ⟨18, 14, 13, 8,
    [⟨4, 3, 14, 13⟩, ⟨0, 0, 15, 15⟩]⟩
  onceRanges := ⟨22, 18, 16, 10,
    [⟨4, 3, 19, 17⟩, ⟨3, 3, 17, 17⟩, ⟨0, 0, 20, 20⟩]⟩
  rangesPart := 14
  tableRowsLog := 8
  tableLogN := 23
  tableData := 524288
  tableRandom := 65535
  blockLog := 11

/-- The setting of these lines. -/
def smallRecordSet : Setting := settingOf smallRecordLines

/-- The table as it is sized at these lines. -/
def smallRecordTable : TableSize := ⟨⟨23, 524288, 65535, false⟩, 8, 1, ⟨0, 0, 82, 82⟩⟩

/-- The group of stage 1 of the test in an entry's chain. -/
def smallRecordG1 : GroupSize :=
  ⟨⟨17, 32768, 97, true⟩, ⟨13, 64, 97, true⟩, 6, 0, 1, .johnson, 483⟩

/-- The group of stage 2 of the test in an entry's chain. -/
def smallRecordG2 : GroupSize :=
  ⟨⟨14, 2048, 66, true⟩, ⟨12, 128, 66, true⟩, 4, 2, 1, .johnson, 600⟩

/-- The group of stage 3 of the test in an entry's chain. -/
def smallRecordG3 : GroupSize :=
  ⟨⟨14, 2048, 66, true⟩, ⟨14, 512, 66, true⟩, 0, 0, 1, .johnson, 600⟩

/-- The three stages of that test. -/
def smallRecordStages : List StageSize :=
  [⟨smallRecordG1, 97, 0⟩, ⟨smallRecordG2, 66, 93⟩, ⟨smallRecordG3, 66, 58⟩]

/-- The shape from which the first group is solved. -/
def smallRecordShape1 : GroupSize :=
  ⟨⟨17, 32768, 0, true⟩, ⟨13, 64, 0, true⟩, 6, 0, 1, .johnson, 0⟩

/-- The link's shape. -/
def smallRecordLink : LinkShape :=
  ⟨⟨⟨23, 524288, 65535⟩, 8, 1, 40⟩, 51, 51, 0, 0, 18, true, 0, true, [⟨1, 1, 4, 2⟩, ⟨1, 2, 0, 0⟩],
  ⟨true⟩⟩

/-- The chain's codes. -/
def smallRecordCodes : Codes :=
  ⟨#[⟨17, 32768, 97⟩, ⟨14, 2048, 66⟩], #[⟨13, 64, 97⟩, ⟨12, 128, 66⟩, ⟨14, 512, 66⟩]⟩

/-- The plan's 25 entries. -/
def smallRecordEntries : List Fmt.Entry :=
  [⟨"RECORD", 1, 0, 0, 0, 0, 20, 1, 0, 0, 0, 0⟩, ⟨"LINK point", 1, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0⟩,
  ⟨"SEND seed", 1, 0, 32, 1, 0, 21, 1, 0, 0, 0, 0⟩, ⟨"SEND answer", 1, 0, 48, 0, 2, 0, 0, 0, 0, 0,
  0⟩, ⟨"LINK", 1, 32, 0, 0, 0, 0, 0, 102, 23, 0, 0⟩, ⟨"LINK phi", 1, 0, 0, 0, 0, 19, 0, 0, 0, 0,
  0⟩, ⟨"BAT", 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 107⟩, ⟨"FOLD epsilon", 1, 0, 24, 0, 0, 1, 0, 0, 0, 0,
  0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0,
  0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0,
  0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0,
  0, 0, 0, 0⟩, ⟨"SEND seed", 1, 0, 32, 1, 0, 17, 1, 0, 0, 0, 0⟩, ⟨"CS", 1, 32, 24, 0, 1, 1, 0, 97,
  17, 0, 293⟩, ⟨"FOLD epsilon", 1, 0, 24, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0,
  1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0,
  0, 1, 0, 0, 0, 0, 0⟩, ⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"SEND seed", 1, 0, 32,
  1, 0, 13, 1, 0, 0, 0, 0⟩, ⟨"CS", 1, 32, 24, 0, 1, 1, 0, 66, 14, 0, 200⟩, ⟨"BASE lambda", 1, 0,
  24, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨"BASE", 1, 32, 64608, 0, 0, 0, 0, 66, 14, 0, 0⟩]

/-- The plan typed for an entry's chain. -/
def smallRecordPlan : Fmt.Plan := ⟨.two, 40, 8, 0, 1, 1, smallRecordEntries⟩

/-- The table as `deriveTable` sizes it. -/
theorem small_record_table :
    deriveTable smallRecordSet smallRecordLines = some smallRecordTable := by decide +kernel

/-- The table is admitted at its analysis. -/
theorem small_record_admitted :
    tableAdmitted smallRecordTable (tableAnalysis smallRecordSet smallRecordTable) = true := by
  decide +kernel

/-- The columns of the first table in a link. -/
theorem small_record_first : scopePositions smallRecordSet .once
    (tableAnalysis smallRecordSet smallRecordTable).later.agree = 51 := by decide +kernel

/-- The columns of the further table in a link. -/
theorem small_record_further :
    scopePositions smallRecordSet .once
      (tableAnalysis smallRecordSet smallRecordTable).once.agree = 51 := by
  decide +kernel

/-- The two tests of `linkSized` on the index's shape pass. -/
theorem small_record_index : (decide (40 < (indexShapeOf smallRecordSet smallRecordTable).v) ||
    decide ((indexShapeOf smallRecordSet smallRecordTable).code.ell ≤
      3 * (indexShapeOf smallRecordSet smallRecordTable).answers)) = false := by decide +kernel

/-- The shape from which `linkSized` has the first group solved. -/
theorem small_record_shape1 : shapeOf smallRecordLines.onceFolded (1 + clog2 (linRowsOf
    (foldedEntries (indexShapeOf smallRecordSet smallRecordTable) + smallRecordSet.samples)
    (2 ^ smallRecordLines.onceFolded.logL) true)) true = smallRecordShape1 := by decide +kernel

/-- The load under which it is solved. -/
theorem small_record_load : (⟨stageCubeBits smallRecordShape1, 2,
    2 * (indexShapeOf smallRecordSet smallRecordTable).answers + 51 + 51 + 1 +
      2 * smallRecordSet.samples⟩ : GroupLoad) = ⟨22, 2, 107⟩ := by decide +kernel

/-- Turn 1 of the first group, from 0 positions. -/
theorem small_record_group_turn1 : turn smallRecordSet .once ⟨22, 2, 107⟩ smallRecordShape1
    (tailFor (id 0)) (tailFor 0) 0 =
      .more ⟨⟨17, 32768, 0, true⟩, ⟨13, 64, 0, true⟩, 6, 0, 1, .johnson, 482⟩ 97 := by
  decide +kernel

/-- Turn 2 of the first group, from 97 positions. -/
theorem small_record_group_turn2 : turn smallRecordSet .once ⟨22, 2, 107⟩ smallRecordShape1
    (tailFor (id 97)) (tailFor 97) 97 =
      .settled smallRecordG1 97 := by
  decide +kernel

/-- The first group as it is solved. -/
theorem small_record_group :
    solveGroup smallRecordSet .once ⟨22, 2, 107⟩ id smallRecordShape1 =
      some ⟨smallRecordG1, 97⟩ := by
  unfold solveGroup
  exact (solveGroupFrom_more _ _ _ _ _ 31 0 _ _ small_record_group_turn1).trans
    ((solveGroupFrom_settled _ _ _ _ _ 30 97 _ _ small_record_group_turn2 rfl))

/-- The shape from which stage 2 is solved. -/
def smallRecordShape2 : GroupSize :=
  ⟨⟨14, 2048, 0, true⟩, ⟨12, 128, 0, true⟩, 4, 2, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem small_record_stage2_shape :
    laterShape smallRecordSet smallRecordG1 ⟨4, 2, 14, 12⟩ = smallRecordShape2 := by
  decide +kernel

/-- Turn 1 of stage 2, from 0 positions. -/
theorem small_record_stage2_turn1 : turn smallRecordSet .once
    ⟨stageCubeBits smallRecordShape2, 1, 4 + 3 * max smallRecordG1.main.r 1024⟩ smallRecordShape2
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨14, 2048, 0, true⟩, ⟨12, 128, 0, true⟩, 4, 2, 1, .johnson, 594⟩ 65 := by
  decide +kernel

/-- Turn 2 of stage 2, from 65 positions. -/
theorem small_record_stage2_turn2 : turn smallRecordSet .once
    ⟨stageCubeBits smallRecordShape2, 1, 4 + 3 * max smallRecordG1.main.r 1024⟩ smallRecordShape2
    (tailFor 65) (tailFor 65) 65 =
      .more ⟨⟨14, 2048, 65, true⟩, ⟨12, 128, 65, true⟩, 4, 2, 1, .johnson, 600⟩ 66 := by
  decide +kernel

/-- Turn 3 of stage 2, from 66 positions. -/
theorem small_record_stage2_turn3 : turn smallRecordSet .once
    ⟨stageCubeBits smallRecordShape2, 1, 4 + 3 * max smallRecordG1.main.r 1024⟩ smallRecordShape2
    (tailFor 66) (tailFor 66) 66 =
      .settled smallRecordG2 66 := by
  decide +kernel

/-- Stage 2 as it is solved. -/
theorem small_record_stage2 : solveStageFrom smallRecordSet .once smallRecordG1.main.r
    (laterShape smallRecordSet smallRecordG1 ⟨4, 2, 14, 12⟩) 32 0 = some ⟨smallRecordG2, 66⟩ := by
  rw [small_record_stage2_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ small_record_stage2_turn1).trans
    ((solveStageFrom_more _ _ _ _ 30 65 _ _ small_record_stage2_turn2).trans
    ((solveStageFrom_settled _ _ _ _ 29 66 _ _ small_record_stage2_turn3)))

/-- The shape from which stage 3 is solved. -/
def smallRecordShape3 : GroupSize :=
  ⟨⟨14, 2048, 0, true⟩, ⟨14, 512, 0, true⟩, 0, 0, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem small_record_stage3_shape :
    laterShape smallRecordSet smallRecordG2 ⟨0, 0, 14, 14⟩ = smallRecordShape3 := by
  decide +kernel

/-- Turn 1 of stage 3, from 0 positions. -/
theorem small_record_stage3_turn1 : turn smallRecordSet .once
    ⟨stageCubeBits smallRecordShape3, 1, 4 + 3 * max smallRecordG2.main.r 1024⟩ smallRecordShape3
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨14, 2048, 0, true⟩, ⟨14, 512, 0, true⟩, 0, 0, 1, .johnson, 594⟩ 65 := by
  decide +kernel

/-- Turn 2 of stage 3, from 65 positions. -/
theorem small_record_stage3_turn2 : turn smallRecordSet .once
    ⟨stageCubeBits smallRecordShape3, 1, 4 + 3 * max smallRecordG2.main.r 1024⟩ smallRecordShape3
    (tailFor 65) (tailFor 65) 65 =
      .more ⟨⟨14, 2048, 65, true⟩, ⟨14, 512, 65, true⟩, 0, 0, 1, .johnson, 600⟩ 66 := by
  decide +kernel

/-- Turn 3 of stage 3, from 66 positions. -/
theorem small_record_stage3_turn3 : turn smallRecordSet .once
    ⟨stageCubeBits smallRecordShape3, 1, 4 + 3 * max smallRecordG2.main.r 1024⟩ smallRecordShape3
    (tailFor 66) (tailFor 66) 66 =
      .settled smallRecordG3 66 := by
  decide +kernel

/-- Stage 3, the last, as it is solved. -/
theorem small_record_stage3 : solveStageFrom smallRecordSet .once smallRecordG2.main.r
    (laterShape smallRecordSet smallRecordG2 ⟨0, 0, 14, 14⟩) 32 0 = some ⟨smallRecordG3, 66⟩ := by
  rw [small_record_stage3_shape]
  exact (solveStageFrom_more _ _ _ _ 31 0 _ _ small_record_stage3_turn1).trans
    ((solveStageFrom_more _ _ _ _ 30 65 _ _ small_record_stage3_turn2).trans
    ((solveStageFrom_settled _ _ _ _ 29 66 _ _ small_record_stage3_turn3)))

/-- The numbering of the codes of the typed stages, from an empty list of codes. -/
theorem small_record_numbering : ioppStages smallRecordStages {} =
    (⟨0, 0, 6, 0⟩ :: smallRecordLink.later, smallRecordCodes) := by decide +kernel

/-- The link's shape as `linkSized` puts it together. -/
theorem small_record_linkShape : (⟨indexShapeOf smallRecordSet smallRecordTable, 51, 51, 0, 0,
    linRowsOf (foldedEntries (indexShapeOf smallRecordSet smallRecordTable) +
      smallRecordSet.samples) (2 ^ smallRecordLines.onceFolded.logL) true,
    true, 0, true, smallRecordLink.later, ⟨true⟩⟩ : LinkShape) = smallRecordLink := by
  decide +kernel

/-- The plan of an entry's chain at the typed sizes is finished and holds, and has the typed entries
and the setting's four numbers. -/
theorem small_record_finish : ((finishHeld smallRecordSet .once
    (linkPlan ⟨smallRecordLink, smallRecordTable,
      ⟨smallRecordG1, 97, smallRecordStages⟩⟩)).toOption.any fun P =>
      decide (P.rounds.map (·.entry) = smallRecordEntries) && decide (P.set.saltBytes = 40) &&
        decide (P.set.nonceBytes = 8) && decide (P.set.positionBytes = 0) &&
        decide (P.set.samples = 1)) = true := by decide +kernel

end OnBytes.Params
