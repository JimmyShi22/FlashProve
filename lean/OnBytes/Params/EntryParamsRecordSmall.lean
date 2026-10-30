-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryParamsRecordSmall.lean: at the lines typed for the small parameter file of the
setting "record with work", `entrySized` answers, and what it returns is typed.

The like of OnBytes/Params/EntryParamsRecord.lean at the small example.
OnBytes/Params/EntryStagesRecordSmall.lean has the parts, each by an evaluation in Lean's kernel;
OnBytes/Params/SizedForward.lean has the laws that put parts together. Here: the two later stages of
the test in an entry's chain (`small_record_later`), the test (`small_record_test`), the link
(`small_record_link`), and the whole: `entrySized smallRecordLines` answers, with the typed link,
table, test and codes, and with a plan that holds in the planner's reckoning and is written as the
typed plan (`small_record_sized`). The typed plan fits the format's words (`smallRecordPlan_fit`).
Its first entry is the entry for the table's own sample, and the chain's rounds are the other 24
(`smallRecordPlan_record`).

Main theorems: `small_record_later`, `small_record_test`, `small_record_link`,
`small_record_sized`, `smallRecordPlan_fit`, `smallRecordPlan_record`.
What is not claimed: what the head of OnBytes/Params/EntryParamsRecord.lean does not claim, read at
the small example. For proofs only; the program, that is the Lean port built from OnBytes/, does not
import this file.

-/
import OnBytes.Params.EntryStagesRecordSmall
import OnBytes.Params.ReadBackPlan

set_option autoImplicit false

namespace OnBytes.Params

/-- The two later stages follow from the first group, one step of `solveLater` after the other. -/
theorem small_record_later : solveLater smallRecordSet .once smallRecordG1
    [⟨4, 2, 14, 12⟩, ⟨0, 0, 14, 14⟩] = some smallRecordStages.tail := by
  rw [solveLater_step (by decide) small_record_stage2,
    solveLater_step (by decide) small_record_stage3]
  decide

/-- The test in an entry's chain as it is solved. -/
theorem small_record_test :
    solveTest smallRecordSet .once smallRecordLines.onceFolded ⟨22, 2, 107⟩ id smallRecordShape1 =
      some ⟨smallRecordG1, 97, smallRecordStages⟩ :=
  solveTest_of (x := ⟨smallRecordG1, 97⟩) small_record_group
    (solveStages_of (by decide) small_record_later)

/-- The link as it is sized. -/
theorem small_record_link : linkSized smallRecordSet smallRecordLines smallRecordTable {} =
    some (⟨smallRecordLink, smallRecordTable, ⟨smallRecordG1, 97, smallRecordStages⟩⟩,
      smallRecordCodes) := by
  have h := linkSized_of (s := smallRecordSet) (l := smallRecordLines) (T := smallRecordTable)
    (codes := {}) (x := ⟨smallRecordG1, 97, smallRecordStages⟩) small_record_admitted
    small_record_first small_record_further (by decide) small_record_index
    (by rw [small_record_shape1, small_record_load]; exact small_record_test)
    small_record_numbering
  rw [h]
  have e := small_record_linkShape
  exact congrArg (fun S : LinkShape =>
    some ((⟨S, smallRecordTable, ⟨smallRecordG1, 97, smallRecordStages⟩⟩ : LinkSized),
      smallRecordCodes)) e

/-- **At `smallRecordLines`, `entrySized` answers**: with the typed link, table, test and codes, and
with a plan that holds in the planner's reckoning and is written as the typed plan. -/
theorem small_record_sized : ∃ P, entrySized smallRecordLines =
      .ok (⟨smallRecordLink, smallRecordTable, ⟨smallRecordG1, 97, smallRecordStages⟩⟩,
        smallRecordCodes, P) ∧
    P.plan = smallRecordPlan ∧ P.holds = true := by
  have hp := small_record_finish
  cases hP : finishHeld smallRecordSet .once
      (linkPlan ⟨smallRecordLink, smallRecordTable, ⟨smallRecordG1, 97, smallRecordStages⟩⟩) with
  | error e =>
    rw [hP] at hp
    cases hp
  | ok P =>
    rw [hP] at hp
    simp only [Except.toOption, Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩ := hp
    refine ⟨P, entrySized_of small_record_table small_record_link hP, ?_, finishHeld_holds hP⟩
    show (⟨.two, P.set.saltBytes, P.set.nonceBytes, P.set.positionBytes, P.set.samples, 1,
      P.rounds.map (·.entry)⟩ : Fmt.Plan) = smallRecordPlan
    rw [b1, b2, b3, b4, b5]
    rfl

/-- The typed plan fits the format's words. -/
theorem smallRecordPlan_fit : smallRecordPlan.fit = true := by decide +kernel

/-- The typed plan's first entry has the name of the entry for the table's own sample, and the
chain's rounds, which are the entries under other names, are all the others. -/
theorem smallRecordPlan_record :
    smallRecordPlan.entries.head?.map (·.name) = some Fmt.recordName ∧
      smallRecordPlan.rounds = smallRecordPlan.entries.tail := by decide +kernel

end OnBytes.Params
