-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryParamsRecord.lean: at the lines typed for the full-size parameter file of the
setting "record with work", `entrySized` answers, and what it returns is typed.

OnBytes/Params/EntryStagesRecord.lean has the parts, each by an evaluation in Lean's kernel;
OnBytes/Params/SizedForward.lean has the laws that put parts together. Here: the four later stages
of the test in an entry's chain (`record_later`), the test (`record_test`), the link
(`record_link`), and the whole: `entrySized recordLines` answers, with the typed link, table, test
and codes, and with a plan that holds in the planner's reckoning and is written as the typed plan
(`record_sized`). The typed plan fits the format's words (`recordPlan_fit`), so that by
OnBytes/Params/ReadBackPlan.lean the reader, where it returns a value, returns the plan as it was
spelled. Its first entry is the entry for the table's own sample, and the chain's rounds are the
other 41 (`recordPlan_record`).

Main theorems: `record_later`, `record_test`, `record_link`, `record_sized`, `recordPlan_fit`,
`recordPlan_record`.
What is not claimed: what the head of OnBytes/Params/EntryStagesRecord.lean does not claim: above
all nothing on what a round's price is worth under the rule `johnson`, and not which rounds hold
without their work. No parameter bytes are typed here, and no digest, and nothing is read or run
dry: OnBytes/Params/EntryDryRecord.lean does that. For proofs only; the program, that is the Lean
port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.EntryStagesRecord
import OnBytes.Params.ReadBackPlan

set_option autoImplicit false

namespace OnBytes.Params

/-- The four later stages follow from the first group, one step of `solveLater` after the other. -/
theorem record_later : solveLater recordSet .once recordG1
    [⟨5, 2, 21, 12⟩, ⟨4, 2, 17, 12⟩, ⟨4, 2, 13, 12⟩, ⟨0, 0, 14, 14⟩] = some recordStages.tail := by
  rw [solveLater_step (by decide) record_stage2, solveLater_step (by decide) record_stage3,
    solveLater_step (by decide) record_stage4, solveLater_step (by decide) record_stage5]
  decide

/-- The test in an entry's chain as it is solved. -/
theorem record_test :
    solveTest recordSet .once recordLines.onceFolded ⟨31, 2, 129⟩ id recordShape1 =
      some ⟨recordG1, 97, recordStages⟩ :=
  solveTest_of (x := ⟨recordG1, 97⟩) record_group (solveStages_of (by decide) record_later)

/-- The link as it is sized. -/
theorem record_link : linkSized recordSet recordLines recordTable {} =
    some (⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩, recordCodes) := by
  have h := linkSized_of (s := recordSet) (l := recordLines) (T := recordTable) (codes := {})
    (x := ⟨recordG1, 97, recordStages⟩) record_admitted record_first record_further (by decide)
    record_index (by rw [record_shape1, record_load]; exact record_test) record_numbering
  rw [h]
  have e := record_linkShape
  exact congrArg (fun S : LinkShape =>
    some ((⟨S, recordTable, ⟨recordG1, 97, recordStages⟩⟩ : LinkSized), recordCodes)) e

/-- **At `recordLines`, `entrySized` answers**: with the typed link, table, test and codes, and with
a plan that holds in the planner's reckoning and is written as the typed plan. -/
theorem record_sized : ∃ P, entrySized recordLines =
      .ok (⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩, recordCodes, P) ∧
    P.plan = recordPlan ∧ P.holds = true := by
  have hp := record_finish
  cases hP : finishHeld recordSet .once
      (linkPlan ⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩) with
  | error e =>
    rw [hP] at hp
    cases hp
  | ok P =>
    rw [hP] at hp
    simp only [Except.toOption, Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩ := hp
    refine ⟨P, entrySized_of record_table record_link hP, ?_, finishHeld_holds hP⟩
    show (⟨.two, P.set.saltBytes, P.set.nonceBytes, P.set.positionBytes, P.set.samples, 1,
      P.rounds.map (·.entry)⟩ : Fmt.Plan) = recordPlan
    rw [b1, b2, b3, b4, b5]
    rfl

/-- The typed plan fits the format's words. -/
theorem recordPlan_fit : recordPlan.fit = true := by decide +kernel

/-- The typed plan's first entry has the name of the entry for the table's own sample, and the
chain's rounds, which are the entries under other names, are all the others. -/
theorem recordPlan_record : recordPlan.entries.head?.map (·.name) = some Fmt.recordName ∧
    recordPlan.rounds = recordPlan.entries.tail := by decide +kernel

end OnBytes.Params
