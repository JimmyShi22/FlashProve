-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/MemberSetting.lean: the setting of the smallness test's first half
(Johnson/Desc/First/K8/Hear.lean) at the library's written setting of the full-size parameter lines
(`recordSet`, OnBytes/Params/EntryStagesRecord.lean). One closed test at a written value; and at
that value the example of Johnson/Desc/First/K8/Member.lean. (In `recordSet`, `record_setting`,
`at_record` and `both_at_record` the word "record" comes from that setting's name, "record with
work", in which the stored table has an out-of-domain sample (lean/GLOSSARY.md, "record").)

Why. `AtWritten st p x` (Johnson/Desc/First/K8/Member.lean) has the setting as a free variable, and
by the text of `rngCombinations` (OnBytes/Params/Planner.lean) the setting with the target t, no
work and one instance gives t combinations, for every t. Here the setting is a written value, of
which a theorem on the public files in scope speaks (Johnson/Goal/Numbers/K8SettingInScope.lean). So
the example stands at a written setting, not only at the structure's default.

Statements and proofs.
  `record_setting`: the written setting passes `settingB` (Johnson/Desc/First/K8/MemberPlace.lean):
    128 combinations for a request's own part, no work for this round, at most one instance. By
    `decide`. Three settings at which `settingB` says no: Johnson/Desc/First/K8/MemberTeeth.lean.
  `at_record`: at the written setting every place with `AtWritten` has 128 combinations and 24,086
    or 10,248 or 20,703 columns.
  `both_at_record`: `AtWritten` and `ReadyAt` hold together there, for each of the three sorts of
    written rounds, at the made-up place and state of Johnson/Desc/First/K8/Member.lean.

Limits. Tools, and a fact on a written value. Not claimed: that the planner runs its routine for
this round under this setting. Not claimed: that the written list is what the planner makes of the
public files (see the head of Johnson/G/DryProofLit.lean; what is shown elsewhere of the data that
are made of this list: the Limits of Johnson/Desc/First/K8/Member.lean): `at_record` brings together
a written setting and a round of a written list, and nothing here ties the one to the other. The
place and the state of `both_at_record` are made up, with the limits that the head of
Johnson/Desc/First/K8/Member.lean tells. No statement here names a description of the protocol.
Nothing on soundness.
-/
import Johnson.Desc.First.K8.Member
import OnBytes.Params.EntryStagesRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Member

open OnBytes.Params (recordSet)

/-- **The written setting passes the test on a setting.** -/
theorem record_setting : settingB recordSet = true := by decide

/-- **At the written setting**: 128 combinations, and one of the three sums of columns. -/
theorem at_record {p : Par} {x : Fmt.Round × List Fmt.Stored} (A : AtWritten recordSet p x) :
    p.tau = 128 ∧ columns p ∈ [24086, 10248, 20703] := at_128 record_setting A

/-- The two premises together, at the written setting. -/
theorem both_at_record {n : Nat} (h : n ∈ [3083008, 1311744, 2649984]) :
    ∃ x : Fmt.Round × List Fmt.Stored, x.1.entry.trits = n ∧
      AtWritten recordSet (madeUpPar (n / 128 - 1)) x ∧
      ReadyAt (madeUpPar (n / 128 - 1)) (toyIn (madeUpTl (n / 128 - 1)))
        (madeUpTl (n / 128 - 1)) := exists_both record_setting h

end VerifiableInference.Desc.First.K8.Member

#print axioms VerifiableInference.Desc.First.K8.Member.record_setting
#print axioms VerifiableInference.Desc.First.K8.Member.at_record
#print axioms VerifiableInference.Desc.First.K8.Member.both_at_record
