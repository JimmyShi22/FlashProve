-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/K8SettingInScope.lean: the setting of the smallness test's first half
(Johnson/Desc/First/K8/Hear.lean) at the public files in the goals' scope (`VerifierAndGoals.InScope`,
Ladder.lean): a law, an example and three negative statements. Theorems alone: no definition is made
here, so no statement is laid down by name.

What it is. Tools beneath the rows on that block (propositions stated by name, each with a theorem
of just that type: Johnson/Desc/First/K8/LawRowsText.lean); no row is stated or changed. By the
planner's text, the planner makes the proof file's first chain, the one chain with rounds that draw
matrix entries, under the setting in the proof file's sizes, `made.sized.proof.set` (`firstPlan`,
OnBytes/Params/DeriveReq.lean). In scope that field is the library's written setting: the lines that
the planner has read are the written lines (`frame_at_scope`,
Johnson/Goal/PlanValues/KeyPlansAtScope.lean), and the proof's sizes have the lines' setting
(`configure_proof_sizes`, OnBytes/Plan/PlanListsProof.lean). The written setting passes `settingB`
(`record_setting`, Johnson/Desc/First/K8/MemberSetting.lean). So in scope, where the planner
returns, that field passes `settingB` by a theorem.

  `proof_set_at_scope`: in scope the setting in the proof file's sizes is `recordSet`. `sets_agree`:
    it is the setting of all sizes, `made.sized.set` (`set_at_scope`, same file as
    `frame_at_scope`).
  `made_setting`: in scope the setting in the proof file's sizes passes `settingB`: 128 combinations
    for a request's own part, no work for this round, at most one instance.
  `at_scope`: so each place with `AtWritten` (Johnson/Desc/First/K8/Member.lean) at that setting has
    128 combinations and 24,086 or 10,248 or 20,703 columns.
  `exists_at_scope`: for each of the three sorts there is a round of the written list, a place and a
    state with `AtWritten` at that setting and `ReadyAt` together: `at_scope` is about something
    wherever the planner returns a value in scope. The place and the state are the made-up ones of
    Johnson/Desc/First/K8/Member.lean.
  `half_not_at_scope`: the place with 64 combinations and twice the columns (`halfPar`,
    Johnson/Desc/First/K8/MemberTeeth.lean), which declares the same round, has `AtWritten` at that
    setting with no round. `place_half_record_no`, `place_half_scope_no`: the test `placeOk` says no
    of it at the written setting, and so in scope.

What of OnBytes/Model/ is used. `Model.Verify.planned`, `Model.Verify.Planned`, by name, in the
statements.

Limits. All statements but `place_half_record_no` have the premise that the planner returns. That it
returns is shown by no theorem in this file, and none is known in the files that it imports. In
other files the two premises of these statements are met at the library's written copy of the
full-size public files (`VerifierAndGoals.storedPublicFiles`: three terms written in Lean; no theorem ties them to the
repository's files): that the files are in scope by `VerifierAndGoals.inScope_full`
(Johnson/Goal/Files/ScopeExample.lean); that the planner returns by
`AtFullSide.Planner.planned_zFull_returns` (AtFullSide/Planner/MadeReturns.lean), at the format's
second hash function (`OnBytes.secondHashFunction`) and the files' own digest, in a side library outside the
main library (one constant beneath it passes Lean's kernel only at a larger thread stack; Lean's
re-checker, leanchecker, was run on it and fails there at each shell stack limit that was tried; the
toolchain's own replay passes it at a larger thread stack; so that constant has been checked by the
kernel in the build and by that replay, and by no independent program); no independent checker has
replayed any of the closed facts beneath it, and the full-size example's weights are synthetic.
These two theorems speak of `VerifierAndGoals.storedPublicFiles` alone, not of other files in scope.
That `firstPlan` is run under
`made.sized.proof.set`, and that no other chain has rounds that draw matrix entries, is read off the
planner's text; no statement here says so. The place is a free variable: that its number of
combinations is the setting's is a field of `AtWritten`, a premise; no description asks `AtWritten`,
`placeOk` or `settingB`. That the written list is what the planner makes of the public files is not
shown here (see the head of Johnson/G/DryProofLit.lean). What is shown elsewhere of the data that
are made of this list: the Limits of Johnson/Desc/First/K8/Member.lean. Of a place all but tau, the
columns' sum and four conditions of form stays free. The closed tests are by `decide`. No statement
here names a description. Out of scope nothing is said. Nothing on soundness.
-/
import Johnson.Desc.First.K8.MemberSetting
import Johnson.Desc.First.K8.MemberTeeth
import Johnson.Goal.PlanValues.KeyPlansAtScope
import OnBytes.Plan.PlanListsProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Member

open OnBytes.Model.Verify (planned Planned)
open OnBytes.Params (recordSet)

/-- In scope the setting in the proof file's sizes is the written setting. -/
theorem proof_set_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) :
    p.chains.made.sized.proof.set = recordSet := by
  obtain ⟨_, shapes, cfg, hc⟩ := Lk6.AtPlan.frame_at_scope hZ hp
  exact (OnBytes.Params.configure_proof_sizes hc).2.1

/-- In scope it is the setting of all sizes. -/
theorem sets_agree {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) :
    p.chains.made.sized.proof.set = p.chains.made.sized.set :=
  (proof_set_at_scope hZ hp).trans (Lk6.AtPlan.set_at_scope hZ hp).symm

/-- **In scope the setting in the proof file's sizes passes the test on a setting.** -/
theorem made_setting {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) :
    settingB p.chains.made.sized.proof.set = true := by
  rw [proof_set_at_scope hZ hp]
  exact record_setting

/-- **In scope, at that setting**: 128 combinations, and one of the three sums of columns. -/
theorem at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) {q : Par}
    {x : Fmt.Round × List Fmt.Stored} (A : AtWritten p.chains.made.sized.proof.set q x) :
    q.tau = 128 ∧ columns q ∈ [24086, 10248, 20703] := at_128 (made_setting hZ hp) A

/-- In scope, at that setting, `AtWritten` and `ReadyAt` hold together for each of the three sorts.
-/
theorem exists_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) {n : Nat}
    (h : n ∈ [3083008, 1311744, 2649984]) :
    ∃ x : Fmt.Round × List Fmt.Stored, x.1.entry.trits = n ∧
      AtWritten p.chains.made.sized.proof.set (madeUpPar (n / 128 - 1)) x ∧
      ReadyAt (madeUpPar (n / 128 - 1)) (toyIn (madeUpTl (n / 128 - 1)))
        (madeUpTl (n / 128 - 1)) := exists_both (made_setting hZ hp) h

/-- In scope the place with 64 combinations and twice the columns has `AtWritten` with no round. -/
theorem half_not_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) (x : Fmt.Round × List Fmt.Stored) :
    ¬ AtWritten p.chains.made.sized.proof.set halfPar x :=
  fun A => absurd (at_scope hZ hp A).1 (by decide)

/-- At the written setting the test on the place says no of it. -/
theorem place_half_record_no : placeOk recordSet halfPar firstSort = false := by decide

/-- So it does in scope. -/
theorem place_half_scope_no {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) :
    placeOk p.chains.made.sized.proof.set halfPar firstSort = false := by
  rw [proof_set_at_scope hZ hp]
  exact place_half_record_no

end VerifiableInference.Desc.First.K8.Member

#print axioms VerifiableInference.Desc.First.K8.Member.proof_set_at_scope
#print axioms VerifiableInference.Desc.First.K8.Member.sets_agree
#print axioms VerifiableInference.Desc.First.K8.Member.made_setting
#print axioms VerifiableInference.Desc.First.K8.Member.at_scope
#print axioms VerifiableInference.Desc.First.K8.Member.exists_at_scope
#print axioms VerifiableInference.Desc.First.K8.Member.half_not_at_scope
#print axioms VerifiableInference.Desc.First.K8.Member.place_half_record_no
#print axioms VerifiableInference.Desc.First.K8.Member.place_half_scope_no
