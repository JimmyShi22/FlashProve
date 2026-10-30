-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyLawsOption.lean: the option `-no-proof-of-work`, and a named policy, in a call
that ends with a passing result.

By its description (`CpId`, OnBytes/Model/Stages.lean) the option means: no pass if a round meets
the target only with its work. `cpStagesRun` (same file) forms the result of a call from the results
of its stages and looks at the option there; `readFirst` (OnBytes/Model/VerifyHeads.lean) hands it
on from the options of the call. This file proves that `readFirst` hands it on whatever the kind of
call is, and what follows of the stages' results if a call with the option passes, on one file alone
as in a whole call.

Main theorems.
- `readFirst_option`, `readCall_option`: in what the first tests of a call return, the field for
  `-no-proof-of-work` is the options' field, and the field `policyGiven` says whether the options
  hold a policy. `readFirst_option` holds for both values of `needed`.
- `cpStagesRun_option`: if the result of a call is a passing one and the field for the option is
  set, then `passedWithWork` and `recordNeedsWork` are both false of the stages' results: no stage
  passed with a note on work, and the record of the last stage does not say that some round meets
  the target only with its work. The statement has no condition on `id.needed`, `part` or `about`.
- `wholeCall_option`, `partCall_option`, `keyCall_option`, `leafCall_option`: the same for a whole
  call and for the calls on one file alone, of the results of the stages that the call ran, with the
  option in the options of the call.
- `wholeCall_within`, by `cpStagesRun_within`: at a result within limits the options hold a policy.

What is not claimed. Nothing on soundness. Nothing on whether the stages' notes on work and their
records are right: they are taken as the stages give them, and no theorem here says how a stage
counts a round's work or compares a round with the target. On work, nothing on a call without the
option. Nothing on a call that does not pass: that a call with the option ends as not a verification
where work is needed is not stated. Nothing says that some files make a call pass. How the options
as read follow from the arguments of the command is not stated here: see
OnBytes/Shell/AtOption.lean. The program is the Lean text `verify-on-bytes`; nothing here is said
of the C++ program `cp_verify` or of how its results compare. For proofs only; the program does not
import this file.
-/
import OnBytes.Model.VerifyLawsId

set_option autoImplicit false

namespace OnBytes.Model

open OnBytes.Params (exc_bind exc_guard exc_either)

namespace Stages

/-- A stage's result that still has a record as the call reads it is read unchanged. -/
theorem asRead_same {x : StageOut} (h : x.asRead.acct.isNone = false) : x.asRead = x := by
  cases x with
  | mk name ending idHex acct work why =>
    cases acct with
    | none => simp [StageOut.asRead] at h
    | some a =>
      by_cases ht : Acct.taken a = true
      · simp [StageOut.asRead, Option.filter, ht]
      · simp [StageOut.asRead, Option.filter, ht] at h

/-- If the result of a call is a passing one, `StageOut.asRead` leaves every stage's result
unchanged. A remark on the code, no part of the statement: `cpStagesRun` works on the results as
`StageOut.asRead` gives them, so in a call that passes it works on the results themselves. -/
theorem cpStagesRun_asRead {stages : List StageOut} {part : Option StageName} {belowBar : Bool}
    {asked : Nat} {id : CpId} {about : Option (Array UInt32 × PolicyLines)}
    (h : (cpStagesRun stages part belowBar asked id about).passing = true) :
    stages.map StageOut.asRead = stages := by
  have hall : (stages.map StageOut.asRead).any (·.acct.isNone) = false := by
    unfold cpStagesRun at h
    dsimp only at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | skip
    all_goals simp_all
  have : ∀ x ∈ stages, StageOut.asRead x = x := by
    intro x hx
    rw [List.any_eq_false] at hall
    exact asRead_same (Bool.eq_false_iff.mpr (hall x.asRead (List.mem_map_of_mem hx)))
  calc stages.map StageOut.asRead = stages.map (fun x => x) := List.map_congr_left this
    _ = stages := by simp

/-- If the result of a call is a passing one (a yes, a result within limits, or that a part passed)
and `id` says that the call had `-no-proof-of-work`: no stage passed with a note on work, and the
record of the last stage does not say that some round meets the target only with its work. This
holds whatever `id.needed`, `part` and `about` are, so for a call on one file alone too. Whether the
notes and the record are right is not stated. -/
theorem cpStagesRun_option {stages : List StageOut} {part : Option StageName} {belowBar : Bool}
    {asked : Nat} {id : CpId} {about : Option (Array UInt32 × PolicyLines)}
    (h : (cpStagesRun stages part belowBar asked id about).passing = true)
    (ho : id.noProofOfWork = true) :
    passedWithWork stages = false ∧ recordNeedsWork stages = false := by
  have hs := cpStagesRun_asRead h
  unfold cpStagesRun at h
  rw [hs] at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | skip
  all_goals simp_all

/-- If the result of a call is within limits, `id.policyGiven` is set. Here `id` is any `CpId`. Of
the `id` that `readFirst` or `readCall` returns, the field says whether the call's options hold a
policy (`readFirst_option`, `readCall_option`). -/
theorem cpStagesRun_within {stages : List StageOut} {part : Option StageName} {belowBar : Bool}
    {asked : Nat} {id : CpId} {about : Option (Array UInt32 × PolicyLines)} {a : Covered}
    {c : Closing} (h : cpStagesRun stages part belowBar asked id about = .withinLimits a c) :
    id.policyGiven = true := by
  unfold cpStagesRun at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | skip
  all_goals simp_all

end Stages

namespace Verify

open OnBytes.Model.Stages

/-- In what the first tests of a call return, whatever `needed` is: the field for
`-no-proof-of-work` is that of the options, and `policyGiven` says whether the options hold a
policy. -/
theorem readFirst_option {o : Options} {f : Files} {needed : Bool} {r : Read}
    (h : readFirst o f needed = .ok r) :
    r.id.noProofOfWork = o.noProofOfWork ∧ r.id.policyGiven = o.policy.isSome := by
  unfold readFirst at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (obtain ⟨_, ha, _⟩ := exc_bind h
       cases ha
       done)
    | (obtain ⟨asked, _, h⟩ := exc_bind h
       obtain ⟨_, _, h⟩ := exc_bind h
       obtain ⟨_, _, h⟩ := exc_bind h
       obtain ⟨⟨pol, kl, lay⟩, _, h⟩ := exc_bind h
       dsimp only at h
       obtain ⟨key, _, h⟩ := exc_bind h
       obtain ⟨_, _, h⟩ := exc_bind h
       obtain ⟨_, _, h⟩ := exc_bind h
       obtain ⟨_, _, h⟩ := exc_bind h
       cases h
       exact ⟨rfl, rfl⟩)

/-- The first tests of a whole call keep what `readFirst` returns on the field for
`-no-proof-of-work` and on `policyGiven`. -/
theorem readCall_option {o : Options} {f : Files} {r : Read} (h : readCall o f = .ok r) :
    r.id.noProofOfWork = o.noProofOfWork ∧ r.id.policyGiven = o.policy.isSome := by
  unfold readCall at h
  replace h := exc_guard h
  obtain ⟨r0, h0, h⟩ := exc_bind h
  have h1 := readFirst_option h0
  extract_lets next at h
  have hj : next () = .ok r := by
    split at h
    · obtain ⟨_, h⟩ := exc_either h
      exact h
    · obtain ⟨_, _, h⟩ := exc_bind h
      exact h
  obtain ⟨_, _, hj⟩ := exc_bind hj
  obtain ⟨request, _, hj⟩ := exc_bind hj
  obtain ⟨y, _, hj⟩ := exc_bind hj
  obtain ⟨_, hj⟩ := exc_either hj
  obtain ⟨proof, _, hj⟩ := exc_bind hj
  obtain ⟨k, _, hj⟩ := exc_bind hj
  cases hj
  exact h1

/-- A whole call with `-no-proof-of-work` in its options. f is any `Files`. If `entryNumber` returns
a number on f, and `wholeCall` on f with its entry replaced by `entry` returns a passing result,
then for the files r that `readCall` returned on f and the bytes of `entry`: of the three stages'
results (`stagesOf`), none is that of a stage that passed with a note on work, and the record of the
last stage does not say that some round meets the target only with its work. Whether the notes and
the record are right is not stated. -/
theorem wholeCall_option {o : Options} {f : Files} {k : Nat} {entry : FileIn}
    (hk : entryNumber o f = .ok k) (h : (wholeCall o { f with entry := entry }).passing = true)
    (ho : o.noProofOfWork = true) :
    ∃ r ent, readCall o f = .ok r ∧ entry = some ent ∧
      passedWithWork (stagesOf o r ent).1 = false ∧
      recordNeedsWork (stagesOf o r ent).1 = false := by
  obtain ⟨r, ent, p, C, table, further, g1, _, g3, _⟩ := wholeCall_passed hk h
  refine ⟨r, ent, g1, g3, ?_⟩
  subst g3
  unfold wholeCall at h
  rw [readCall_entry, g1] at h
  dsimp only at h
  exact cpStagesRun_option h ((readCall_option g1).1.trans ho)

/-- f is any `Files`. If `entryNumber` returns a number on f, and `wholeCall` on f with its entry
replaced by `entry` ends as within limits, the options hold a policy. -/
theorem wholeCall_within {o : Options} {f : Files} {k : Nat} {entry : FileIn} {a : Covered}
    {c : Closing} (hk : entryNumber o f = .ok k)
    (h : wholeCall o { f with entry := entry } = .withinLimits a c) : o.policy.isSome = true := by
  have hp : (wholeCall o { f with entry := entry }).passing = true := by
    rw [h]
    rfl
  obtain ⟨r, ent, p, C, table, further, g1, _, g3, _⟩ := wholeCall_passed hk hp
  subst g3
  unfold wholeCall at h
  rw [readCall_entry, g1] at h
  dsimp only at h
  exact (readCall_option g1).2.symm.trans (cpStagesRun_within h)

/-- A call on one file alone with `-no-proof-of-work` in its options. If it ends with the result
that a part passed, then for the files r that `readFirst` returned and the common beginning C: the
one stage's result is not a pass with a note on work, and its record does not say that some round
meets the target only with its work. Whether the note and the record are right is not stated. The
result is written with `stageOut`: the program's `Common.oneTimeOut` differs from it in the field
`oneTimeLine` alone, which neither function reads. -/
theorem partCall_option {o : Options} {f : Files} {part s : StageName}
    {run : Common → Read → Except Refused Found} {c : Closing}
    (h : partCall o f part run = .partPassed s c) (ho : o.noProofOfWork = true) :
    ∃ r C, readFirst o f false = .ok r ∧ commonOfCall r = .ok C ∧
      passedWithWork [stageOut part C.idHex (run C r)] = false ∧
      recordNeedsWork [stageOut part C.idHex (run C r)] = false := by
  obtain ⟨r, C, acct, work, h1, h2, _⟩ := partCall_passed h
  refine ⟨r, C, h1, h2, ?_⟩
  unfold partCall at h
  split at h
  · cases h
  · rw [h1] at h
    dsimp only at h
    rw [h2] at h
    dsimp only at h
    have hp : (cpStagesRun [C.oneTimeOut part (run C r)] (some part) (askedBelowBar o.bits)
        o.bits r.id none).passing = true := by
      rw [h]
      rfl
    have hq := cpStagesRun_option hp ((readFirst_option h1).1.trans ho)
    exact hq

/-- `partCall_option` for the call on a key file alone. -/
theorem keyCall_option {o : Options} {f : Files} {s : StageName} {c : Closing}
    (h : keyCall o f = .partPassed s c) (ho : o.noProofOfWork = true) :
    ∃ r C, readFirst o f false = .ok r ∧ commonOfCall r = .ok C ∧
      passedWithWork [stageOut .key C.idHex (keyStage C o.bits r.key)] = false ∧
      recordNeedsWork [stageOut .key C.idHex (keyStage C o.bits r.key)] = false :=
  partCall_option h ho

/-- `partCall_option` for the call on an entry file alone. The result of the stage leaf is that on
`f.entry.getD .empty`, as `leafCall` writes it: the entry's bytes. A remark on the code, no part of
the statement: if f has no entry, `leafCall` ends before it runs the stage. -/
theorem leafCall_option {o : Options} {f : Files} {s : StageName} {c : Closing}
    (h : leafCall o f = .partPassed s c) (ho : o.noProofOfWork = true) :
    ∃ r C, readFirst o f false = .ok r ∧ commonOfCall r = .ok C ∧
      passedWithWork
        [stageOut .leaf C.idHex (leafStage C o.bits (f.entry.getD .empty))] = false ∧
      recordNeedsWork
        [stageOut .leaf C.idHex (leafStage C o.bits (f.entry.getD .empty))] = false := by
  unfold leafCall at h
  split at h
  · split at h <;> cases h
  · exact partCall_option h ho

end Verify

end OnBytes.Model

#print axioms OnBytes.Model.Stages.cpStagesRun_option
#print axioms OnBytes.Model.Verify.readFirst_option
#print axioms OnBytes.Model.Verify.wholeCall_option
#print axioms OnBytes.Model.Verify.partCall_option
#print axioms OnBytes.Model.Verify.wholeCall_within
#print axioms OnBytes.Model.Verify.keyCall_option
#print axioms OnBytes.Model.Verify.leafCall_option
