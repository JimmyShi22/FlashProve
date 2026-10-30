-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyLawsRecord.lean: what the program does at the end of a stage: the flag by
which a stage says that the table has a record; the condition record-one-answer; and where the
stages key and leaf use these. Also the number that a call's closing holds for the committer's
files.

This file is on three places of the program at the end of a stage. `Common.oneTimeOut` sets a
flag in the result of the stages key and leaf, and `Stages.closingOf` (OnBytes/Model/Stages.lean)
gathers it for two printed lines. `Public.recordOneAnswer` (the condition record-one-answer, which
all three stages test) decides whether a call can say yes. These laws state what each does, and
where the stages key and leaf use the last: a change of that stops this file from compiling. A
change of what `Common.acct` does with its arguments asked or object need not. The file is also on
a number: how many closeness rounds of a committer's file rest on another source than the lemma
within a third of a code's distance (`Stages.Acct.closeOther`). The same two printed lines show it.

Two things are called record here: the record of a table (GLOSSARY.md: record), and the record
of an accounting (`Stages.Acct`), which a stage hands on.

Main definition: `Stages.CallEnd.closing`, for the theorems alone. Main theorems.
- `acct_record`, `record_closeOther`: the record in what `Common.acct` returns is the record of the
  accounting of the file's plans, whose field `closeOther` is its count closeJohnson.
- `recordOneAnswer_iff`: the condition record-one-answer holds if and only if the line answers is 1.
- `oneTimeForm_nil`: the stages key and leaf list no condition as missed if and only if their three
  conditions hold, record-one-answer among them.
- `keyStage_end`, `leafStage_end`: if such a stage refuses nothing, it has asked `Common.acct` for a
  committer's file; its end is `lastLine` of that list; and it hands on that value's record and note
  on work.
- `oneTimeOut_line`, `oneTimeOut_else`: the stage's flag is set if and only if the stage's value
  holds findings (is `.ok`); but for that flag the value is `stageOut`'s.
- `stageOut_found`, `stageOut_line`: what `stageOut` makes of findings holds their end, record and
  note on work; its flag is not set.
- `closingOf_tableRecord`: the closing's flag is set if and only if some stage's is.
- `closingOf_oneTimeAssumed`: the number that the closing holds for the committer's files is the sum
  of `closeOther` over the records of all stages but the last.
- `asRead_acct`, `any_asRead`: a stage's result as the call reads it holds the stage's record if it
  is accepted, and keeps the stage's flag.
- `cpStagesRun_closing`: in the closing that a call's result carries, whatever the verdict, the flag
  is set if and only if some stage's is.
- `cpStagesRun_closing_sum`, `cpStagesRun_closing_acct`: in that closing the number for the
  committer's files is the sum of `closeOther` over the records, as the call reads them, of all
  stages but the last; and the call has accepted every stage's record (`filter_kept`: such a record
  is kept).
- `cpStagesRun_closing_no`, `stageOut_ok`: if a call's result carries a closing, no stage has
  refused; a stage's value whose result has not refused holds findings.
- `wholeCall_record`: if the tests before the entry is read returned a number, then in the closing
  that a whole call's result carries, whatever the verdict, the flag is set.
  `partCall_record`: the same of a call on one file alone that
  passes. Two printed lines read that flag (OnBytes/Shell/Lines.lean), in a whole call alone: a call
  on one file prints neither; what they print under it is tested, and not stated here.
- `wholeCall_oneTimeAssumed`: if the tests before the entry is read returned a number, then,
  whatever the verdict, the number for the committer's files in a whole call's closing is the sum of
  two counts: closeJohnson of the accounting of the key's plans, and the same of the entry's plan.

What is not claimed. Nothing on soundness, and nothing on what a record is worth: a committer's file
rests on the assumed theorem (ePrint 2025/2055, Theorem 4.6). Nothing says that some files make a
call pass or end as not a verification. That a stage whose list is not empty does not pass, and that
a call passes only if its stages do, is not stated here (the first: read `Stages.lastLine`; the
second: `cpStagesRun_passed`, OnBytes/Model/VerifyLawsWhole.lean). Which names the list of the
stages key and leaf holds, and in which order, is not stated. Where the stage request uses
record-one-answer is not stated here. Of the flag in the closing of a call on one file alone that
ends as not a verification, which prints neither line, only `cpStagesRun_closing` speaks: that it is
set is not stated. Where the tests before the entry is read end a whole call, the result is theirs:
that it carries no closing is not stated (read `readCall`, OnBytes/Model/VerifyHeads.lean). That a
whole call never ends with the result that a part passed, and never as not a verification without
what it is about, is not stated (read `cpStagesRun`). Whether an accounting counts the closeness
terms rightly is not stated (`Accounting.take`, OnBytes/Model/VerifyAccount.lean; `account` and
`merged` are taken as defined). The common beginning C and its plans are taken as `commonOfCall`
returns them: that `Key.check` and `Entry.check` read the files under these plans is not stated. Of
the number in the closing of a call on one file alone only `cpStagesRun_closing_sum` speaks: that it
is 0 is tested (OnBytes/Model/TestStages.lean), and not stated. What is and is not proved of any
call: OnBytes/LIMITS.md. Nothing on the printed lines themselves (OnBytes/Shell/Lines.lean). That
the C++ verifier does the same is not proved. For proofs only; the program does not import this
file.


-/
import OnBytes.Model.VerifyLawsWhole

set_option autoImplicit false

namespace OnBytes.Model

namespace Verify

open OnBytes.Model.Stages
open OnBytes.Params (exc_bind)

/-- If `Common.acct` returned a, for a committer's file or another, then the record in a is the
record of the accounting of the file's plans, joined under the setting under which C's plans were
made. -/
theorem acct_record {C : Common} {plans : List Params.Planned} {asked : Nat} {object : String}
    {a : FileAcct} (h : C.acct plans asked object = .ok a) :
    a.acct = (account (merged C.chains.made.sized.set plans)).record := by
  unfold Common.acct acctOfH at h
  dsimp only at h
  split at h
  · cases h
  · cases h
    rfl

/-- In the record of an accounting, the field `closeOther` is the accounting's count of the
closeness terms that rest on the assumed theorem. -/
theorem record_closeOther (a : Accounting) :
    a.record.closeOther = a.closeJohnson := rfl

/-- The condition record-one-answer holds if and only if the number that X holds for the line
answers is 1. -/
theorem recordOneAnswer_iff (X : Public) :
    X.recordOneAnswer = true ↔ X.P.frame.answers = 1 := by
  simp [Public.recordOneAnswer]

/-- The stages key and leaf list no condition as missed if and only if their three conditions hold.
They are those in the fields `readingAsPrinted`, `twoCodes` and `recordOneAnswer` of
`servedOf`. -/
theorem oneTimeForm_nil {C : Common} :
    C.oneTimeForm = [] ↔
      C.X.P.frame.reading = 1 ∧ C.chains.twoCodes = true ∧ C.X.recordOneAnswer = true := by
  simp [Common.oneTimeForm]

/-- If the stage key refuses nothing, it has asked `Common.acct` for the key's plans as a
committer's file; its end is what `lastLine` returns on the list `Common.oneTimeForm`; and the
record and the note on work that it hands on are those of what `Common.acct` returned. -/
theorem keyStage_end {C : Common} {asked : Nat} {key : ByteArray} {y : Found}
    (h : keyStage C asked key = .ok y) :
    ∃ a, C.acct C.chains.made.key asked "key" = .ok a ∧
      y = (lastLine (!C.X.p4) (askedBelowBar asked) (C.oneTimeForm)
        lidbSealed 0, some a.acct, a.work) := by
  unfold keyStage at h
  obtain ⟨a, ha, h⟩ := exc_bind h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := exc_bind h
    cases h
    exact ⟨a, named_ok ha, rfl⟩

/-- If the stage leaf refuses nothing, it has asked `Common.acct` for the entry's plan as a
committer's file; its end is what `lastLine` returns on the list `Common.oneTimeForm`; and the
record and the note on work that it hands on are those of what `Common.acct` returned. -/
theorem leafStage_end {C : Common} {asked : Nat} {entry : ByteArray} {y : Found}
    (h : leafStage C asked entry = .ok y) :
    ∃ a, C.acct [C.chains.made.entry] asked "leaf" = .ok a ∧
      y = (lastLine (!C.X.p4) (askedBelowBar asked) (C.oneTimeForm)
        lidbSealed 0, some a.acct, a.work) := by
  unfold leafStage at h
  obtain ⟨a, ha, h⟩ := exc_bind h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := exc_bind h
    cases h
    exact ⟨a, named_ok ha, rfl⟩

/-- The stage's flag is set (the stage key or leaf says that the table has a record) if and only if
x holds findings (is `.ok`). -/
theorem oneTimeOut_line (C : Common) (name : StageName) (x : Except Refused Found) :
    (C.oneTimeOut name x).oneTimeLine = x.toOption.isSome := rfl

/-- But for the stage's flag, the result of the stage key or leaf is `stageOut`'s, whose flag is not
set. -/
theorem oneTimeOut_else (C : Common) (name : StageName) (x : Except Refused Found) :
    { C.oneTimeOut name x with oneTimeLine := false } = stageOut name C.idHex x := by
  cases x <;> rfl

/-- The closing's flag is set (the closing says that the table has a record) if and only if some
stage's flag is. -/
theorem closingOf_tableRecord (stages : List StageOut) (id : CpId) (idHex : String) :
    (closingOf stages id idHex).tableRecord = stages.any (·.oneTimeLine) := rfl

/-- The number that the closing holds for the committer's files is the sum, over all stages but the
last, of the field `closeOther` of the records that they handed on. -/
theorem closingOf_oneTimeAssumed (stages : List StageOut) (id : CpId) (idHex : String) :
    (closingOf stages id idHex).oneTimeAssumed =
      (stages.dropLast.filterMap (·.acct)).foldl (fun s a => s + a.closeOther) 0 := rfl

/-- What `stageOut` makes of findings: the end, the record and the note on work are the findings'
own. -/
theorem stageOut_found (name : StageName) (idHex : String) (e : StageEnd) (acct : Option Acct)
    (work : Option WorkNote) : stageOut name idHex (.ok (e, acct, work)) =
      { name := name, ending := e, idHex := idHex, acct := acct, work := work } := rfl

/-- The stage's flag is not set in what `stageOut` returns. -/
theorem stageOut_line (name : StageName) (idHex : String) (x : Except Refused Found) :
    (stageOut name idHex x).oneTimeLine = false := by
  cases x <;> rfl

end Verify

namespace Stages

/-- The closing that a call's result carries: a yes, a result within limits, that a part passed, and
an end as not a verification carry one. For the theorems below; the program does not use it. -/
def CallEnd.closing : CallEnd → Option Closing
  | .yes _ c => some c
  | .withinLimits _ c => some c
  | .partPassed _ c => some c
  | .notVer _ _ c => some c
  | _ => none

/-- A stage's result as the call reads it keeps the stage's flag. -/
theorem any_asRead (stages : List StageOut) :
    (stages.map StageOut.asRead).any (·.oneTimeLine) = stages.any (·.oneTimeLine) := by
  rw [List.any_map]
  rfl

/-- If the result of a call carries the closing c, then the closing's flag is set in c if and only
if some stage's flag is. -/
theorem cpStagesRun_closing {stages : List StageOut} {part : Option StageName} {belowBar : Bool}
    {asked : Nat} {id : CpId} {about : Option (Array UInt32 × PolicyLines)} {c : Closing}
    (h : (cpStagesRun stages part belowBar asked id about).closing = some c) :
    c.tableRecord = stages.any (·.oneTimeLine) := by
  unfold cpStagesRun at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (obtain rfl := Option.some.inj h
       exact any_asRead stages)

/-- A stage's result as the call reads it holds the stage's record if the record is accepted, and
none otherwise. -/
theorem asRead_acct (x : StageOut) : x.asRead.acct = x.acct.filter Acct.taken := rfl

/-- If the result of a call carries the closing c, then the number that c holds for the committer's
files is the sum, over all stages but the last, of the field `closeOther` of the records as the call
reads them. -/
theorem cpStagesRun_closing_sum {stages : List StageOut} {part : Option StageName} {belowBar : Bool}
    {asked : Nat} {id : CpId} {about : Option (Array UInt32 × PolicyLines)} {c : Closing}
    (h : (cpStagesRun stages part belowBar asked id about).closing = some c) :
    c.oneTimeAssumed = ((stages.map StageOut.asRead).dropLast.filterMap (·.acct)).foldl
      (fun s a => s + a.closeOther) 0 := by
  unfold cpStagesRun at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (obtain rfl := Option.some.inj h
       rfl)

/-- If the result of a call carries a closing, every stage has handed on a record, and the call has
accepted it. -/
theorem cpStagesRun_closing_acct {stages : List StageOut} {part : Option StageName}
    {belowBar : Bool} {asked : Nat} {id : CpId} {about : Option (Array UInt32 × PolicyLines)}
    {c : Closing} (h : (cpStagesRun stages part belowBar asked id about).closing = some c) :
    ∀ x ∈ stages, x.asRead.acct.isSome = true := by
  unfold cpStagesRun at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | skip
  all_goals
    intro x hx
    cases hq : x.asRead.acct with
    | some _ => rfl
    | none =>
      have hany : ((stages.map StageOut.asRead).any fun x => x.acct.isNone) = true :=
        List.any_eq_true.2 ⟨x.asRead, List.mem_map_of_mem hx, by rw [hq]; rfl⟩
      contradiction

/-- If the result of a call carries a closing, no stage has refused. -/
theorem cpStagesRun_closing_no {stages : List StageOut} {part : Option StageName} {belowBar : Bool}
    {asked : Nat} {id : CpId} {about : Option (Array UInt32 × PolicyLines)} {c : Closing}
    (h : (cpStagesRun stages part belowBar asked id about).closing = some c) :
    ∀ x ∈ stages, ∀ name, x.ending ≠ .no name := by
  unfold cpStagesRun at h
  dsimp only at h
  split at h
  · split at h <;> cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i hfault
        have hno := firstFault_no _ hfault
        intro x hx name he
        exact hno x.asRead (List.mem_map_of_mem hx) name he

end Stages

namespace Verify

open OnBytes.Model.Stages

/-- A stage's value whose result has not refused holds findings. The converse does not hold:
findings can hold the end internal-last-line (`lastLine`). -/
theorem stageOut_ok {name : StageName} {idHex : String} {x : Except Refused Found}
    (h : ∀ n, (stageOut name idHex x).ending ≠ .no n) : x.toOption.isSome = true := by
  cases x with
  | error e => exact absurd rfl (h e.name)
  | ok y => rfl

/-- If the tests before the entry is read returned a number, and the result of `wholeCall` on the
same files with the entry carries the closing c, whatever the verdict (a yes, within limits, not a
verification), then, for the files r that `readCall` returned and the common beginning C, the
closing's flag is set in c.
-/
theorem wholeCall_record {o : Options} {f : Files} {k : Nat} {entry : FileIn} {c : Closing}
    (hk : entryNumber o f = .ok k)
    (hc : (wholeCall o { f with entry := entry }).closing = some c) :
    ∃ (r : Read) (C : Common),
      readCall o f = .ok r ∧ commonOfCall r = .ok C ∧
      c.tableRecord = true := by
  unfold entryNumber at hk
  cases hr : readCall o f with
  | error e =>
    rw [hr] at hk
    cases hk
  | ok r =>
    unfold wholeCall at hc
    rw [readCall_entry, hr] at hc
    dsimp only at hc
    cases entry with
    | none => cases hc
    | some ent =>
      dsimp only at hc
      unfold stagesOf at hc
      cases hC : commonOfCall r with
      | error e =>
        rw [hC] at hc
        exact absurd rfl (cpStagesRun_closing_no hc _ (List.mem_cons_self) e.name)
      | ok C =>
        rw [hC] at hc
        have hno := cpStagesRun_closing_no hc
        have a1 : (keyStage C o.bits r.key).toOption.isSome = true :=
          stageOut_ok (name := .key) (idHex := C.idHex)
            (hno (C.oneTimeOut .key (keyStage C o.bits r.key)) (by simp))
        have e1 : (C.oneTimeOut .key (keyStage C o.bits r.key)).oneTimeLine = true := by
          rw [oneTimeOut_line, a1]
        refine ⟨r, C, rfl, hC, ?_⟩
        rw [cpStagesRun_closing hc]
        show ([C.oneTimeOut .key (keyStage C o.bits r.key),
          C.oneTimeOut .leaf (leafStage C o.bits ent),
          stageOut .request C.idHex (requestStage C o r ent)] : List StageOut).any
            (·.oneTimeLine) = _
        simp [e1]

/-- A record that is accepted is kept. -/
theorem filter_kept {a : Acct} (h : ((some a).filter Acct.taken).isSome = true) :
    (some a).filter Acct.taken = some a := by
  cases ht : Acct.taken a with
  | true => simp [Option.filter, ht]
  | false => simp [Option.filter, ht] at h

/-- If the tests before the entry is read returned a number, and the result of `wholeCall` on the
same files with the entry carries the closing c, whatever the verdict, then, for the files r that
`readCall` returned and the common beginning C, the number that c holds for the committer's files is
the sum of two counts of the accounting: closeJohnson (the closeness terms that rest on the assumed
theorem) for the key's plans, and the same for the entry's plan, each joined under the setting
under which C's plans were made. -/
theorem wholeCall_oneTimeAssumed {o : Options} {f : Files} {k : Nat} {entry : FileIn} {c : Closing}
    (hk : entryNumber o f = .ok k)
    (hc : (wholeCall o { f with entry := entry }).closing = some c) :
    ∃ (r : Read) (C : Common),
      readCall o f = .ok r ∧ commonOfCall r = .ok C ∧
      c.oneTimeAssumed =
        (account (merged C.chains.made.sized.set C.chains.made.key)).closeJohnson +
          (account (merged C.chains.made.sized.set [C.chains.made.entry])).closeJohnson := by
  unfold entryNumber at hk
  cases hr : readCall o f with
  | error e =>
    rw [hr] at hk
    cases hk
  | ok r =>
    unfold wholeCall at hc
    rw [readCall_entry, hr] at hc
    dsimp only at hc
    cases entry with
    | none => cases hc
    | some ent =>
      dsimp only at hc
      unfold stagesOf at hc
      cases hC : commonOfCall r with
      | error e =>
        rw [hC] at hc
        exact absurd rfl (cpStagesRun_closing_no hc _ (List.mem_cons_self) e.name)
      | ok C =>
        rw [hC] at hc
        have hno := cpStagesRun_closing_no hc
        have hs := cpStagesRun_closing_acct hc
        have n1 := hno (C.oneTimeOut .key (keyStage C o.bits r.key)) (by simp)
        have n2 := hno (C.oneTimeOut .leaf (leafStage C o.bits ent)) (by simp)
        have s1 := hs (C.oneTimeOut .key (keyStage C o.bits r.key)) (by simp)
        have s2 := hs (C.oneTimeOut .leaf (leafStage C o.bits ent)) (by simp)
        cases ek : keyStage C o.bits r.key with
        | error e =>
          rw [ek] at n1
          exact absurd rfl (n1 e.name)
        | ok yk =>
          cases el : leafStage C o.bits ent with
          | error e =>
            rw [el] at n2
            exact absurd rfl (n2 e.name)
          | ok yl =>
            obtain ⟨ak, hak, eyk⟩ := keyStage_end ek
            obtain ⟨al, hal, eyl⟩ := leafStage_end el
            subst eyk
            subst eyl
            have k2 : (C.oneTimeOut .key (keyStage C o.bits r.key)).asRead.acct =
                some ak.acct := by
              rw [ek] at s1 ⊢
              exact filter_kept (a := ak.acct) s1
            have l2 : (C.oneTimeOut .leaf (leafStage C o.bits ent)).asRead.acct =
                some al.acct := by
              rw [el] at s2 ⊢
              exact filter_kept (a := al.acct) s2
            refine ⟨r, C, rfl, hC, ?_⟩
            rw [cpStagesRun_closing_sum hc]
            show ((([C.oneTimeOut .key (keyStage C o.bits r.key),
              C.oneTimeOut .leaf (leafStage C o.bits ent),
              stageOut .request C.idHex (requestStage C o r ent)] : List StageOut).map
                StageOut.asRead).dropLast.filterMap (·.acct)).foldl
                  (fun s a => s + a.closeOther) 0 = _
            simp only [List.map_cons, List.map_nil, List.dropLast, List.filterMap_cons,
              List.filterMap_nil, k2, l2, List.foldl_cons, List.foldl_nil]
            rw [acct_record hak, acct_record hal, record_closeOther, record_closeOther]
            omega

/-- If a call on one file alone ends with the result that a part passed, with the closing c, then,
for the files r that `readFirst` returned and the common beginning C, the closing's flag is set in
c. -/
theorem partCall_record {o : Options} {f : Files} {part s : StageName}
    {run : Common → Read → Except Refused Found} {c : Closing}
    (h : partCall o f part run = .partPassed s c) :
    ∃ r C, readFirst o f false = .ok r ∧ commonOfCall r = .ok C ∧
      c.tableRecord = true := by
  obtain ⟨r, C, acct, work, h1, h2, h3⟩ := partCall_passed h
  refine ⟨r, C, h1, h2, ?_⟩
  unfold partCall at h
  split at h
  · cases h
  · rw [h1] at h
    dsimp only at h
    rw [h2] at h
    dsimp only at h
    have hc : (cpStagesRun [C.oneTimeOut part (run C r)] (some part) (askedBelowBar o.bits)
        o.bits r.id none).closing = some c := by
      rw [h]
      rfl
    have e1 : (C.oneTimeOut part (run C r)).oneTimeLine = true := by
      rw [oneTimeOut_line, h3.1]
      rfl
    rw [cpStagesRun_closing hc]
    simp only [List.any_cons, List.any_nil, e1, Bool.or_false]

end Verify

end OnBytes.Model

#print axioms OnBytes.Model.Verify.acct_record
#print axioms OnBytes.Model.Verify.record_closeOther
#print axioms OnBytes.Model.Verify.recordOneAnswer_iff
#print axioms OnBytes.Model.Verify.oneTimeForm_nil
#print axioms OnBytes.Model.Verify.keyStage_end
#print axioms OnBytes.Model.Verify.leafStage_end
#print axioms OnBytes.Model.Verify.oneTimeOut_line
#print axioms OnBytes.Model.Verify.oneTimeOut_else
#print axioms OnBytes.Model.Verify.stageOut_found
#print axioms OnBytes.Model.Verify.stageOut_line
#print axioms OnBytes.Model.Stages.any_asRead
#print axioms OnBytes.Model.Verify.closingOf_tableRecord
#print axioms OnBytes.Model.Verify.closingOf_oneTimeAssumed
#print axioms OnBytes.Model.Stages.cpStagesRun_closing
#print axioms OnBytes.Model.Stages.asRead_acct
#print axioms OnBytes.Model.Stages.cpStagesRun_closing_sum
#print axioms OnBytes.Model.Stages.cpStagesRun_closing_acct
#print axioms OnBytes.Model.Stages.cpStagesRun_closing_no
#print axioms OnBytes.Model.Verify.stageOut_ok
#print axioms OnBytes.Model.Verify.wholeCall_record
#print axioms OnBytes.Model.Verify.filter_kept
#print axioms OnBytes.Model.Verify.wholeCall_oneTimeAssumed
#print axioms OnBytes.Model.Verify.partCall_record
