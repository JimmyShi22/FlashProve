-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/PlanWritten/Mixed.lean: nine tests with code on what the planner configures, each on
a condition that reaches across the three files, or on the form of a plan. Where the planner makes
all parts in one call these conditions hold by the making, and no test of the library asks them.
Where the parts stand as written data, from several hands, they are to be asked.

All that is here are tools: definitions with code, and what a yes of each says. They name no file
and no value.

Definitions.
  `oneTableB Z`: the six words of the stored table's shape are the same in the entry file's link
    (`Z.link.shape.table`) and in the test on the table of the key file
    (`Z.key.once.shape.fold.index`) and of the proof file (`Z.proof.batch.shape.fold.index`).
  `oneSizedTableB Z`: the table as it is sized, with its pair of distances, is the same in the three
    files' sizes (`Z.link.table`, `Z.key.once.table`, `Z.proof.batch.table`).
  `oneRowsB Z`: the matrix has the same number of rows in the shape of the test on the table of the
    key file and of the proof file, and in the sizes of the key file's proof of the ranges.
  `oneKLoB Z`: a row of the table holds the same number of the matrix's columns in these two shapes.
  `slotsB Z`: the lines' number of slots is the number of requests of a batch in the proof file's
    sizes.
  `tauB Z`: the combinations of the smallness test at the proof file's setting, in a request's scope
    (`rngCombinations`, OnBytes/Params/Planner.lean), are 128.
  `oneSetB W`: all seven plans have the setting of the sizes, and so have the key file's and the
    proof file's sizes.
  `workB P`, `workTableB W`: every round's bits of work, which stand in its entry, are those of the
    plan's setting for the round's `why` and `scope`; at all seven plans.
  `recordEntry T`: the entry under the name "RECORD" as the format's page on key files states it for
    a table of the shape T: s (c + 1) drawn elements, of which s are not 0, where s is the number of
    stored answers of a row and c the number of coordinates of the record's sample; all other
    numbers are 0. It has the text of `EntryShape.ok` (OnBytes/Params/EntryLayout.lean).
  `formB T r P`: the form of one plan. The entries under the name "RECORD" are just `recordEntry T`
    where r is true and the table has stored answers, and none else; it is then the first entry; and
    every entry under the name "SEAL" has no work.
  `formsB W`: `formB` at the seven plans: with r true at the key file's first plan and at the entry
    file's plan, false at the five others. It says no unless the key file and the proof file have
    three plans each.
Statements: `oneTableB_iff`, `oneSizedTableB_iff`, `oneRowsB_iff`, `oneKLoB_iff`, `slotsB_iff`,
`tauB_iff`, `oneSetB_iff`, `workTableB_iff`, `formB_iff`: what a yes says, as a proposition.

What of OnBytes/Model/ is used: nothing.

Limits. No theorem says what these conditions are good for. That a description asks them is said
nowhere. `oneSetB` compares settings as written words. Of a setting's sixteen fields the tests on a
written plan read twelve: the field's size and degree and the target (`Desc.chainAll`), the four
that `Planned.plan` spells, and, through `workB`, the five tables of work. The four others
(`printed`, `rowsFactor`, `uniqueSource`, `instances`) are read in no plan's setting (`tauB` reads
`instances` in the setting of the proof file's sizes): that the errors of the seven plans were
computed under one reading of the closeness bound and one cost of a row is not reached by any
comparison of settings: it hangs on whence the errors are. `tauB` asks one number at one setting and
scope: not that a sub-proof's own number of combinations is that number. Of the conditions on a
plan's form that the format's page lists, two more are not here: that the seventh of a plan's eight
words is 1 holds of every `Planned.plan` by its definition, and that an entry's first word is 1 is
not asked. Nothing on soundness.
-/
import Johnson.G.MadeFree
import OnBytes.Iop.Foldeq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten.Mixed
open OnBytes OnBytes.Params Johnson.G.MadeFree

/-- The three files hold one shape of the stored table. -/
def oneTableB (Z : Sized) : Bool :=
  decide (Z.link.shape.table = Z.key.once.shape.fold.index) &&
    decide (Z.link.shape.table = Z.proof.batch.shape.fold.index)

theorem oneTableB_iff (Z : Sized) : oneTableB Z = true ↔
    Z.link.shape.table = Z.key.once.shape.fold.index ∧
      Z.link.shape.table = Z.proof.batch.shape.fold.index := by
  simp only [oneTableB, Bool.and_eq_true, decide_eq_true_eq]

/-- The three files' sized tables are one: code, rows, record, answers and the pair of distances. -/
def oneSizedTableB (Z : Sized) : Bool :=
  decide (Z.link.table = Z.key.once.table) && decide (Z.link.table = Z.proof.batch.table)

theorem oneSizedTableB_iff (Z : Sized) : oneSizedTableB Z = true ↔
    Z.link.table = Z.key.once.table ∧ Z.link.table = Z.proof.batch.table := by
  simp only [oneSizedTableB, Bool.and_eq_true, decide_eq_true_eq]

/-- The key file's and the proof file's matrix have one number of rows. -/
def oneRowsB (Z : Sized) : Bool :=
  decide (Z.key.once.shape.matrixRows = Z.proof.batch.shape.matrixRows) &&
    decide (Z.key.ranges.matrix.rows = Z.proof.batch.shape.matrixRows)

theorem oneRowsB_iff (Z : Sized) : oneRowsB Z = true ↔
    Z.key.once.shape.matrixRows = Z.proof.batch.shape.matrixRows ∧
      Z.key.ranges.matrix.rows = Z.proof.batch.shape.matrixRows := by
  simp only [oneRowsB, Bool.and_eq_true, decide_eq_true_eq]

/-- A row of the table holds the same number of the matrix's columns in the key file's and in the
proof file's shape of the test on the table. -/
def oneKLoB (Z : Sized) : Bool := decide (Z.key.once.shape.kLo = Z.proof.batch.shape.kLo)

theorem oneKLoB_iff (Z : Sized) : oneKLoB Z = true ↔
    Z.key.once.shape.kLo = Z.proof.batch.shape.kLo := by
  simp only [oneKLoB, decide_eq_true_eq]

/-- The lines' number of slots is the number of requests of a batch in the proof file's sizes. -/
def slotsB (Z : Sized) : Bool := decide (Z.lines.slots = Z.proof.batch.lines.requests)

theorem slotsB_iff (Z : Sized) : slotsB Z = true ↔
    Z.lines.slots = Z.proof.batch.lines.requests := by
  simp only [slotsB, decide_eq_true_eq]

/-- The combinations of the smallness test at the proof file's setting are 128. -/
def tauB (Z : Sized) : Bool := decide (rngCombinations Z.proof.set .request = 128)

theorem tauB_iff (Z : Sized) : tauB Z = true ↔ rngCombinations Z.proof.set .request = 128 := by
  simp only [tauB, decide_eq_true_eq]

/-- All seven plans, and the key file's and the proof file's sizes, have the setting of the
sizes. -/
def oneSetB (W : Free) : Bool :=
  ((W.key ++ W.entry :: W.proof).all fun P => decide (P.set = W.sized.set)) &&
    decide (W.sized.key.set = W.sized.set) && decide (W.sized.proof.set = W.sized.set)

theorem oneSetB_iff (W : Free) : oneSetB W = true ↔
    (∀ P ∈ W.key ++ W.entry :: W.proof, P.set = W.sized.set) ∧ W.sized.key.set = W.sized.set ∧
      W.sized.proof.set = W.sized.set := by
  simp only [oneSetB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc]

/-- Every round's bits of work, which stand in its entry, are those of the plan's setting for the
round's kind of error and scope. -/
def workB (P : Planned) : Bool :=
  P.rounds.all fun r => r.entry.work == P.set.workOf r.why r.scope

/-- So at all seven plans. -/
def workTableB (W : Free) : Bool := (W.key ++ W.entry :: W.proof).all workB

theorem workTableB_iff (W : Free) : workTableB W = true ↔
    ∀ P ∈ W.key ++ W.entry :: W.proof, ∀ r ∈ P.rounds,
      r.entry.work = P.set.workOf r.why r.scope := by
  simp only [workTableB, workB, List.all_eq_true, beq_iff_eq]

/-- The entry under the name "RECORD" for a table of the shape T. -/
def recordEntry (T : IndexShape) : Fmt.Entry :=
  { name := Fmt.recordName, drawE := T.answers * (T.cubeBits + 1), drawNZ := T.answers }

/-- The form of one plan. r: whether the plan is one of those that hold the entry "RECORD". -/
def formB (T : IndexShape) (r : Bool) (P : Planned) : Bool :=
  decide (P.plan.entries.filter (fun e => e.name == Fmt.recordName) =
      if r && T.answers != 0 then [recordEntry T] else []) &&
    (!(r && T.answers != 0) || P.plan.entries.head?.map (·.name) == some Fmt.recordName) &&
    P.plan.entries.all fun e => e.name != "SEAL" || e.work == 0

theorem formB_iff (T : IndexShape) (r : Bool) (P : Planned) : formB T r P = true ↔
    (P.plan.entries.filter (fun e => e.name == Fmt.recordName) =
      if r && T.answers != 0 then [recordEntry T] else []) ∧
    (!(r && T.answers != 0) ||
      P.plan.entries.head?.map (·.name) == some Fmt.recordName) = true ∧
    (P.plan.entries.all fun e => e.name != "SEAL" || e.work == 0) = true := by
  simp only [formB, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- The form of the seven plans. -/
def formsB (W : Free) : Bool :=
  match W.key, W.proof with
  | [k₁, k₂, k₃], [p₁, p₂, p₃] =>
    formB W.sized.link.shape.table true k₁ && formB W.sized.link.shape.table false k₂ &&
      formB W.sized.link.shape.table false k₃ && formB W.sized.link.shape.table true W.entry &&
      formB W.sized.link.shape.table false p₁ && formB W.sized.link.shape.table false p₂ &&
      formB W.sized.link.shape.table false p₃
  | _, _ => false

end VerifiableInference.PlanWritten.Mixed

#print axioms VerifiableInference.PlanWritten.Mixed.oneTableB_iff
#print axioms VerifiableInference.PlanWritten.Mixed.oneSizedTableB_iff
#print axioms VerifiableInference.PlanWritten.Mixed.oneRowsB_iff
#print axioms VerifiableInference.PlanWritten.Mixed.oneKLoB_iff
#print axioms VerifiableInference.PlanWritten.Mixed.slotsB_iff
#print axioms VerifiableInference.PlanWritten.Mixed.tauB_iff
#print axioms VerifiableInference.PlanWritten.Mixed.oneSetB_iff
#print axioms VerifiableInference.PlanWritten.Mixed.workTableB_iff
#print axioms VerifiableInference.PlanWritten.Mixed.formB_iff
