-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryPricesRecord.lean: at the full-size lines of the setting "record with work"
every round of an entry's plan has the name and the error of a formula of which the laws on prices
speak.

The laws of OnBytes/Params/RecordPrice.lean, OnBytes/Params/GroupPrices.lean,
OnBytes/Params/MorePrices.lean and OnBytes/Params/LinkPrices.lean speak of the planner's formulas:
`sampleError`, `foldRoundError`, `baseError`, `tableFoldError`, powers of an agreement, a list size
times `fieldError` or `powersError`. This file ties the formulas to a plan. `recordBounds` lists,
for the 42 rounds of an entry's plan, each round's name and its formula at `recordSet`,
`recordTable` and the five groups `recordG1` to `recordG5` (OnBytes/Params/EntryStagesRecord.lean):
the record's entry; the link's five rounds; the batching; for each of four stages the round before
the fold, the fold's rounds and the two rounds of the code switch (`foldBounds`, `switchBounds`);
and the last step's two rounds. By evaluations in Lean's kernel: there are 42 and none is marked bad
(`recordBounds_good`, `recordBounds_good_at`); and the rounds of the plan that `entrySized` returns
at `recordLines` have these names and the errors of these bounds, in this order
(`recordBounds_test`, `record_plan_prices`).

Main definitions: `foldBounds`, `switchBounds`, `recordBounds`.
Main theorems: `recordBounds_good`, `recordBounds_good_at`, `recordBounds_test`,
`record_plan_prices`.
What is not claimed: what the heads of the four files of laws do not claim. No law on prices is
drawn here at a round (OnBytes/Params/EntryCoveredRecord.lean does that): the conditions of most are
evaluated in OnBytes/Params/RecordRound.lean, OnBytes/Params/GroupPricesRecord.lean,
OnBytes/Params/MorePricesRecord.lean and OnBytes/Params/LinkPricesRecord.lean. A round's other
fields (its work, its draws, its scope). The error here is a round's own; the planner adds the
distance from uniform of the round's draws before it compares (`wholeError`), and counts the round's
work. The numbers 29, 62, 129, 23, 97, 293 and their like in `recordBounds` were read off a print of
the plan's rounds; the theorem checks that the errors at them are the plan's, and `record_finish`
(OnBytes/Params/EntryStagesRecord.lean) that the entries have these positions and rows. A key's and
a proof's plans; the small files. For proofs only; the program, that is the Lean port built from
OnBytes/, does not import this file.

-/
import OnBytes.Params.LinkPricesRecord
import OnBytes.Params.MorePricesRecord

set_option autoImplicit false

namespace OnBytes.Params
open Bound

/-- The bounds of the round before a fold's rounds and of the rounds j = 1 .. k, under their
names. -/
def foldBounds (s : Setting) (g : GroupSize) : List (String × Bound) :=
  ("FOLD epsilon", Bound.ofNat (analysisOfM s g).list * fieldError s 1) ::
    (List.range' 1 g.k).map fun j => ("FOLD round", foldRoundError s g (analysisOfM s g) j)

/-- The bounds of the two rounds of a code switch from the group g to the group g', under their
names. -/
def switchBounds (s : Setting) (g g' : GroupSize) (cube t rows : ℕ) : List (String × Bound) :=
  [("SEND seed", Bound.ofWord 0 + sampleError s (max (analysisOfM s g').list 1) cube s.samples),
    ("CS", Bound.pow (analysisOfM s g).mainAt.agree t +
      Bound.ofNat (analysisOfM s g').list * powersError s rows)]

/-- The 42 rounds of an entry's plan at the full-size lines of the setting "record with work": each
name with the planner's formula of which the laws on prices speak. -/
def recordBounds : List (String × Bound) :=
  [("RECORD", sampleError recordSet (tableAnalysis recordSet recordTable).once.list 29 1),
    ("LINK point", fieldError recordSet recordTable.v +
      tableFoldError recordSet recordTable (tableAnalysis recordSet recordTable).once +
      tableFoldError recordSet recordTable (tableAnalysis recordSet recordTable).later),
    ("SEND seed", Bound.ofWord 2 *
      sampleError recordSet (max (analysisOfM recordSet recordG1).list 1) 29 1),
    ("SEND answer", Bound.ofWord 0),
    ("LINK", if (Bound.pow (tableAnalysis recordSet recordTable).later.agree 62).hi.lt
        (Bound.pow (tableAnalysis recordSet recordTable).once.agree 62).hi
      then Bound.pow (tableAnalysis recordSet recordTable).once.agree 62
      else Bound.pow (tableAnalysis recordSet recordTable).later.agree 62),
    ("LINK phi", fieldError recordSet 29),
    ("BAT", Bound.ofNat (max (analysisOfM recordSet recordG1).list 1) *
      powersError recordSet 129)] ++
  foldBounds recordSet recordG1 ++ switchBounds recordSet recordG1 recordG2 23 97 293 ++
  foldBounds recordSet recordG2 ++ switchBounds recordSet recordG2 recordG3 18 49 149 ++
  foldBounds recordSet recordG3 ++ switchBounds recordSet recordG3 recordG4 14 49 149 ++
  foldBounds recordSet recordG4 ++ switchBounds recordSet recordG4 recordG5 10 50 152 ++
  [("BASE lambda", baseError recordSet recordG5 (analysisOfM recordSet recordG5)),
    ("BASE", Bound.pow (analysisOfM recordSet recordG5).mainAt.agree 40)]

/-- There are 42, and none is marked bad. -/
theorem recordBounds_good :
    recordBounds.length = 42 ∧ (recordBounds.all fun x => !x.2.bad) = true := by decide +kernel

/-- No member of `recordBounds` is marked bad. -/
theorem recordBounds_good_at {x : String × Bound} (h : x ∈ recordBounds) : x.2.bad = false := by
  simpa using List.all_eq_true.mp recordBounds_good.2 x h

/-- The rounds of the entry's plan, as `finishHeld` returns it, have these names and the errors of
these bounds, in this order. -/
theorem recordBounds_test : ((finishHeld recordSet .once
    (linkPlan ⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩)).toOption.any fun P =>
      decide ((P.rounds.map fun r => (r.entry.name, r.error)) =
        recordBounds.map fun x => (x.1, x.2.error))) = true := by decide +kernel

/-- **At `recordLines` every round of the entry's plan has the name and the error of its formula in
`recordBounds`.** -/
theorem record_plan_prices : ∃ P, entrySized recordLines =
      .ok (⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩, recordCodes, P) ∧
    (P.rounds.map fun r => (r.entry.name, r.error)) =
      recordBounds.map fun x => (x.1, x.2.error) := by
  have hp := recordBounds_test
  cases hP : finishHeld recordSet .once
      (linkPlan ⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩) with
  | error e =>
    rw [hP] at hp
    cases hp
  | ok P =>
    rw [hP] at hp
    simp only [Except.toOption, Option.any_some, decide_eq_true_eq] at hp
    exact ⟨P, entrySized_of record_table record_link hP, hp⟩

end OnBytes.Params

#print axioms OnBytes.Params.recordBounds_good
#print axioms OnBytes.Params.recordBounds_good_at
#print axioms OnBytes.Params.recordBounds_test
#print axioms OnBytes.Params.record_plan_prices
