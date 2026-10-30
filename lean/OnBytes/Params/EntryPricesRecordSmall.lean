-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryPricesRecordSmall.lean: at the small lines of the setting "record with work":
the conditions of the laws on prices at the groups of an entry's test, and that every round of an
entry's plan has the name and the error of its formula.

The like, in one file, of most of OnBytes/Params/GroupPricesRecord.lean,
OnBytes/Params/MorePricesRecord.lean, OnBytes/Params/LinkPricesRecord.lean and
OnBytes/Params/EntryPricesRecord.lean at the small example (`smallRecordSet`, `smallRecordTable`,
`smallRecordG1` to `smallRecordG3`: OnBytes/Params/EntryStagesRecordSmall.lean), by evaluations in
Lean's kernel. The three groups meet the conditions `JohnsonGroup`, at the radii 65304, 10490 and
10490, which are also at least the upper radius (`small_record_groups_test`,
`small_record_groups_johnson`, `small_record_groups_upper`). `smallRecordBounds` lists, for the 25
rounds of an entry's plan, each round's name and its formula; there are 25 and none is marked bad
(`smallRecordBounds_good`); the rounds of the plan that `entrySized` returns at `smallRecordLines`
have these names and the errors of these bounds, in this order (`smallRecordBounds_test`,
`small_record_plan_prices`). The price of a link's fold point covers the proof library's numbers at
`smallRecordRadius`, for both tables (`rls_facts`, `small_record_link_point_covers`). The marks of
the two lists of 51 columns and the law that no member of the list is marked bad stand in
OnBytes/Params/EntryCoveredRecord.lean.

Main definition: `smallRecordBounds`.
Main theorems: `small_record_groups_test`, `small_record_groups_johnson`,
`small_record_groups_upper`, `smallRecordBounds_good`, `smallRecordBounds_test`,
`small_record_plan_prices`, `rls_facts`, `small_record_link_point_covers`.
What is not claimed: what the heads of the four files named above do not claim, read at the small
example. The numbers 19, 20, 51, 107, 16, 97, 293, 12, 66 and 200 in `smallRecordBounds` were read
off a print of the plan's entries; the theorem checks that the errors at them are the plan's, and
`small_record_finish` (OnBytes/Params/EntryStagesRecordSmall.lean) that the entries have these
positions and rows. For proofs only; the program, that is the Lean port built from OnBytes/, does
not import this file.

-/
import OnBytes.Params.EntryPricesRecord
import OnBytes.Params.RecordRoundSmall

set_option autoImplicit false

namespace OnBytes.Params
open Bound

/-- At the three groups of the proximity test in an entry's chain, at the small lines of the setting
"record with work", the test `johnsonGroupTest` answers yes, each at its typed radius. -/
theorem small_record_groups_test :
    johnsonGroupTest smallRecordSet smallRecordG1 65304 = true ∧
      johnsonGroupTest smallRecordSet smallRecordG2 10490 = true ∧
      johnsonGroupTest smallRecordSet smallRecordG3 10490 = true := by decide +kernel

/-- So the three groups meet the conditions. -/
theorem small_record_groups_johnson :
    JohnsonGroup smallRecordSet smallRecordG1 65304 ∧
      JohnsonGroup smallRecordSet smallRecordG2 10490 ∧
      JohnsonGroup smallRecordSet smallRecordG3 10490 :=
  ⟨johnsonGroup_of_test small_record_groups_test.1,
    johnsonGroup_of_test small_record_groups_test.2.1,
    johnsonGroup_of_test small_record_groups_test.2.2⟩

/-- The typed radii are also at least the upper radius. -/
theorem small_record_groups_upper :
    upperRadiusTest smallRecordSet smallRecordG1 65304 = true ∧
      upperRadiusTest smallRecordSet smallRecordG2 10490 = true ∧
      upperRadiusTest smallRecordSet smallRecordG3 10490 = true := by decide +kernel

/-- The 25 rounds of an entry's plan at the small lines: each name with the planner's formula of
which the laws on prices speak. -/
def smallRecordBounds : List (String × Bound) :=
  [("RECORD",
      sampleError smallRecordSet (tableAnalysis smallRecordSet smallRecordTable).once.list 19 1),
    ("LINK point", fieldError smallRecordSet smallRecordTable.v +
      tableFoldError smallRecordSet smallRecordTable
        (tableAnalysis smallRecordSet smallRecordTable).once +
      tableFoldError smallRecordSet smallRecordTable
        (tableAnalysis smallRecordSet smallRecordTable).later),
    ("SEND seed", Bound.ofWord 2 *
      sampleError smallRecordSet (max (analysisOfM smallRecordSet smallRecordG1).list 1) 20 1),
    ("SEND answer", Bound.ofWord 0),
    ("LINK", if (Bound.pow (tableAnalysis smallRecordSet smallRecordTable).later.agree 51).hi.lt
        (Bound.pow (tableAnalysis smallRecordSet smallRecordTable).once.agree 51).hi
      then Bound.pow (tableAnalysis smallRecordSet smallRecordTable).once.agree 51
      else Bound.pow (tableAnalysis smallRecordSet smallRecordTable).later.agree 51),
    ("LINK phi", fieldError smallRecordSet 19),
    ("BAT", Bound.ofNat (max (analysisOfM smallRecordSet smallRecordG1).list 1) *
      powersError smallRecordSet 107)] ++
  foldBounds smallRecordSet smallRecordG1 ++
  switchBounds smallRecordSet smallRecordG1 smallRecordG2 16 97 293 ++
  foldBounds smallRecordSet smallRecordG2 ++
  switchBounds smallRecordSet smallRecordG2 smallRecordG3 12 66 200 ++
  [("BASE lambda",
      baseError smallRecordSet smallRecordG3 (analysisOfM smallRecordSet smallRecordG3)),
    ("BASE", Bound.pow (analysisOfM smallRecordSet smallRecordG3).mainAt.agree 66)]

/-- There are 25, and none is marked bad. -/
theorem smallRecordBounds_good :
    smallRecordBounds.length = 25 ∧ (smallRecordBounds.all fun x => !x.2.bad) = true := by
  decide +kernel

/-- The rounds of the entry's plan, as `finishHeld` returns it, have these names and the errors of
these bounds, in this order. -/
theorem smallRecordBounds_test : ((finishHeld smallRecordSet .once
    (linkPlan ⟨smallRecordLink, smallRecordTable,
      ⟨smallRecordG1, 97, smallRecordStages⟩⟩)).toOption.any fun P =>
      decide ((P.rounds.map fun r => (r.entry.name, r.error)) =
        smallRecordBounds.map fun x => (x.1, x.2.error))) = true := by decide +kernel

/-- **At `smallRecordLines` every round of the entry's plan has the name and the error of its
formula in `smallRecordBounds`.** -/
theorem small_record_plan_prices : ∃ P, entrySized smallRecordLines =
      .ok (⟨smallRecordLink, smallRecordTable, ⟨smallRecordG1, 97, smallRecordStages⟩⟩,
        smallRecordCodes, P) ∧
    (P.rounds.map fun r => (r.entry.name, r.error)) =
      smallRecordBounds.map fun x => (x.1, x.2.error) := by
  have hp := smallRecordBounds_test
  cases hP : finishHeld smallRecordSet .once
      (linkPlan ⟨smallRecordLink, smallRecordTable, ⟨smallRecordG1, 97, smallRecordStages⟩⟩) with
  | error e =>
    rw [hP] at hp
    cases hp
  | ok P =>
    rw [hP] at hp
    simp only [Except.toOption, Option.any_some, decide_eq_true_eq] at hp
    exact ⟨P, entrySized_of small_record_table small_record_link hP, hp⟩

/-- The table's two integers are the same, a later test's count is not marked bad, and the price of
a link's fold point is not marked bad. -/
theorem rls_facts : smallRecordTable.distances.mLater = smallRecordTable.distances.mOnce ∧
    (tableAnalysis smallRecordSet smallRecordTable).later.count.bad = false ∧
    (fieldError smallRecordSet smallRecordTable.v +
      tableFoldError smallRecordSet smallRecordTable
        (tableAnalysis smallRecordSet smallRecordTable).once +
      tableFoldError smallRecordSet smallRecordTable
        (tableAnalysis smallRecordSet smallRecordTable).later).bad = false := by
  decide +kernel

/-- **At the small lines the price of a link's fold point covers the library's numbers at the typed
radius, for both tables.** -/
theorem small_record_link_point_covers :
    ((smallRecordTable.v : ℝ) +
        ((smallRecordTable.v : ℝ) * Cb.bchksBound (2 ^ 23) 589822 smallRecordRadius +
          (Cb.listMax (2 ^ 23) 7798786 smallRecordRadius : ℝ) * (smallRecordTable.v : ℝ)) +
        ((smallRecordTable.v : ℝ) * Cb.bchksBound (2 ^ 23) 589822 smallRecordRadius +
          (Cb.listMax (2 ^ 23) 7798786 smallRecordRadius : ℝ) * (smallRecordTable.v : ℝ))) /
        (smallRecordSet.cardE : ℝ) ≤
      (((fieldError smallRecordSet smallRecordTable.v +
        tableFoldError smallRecordSet smallRecordTable
          (tableAnalysis smallRecordSet smallRecordTable).once +
        tableFoldError smallRecordSet smallRecordTable
          (tableAnalysis smallRecordSet smallRecordTable).later).error.val : ℚ) : ℝ) := by
  obtain ⟨m0, g0, g⟩ := rls_facts
  have hk : 0 < (wordOf smallRecordTable.code).k := by
    rw [rs_word]
    decide
  have h0 : (smallRecordRadius : ℝ) ≤
      (1 - (wordOf smallRecordTable.code).agreeAt smallRecordTable.distances.mLater true) *
        ((wordOf smallRecordTable.code).n : ℝ) := by
    rw [m0]
    exact small_record_radius_le
  have h := link_point_covers_johnson (s := smallRecordSet) (T := smallRecordTable)
    (e1 := smallRecordRadius) (e0 := smallRecordRadius) (by decide) rs_set.1 rs_once.1 g0 hk
    small_record_radius_le h0 g
  rw [rs_word] at h
  exact h

end OnBytes.Params

#print axioms OnBytes.Params.small_record_groups_test
#print axioms OnBytes.Params.small_record_groups_johnson
#print axioms OnBytes.Params.small_record_groups_upper
#print axioms OnBytes.Params.smallRecordBounds_good
#print axioms OnBytes.Params.smallRecordBounds_test
#print axioms OnBytes.Params.small_record_plan_prices
#print axioms OnBytes.Params.rls_facts
#print axioms OnBytes.Params.small_record_link_point_covers
