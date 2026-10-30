-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/RecordRoundSmall.lean: at the small lines of the setting "record with work": the
price of the round of the table's record, a radius, and that the price covers the proof library's
count.

The like of the second part of OnBytes/Params/RecordRound.lean at `smallRecordSet` and
`smallRecordTable` (OnBytes/Params/EntryStagesRecordSmall.lean), by evaluations of the planner in
Lean's kernel: the table's word has the length 2 ^ 23 and k = 589822, the dimension less 1
(`rs_word`); m is read as printed (`rs_set`); the one-time test's count is not marked bad and its
list size is 114 (`rs_once`); the lower and the upper end of its distance times the length, rounded
down, are one number, `smallRecordRadius` = 6137119 (`rs_radius`); the error of the round that
`planRecord` adds is the typed `smallRecordPrice`, at the cube 19 and one answer (`rs_price`); and
the first round of the entry's plan has the name RECORD and that price (`rs_first`,
`small_record_first_round`). So the typed radius is at most 1 less the one-time test's agreement,
times the length, which lies below the radius and one (`small_record_radius_le`,
`small_record_radius_top`); it is below the library's Johnson radius and below the distance 7798786
of a row's code (`small_record_radius_inJohnson`); and the typed price covers, with any bias (1 + x)
^ b for 228 b x ≤ 1, the library's count of the record's clashes at that radius
(`small_record_covers_at`).

Main definitions: `smallRecordPrice`, `smallRecordRadius`.
Main theorems: `rs_word`, `rs_set`, `rs_once`, `rs_radius`, `rs_price`, `rs_first`,
`small_record_radius_le`, `small_record_radius_top`, `small_record_radius_inJohnson`,
`small_record_covers_at`, `small_record_first_round`.
What is not claimed: what the heads of OnBytes/Params/RecordPrice.lean and
OnBytes/Params/RecordRound.lean do not claim, read at the small example. Which b and x are the bias
of a way to make seeds at these sizes. The typed values were printed by Lean's evaluator and laid in
by a program; the theorems check them. For proofs only; the program, that is the Lean port built
from OnBytes/, does not import this file.

-/
import OnBytes.Params.RecordRound
import OnBytes.Params.EntryParamsRecordSmall

set_option autoImplicit false

namespace OnBytes.Params
open Bound

/-- The price of the record's round. -/
def smallRecordPrice : Binary := ⟨5912655143704453476220503744237291720752397332754121162756, -367⟩

/-- A radius in whole positions for the table's one-time test. -/
def smallRecordRadius : ℕ := 6137119

/-- The table's word: the length 2 ^ 23 and k, the dimension less 1. -/
theorem rs_word : wordOf smallRecordTable.code = ⟨23, 589822⟩ := by decide +kernel

/-- The reading of m is the printed one, and the extension field has two elements or more. -/
theorem rs_set : smallRecordSet.printed = true ∧ 2 ≤ smallRecordSet.cardE := by decide +kernel

/-- The count of the one-time test is not marked bad; its list size is 114. -/
theorem rs_once : (tableAnalysis smallRecordSet smallRecordTable).once.count.bad = false ∧
    (tableAnalysis smallRecordSet smallRecordTable).once.list = 114 := by decide +kernel

/-- The lower and the upper end of the one-time test's distance times the length, rounded down, are
the typed radius, and the product is not marked bad. -/
theorem rs_radius :
    lowerRadius (tableAnalysis smallRecordSet smallRecordTable).once.delta (2 ^ 23) =
        smallRecordRadius ∧
      upperRadius (tableAnalysis smallRecordSet smallRecordTable).once.delta (2 ^ 23) =
        smallRecordRadius ∧
      ((tableAnalysis smallRecordSet smallRecordTable).once.delta * Bound.ofNat (2 ^ 23)).bad =
        false := by
  decide +kernel

/-- The round that `planRecord` adds has the typed price, which is not the error of a bound that is
marked bad. -/
theorem rs_price : (recordRound smallRecordSet .once smallRecordTable).error = smallRecordPrice ∧
    (sampleError smallRecordSet 114 19 1).error = smallRecordPrice ∧
    (sampleError smallRecordSet 114 19 1).bad = false ∧
    clog2 smallRecordTable.code.ell = 19 ∧ smallRecordTable.answers = 1 := by decide +kernel

/-- The first round of the entry's plan, as `finishHeld` returns it, has the name RECORD and the
typed price. -/
theorem rs_first : ((finishHeld smallRecordSet .once
    (linkPlan ⟨smallRecordLink, smallRecordTable,
      ⟨smallRecordG1, 97, smallRecordStages⟩⟩)).toOption.any fun P =>
      decide ((P.rounds.head?.map fun r => (r.entry.name, r.error)) =
        some ("RECORD", smallRecordPrice))) = true := by decide +kernel

/-- The typed radius is at most 1 less the one-time test's agreement, times the length. -/
theorem small_record_radius_le : (smallRecordRadius : ℝ) ≤
    (1 - (wordOf smallRecordTable.code).agreeAt smallRecordTable.distances.mOnce true) *
      ((wordOf smallRecordTable.code).n : ℝ) := by
  have e1 := (tableAnalysis_fromM (s := smallRecordSet) (T := smallRecordTable) (by decide)).1
  rw [rs_set.1] at e1
  have hn : (wordOf smallRecordTable.code).n = 2 ^ 23 := by
    rw [rs_word]
    rfl
  obtain ⟨r1, _, r3⟩ := rs_radius
  rw [e1] at r1 r3
  have h := lowerRadius_le
    (enclR_johnson_delta (wordOf smallRecordTable.code) smallRecordTable.distances.mOnce true) r3
  rw [r1] at h
  rw [hn]
  exact_mod_cast h

/-- 1 less the one-time test's agreement, times the length, lies below the typed radius and one. -/
theorem small_record_radius_top :
    (1 - (wordOf smallRecordTable.code).agreeAt smallRecordTable.distances.mOnce true) *
      ((wordOf smallRecordTable.code).n : ℝ) < (smallRecordRadius : ℝ) + 1 := by
  have e1 := (tableAnalysis_fromM (s := smallRecordSet) (T := smallRecordTable) (by decide)).1
  rw [rs_set.1] at e1
  have hn : (wordOf smallRecordTable.code).n = 2 ^ 23 := by
    rw [rs_word]
    rfl
  obtain ⟨_, r2, r3⟩ := rs_radius
  rw [e1] at r2 r3
  have h := lt_upperRadius
    (enclR_johnson_delta (wordOf smallRecordTable.code) smallRecordTable.distances.mOnce true) r3
  rw [r2] at h
  rw [hn]
  exact_mod_cast h

/-- The typed radius is below the library's Johnson radius and below the distance of a row's code.
-/
theorem small_record_radius_inJohnson :
    Cb.InJohnson (2 ^ 23) 7798786 smallRecordRadius ∧ smallRecordRadius < 7798786 := by
  unfold Cb.InJohnson smallRecordRadius
  constructor <;> norm_num

/-- **At the small lines the typed price of the record's round covers the library's count of the
record's clashes at the typed radius, with any bias (1 + x) ^ b for 0 ≤ x and 228 b x ≤ 1.** -/
theorem small_record_covers_at {b : ℕ} {x : ℝ} (hx : 0 ≤ x) (hx1 : 228 * (b : ℝ) * x ≤ 1) :
    (1 + x) ^ b *
        ((((Cb.listMax (2 ^ 23) 7798786 smallRecordRadius).choose 2 *
          clashSeeds smallRecordSet.cardE 19 ^ 1 : ℕ) : ℝ) /
            ((allSeeds smallRecordSet.cardE 19 ^ 1 : ℕ) : ℝ)) ≤
      ((smallRecordPrice.val : ℚ) : ℝ) := by
  obtain ⟨o1, o2⟩ := rs_once
  obtain ⟨_, p2, p3, _, _⟩ := rs_price
  have hk : 0 < (wordOf smallRecordTable.code).k := by
    rw [rs_word]
    decide
  have h := record_round_covers (s := smallRecordSet) (T := smallRecordTable)
    (e := smallRecordRadius) (lg := 19) (a := 1) (b := b) (x := x) (by decide) rs_set.1 rs_set.2 o1
    hk small_record_radius_le hx
    (by
      rw [o2]
      push_cast
      linarith)
    (by
      rw [o2]
      decide)
    (by
      rw [o2]
      exact p3)
  rw [o2, p2, rs_word] at h
  exact h

/-- **At `smallRecordLines` the first round of the entry's plan is the record's, at the typed
price.** -/
theorem small_record_first_round : ∃ P, entrySized smallRecordLines =
      .ok (⟨smallRecordLink, smallRecordTable, ⟨smallRecordG1, 97, smallRecordStages⟩⟩,
        smallRecordCodes, P) ∧
    (P.rounds.head?.map fun r => (r.entry.name, r.error)) =
      some ("RECORD", smallRecordPrice) := by
  have hp := rs_first
  cases hP : finishHeld smallRecordSet .once
      (linkPlan ⟨smallRecordLink, smallRecordTable, ⟨smallRecordG1, 97, smallRecordStages⟩⟩) with
  | error e =>
    rw [hP] at hp
    cases hp
  | ok P =>
    rw [hP] at hp
    simp only [Except.toOption, Option.any_some, decide_eq_true_eq] at hp
    exact ⟨P, entrySized_of small_record_table small_record_link hP, hp⟩

end OnBytes.Params

#print axioms OnBytes.Params.rs_word
#print axioms OnBytes.Params.rs_set
#print axioms OnBytes.Params.rs_once
#print axioms OnBytes.Params.rs_radius
#print axioms OnBytes.Params.rs_price
#print axioms OnBytes.Params.rs_first
#print axioms OnBytes.Params.small_record_radius_le
#print axioms OnBytes.Params.small_record_radius_top
#print axioms OnBytes.Params.small_record_radius_inJohnson
#print axioms OnBytes.Params.small_record_covers_at
#print axioms OnBytes.Params.small_record_first_round
