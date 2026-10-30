-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/RecordRound.lean: the round that the planner adds for a table's record; and, at the
full-size lines of the setting "record with work", its price, a radius, and that the price covers
the proof library's count.

`planRecord` (OnBytes/Params/Planner.lean) writes the entry RECORD. For a table with a record whose
distances are admitted it adds one round, `recordRound`, and changes nothing else
(`planRecord_run`). The round's error is
`sampleError` at the list size of the one-time test, the cube of the table's messages and the
table's answers: the price of which OnBytes/Params/RecordPrice.lean speaks. The second part is at
`recordSet` and `recordTable` (OnBytes/Params/EntryStagesRecord.lean), by evaluations of the planner
in Lean's kernel: the table's word has the length 2 ^ 32 and k = 446693374, the dimension less 1
(`rr_word`); m is read as printed (`rr_set`); the one-time test's count is not marked bad and its
list size is 26 (`rr_once`); the lower and the upper end of its distance times the length, rounded
down, are one number, `recordRadius` = 2852142980 (`rr_radius`); the round's error is the typed
`recordPrice`, at the cube 29 and one answer (`rr_price`); and the first round of the entry's plan
has the name RECORD and that price (`rr_first`, `record_first_round`). So the typed radius is at
most 1 less the one-time test's agreement, times the length, which lies below the radius and one
(`record_radius_le`, `record_radius_top`); it is below the library's Johnson radius and below the
distance 3848273922 of a row's code (`record_radius_inJohnson`); and the typed price covers (1 + 2 ^
-128) ^ 140 times the library's count of the record's clashes at that radius: (`Cb.listMax` choose
2) times the seeds at which one pair can clash, among all seeds (`record_full_covers`; for any bias
(1 + x) ^ 140 with 7280 x ≤ 1: `record_full_covers_at`).

Main definitions: `recordRound`, `recordPrice`, `recordRadius`.
Main theorems: `planRecord_run`, `rr_word`, `rr_set`, `rr_once`, `rr_radius`,
`rr_price`, `rr_first`, `record_radius_le`, `record_radius_top`, `record_radius_inJohnson`,
`record_full_covers_at`, `record_full_covers`, `record_first_round`.
What is not claimed: what the head of OnBytes/Params/RecordPrice.lean does not claim: above all that
the count bounds a chance, and that `clashSeeds` and `allSeeds` are the numbers of any sample map.
That 140 and 2 ^ -128 are the bias of any way to make seeds: 140 is typed after
OnBytes/Slice/SeedRow.lean, which this file does not import; that file writes the base as `kapSl` at
128, and that this is 1 + 2 ^ -128 is not checked here. OnBytes/Slice/SeedBias.lean proves that the
block sampler of a record's seeds reads 140 blocks at the sizes of OnBytes/Slice/RecordFull.lean
(`seedBS_b_full`); OnBytes/Slice/RecordPriceGlue.lean proves that `kapSl 128` is 1 + 2 ^ -128
(`kapSl_real`) and, by `record_full_covers`, that the right side of `coll_pr_full`
(OnBytes/Slice/SeedBias.lean), with its factor `kapSl 128 ^ 140`, is at most `recordPrice` at the
radius `recordRadius` (`record_bound_full_closed`). The planner compares a round's error with the
distance from uniform of its draws added (`wholeError`); the price here is the error without it. The
key's plan, whose first chain has the same entry. The small files. That the example's parameter file
says `recordLines`. The typed values were printed by Lean's evaluator and laid in by hand; the
theorems check them. For proofs only; the program, that is the Lean text `verify-on-bytes`, does
not import this file.

-/
import OnBytes.Params.RecordPrice
import OnBytes.Params.PlanningLaws
import OnBytes.Params.EntryParamsRecord

set_option autoImplicit false

namespace OnBytes.Params
open Bound

/-- The round that `planRecord` adds for a table with a record, under a setting and a scope. -/
def recordRound (s : Setting) (c : Scope) (T : TableSize) : PlanRound :=
  { entry := { name := "RECORD", drawE := T.answers * (clog2 T.code.ell + 1), drawNZ := T.answers },
    error := (sampleError s (tableAnalysis s T).once.list (clog2 T.code.ell) T.answers).error,
    why := .sample, scope := c }

/-- **What `planRecord` does for a table whose distances are admitted**: it adds one
round, `recordRound`, and changes nothing else. -/
theorem planRecord_run {T : TableSize} {p : PlanState}
    (hA : tableAdmitted T (tableAnalysis p.set T) = true) :
    planRecord T p =
      .ok ((), { p with rounds := p.rounds.push (recordRound p.set p.scope T) }) := by
  have hS : theSetting p = .ok (p.set, p) := rfl
  have hC : theScope p = .ok (p.scope, p) := rfl
  have hT : planTable T p = .ok (tableAnalysis p.set T, p) := by
    unfold planTable
    rw [bind_run, hS]
    dsimp only
    rw [bind_run]
    unfold needs
    rw [if_pos hA]
    rfl
  unfold planRecord
  rw [bind_run, hS]
  dsimp only
  rw [bind_run, hT]
  dsimp only
  rw [bind_run, hC]
  rfl

/-! ## At the full-size lines of the setting "record with work" -/

/-- The price of the record's round. -/
def recordPrice : Binary := ⟨3755380325514963501249834132025331418367756793549814235138, -370⟩

/-- A radius in whole positions for the table's one-time test. -/
def recordRadius : ℕ := 2852142980

/-- The table's word: the length 2 ^ 32 and k. -/
theorem rr_word : wordOf recordTable.code = ⟨32, 446693374⟩ := by decide +kernel

/-- The reading of m is the printed one, and the extension field has two elements or more. -/
theorem rr_set : recordSet.printed = true ∧ 2 ≤ recordSet.cardE := by decide +kernel

/-- The count of the one-time test is not marked bad; its list size is 26. -/
theorem rr_once : (tableAnalysis recordSet recordTable).once.count.bad = false ∧
    (tableAnalysis recordSet recordTable).once.list = 26 := by decide +kernel

/-- The lower and the upper end of the one-time test's distance times the length, rounded down, are
the typed radius, and the product is not marked bad. -/
theorem rr_radius :
    lowerRadius (tableAnalysis recordSet recordTable).once.delta (2 ^ 32) = recordRadius ∧
      upperRadius (tableAnalysis recordSet recordTable).once.delta (2 ^ 32) = recordRadius ∧
      ((tableAnalysis recordSet recordTable).once.delta * Bound.ofNat (2 ^ 32)).bad = false := by
  decide +kernel

/-- The round that `planRecord` adds has the typed price, which is not the error of a bound that is
marked bad. -/
theorem rr_price : (recordRound recordSet .once recordTable).error = recordPrice ∧
    (sampleError recordSet 26 29 1).error = recordPrice ∧
    (sampleError recordSet 26 29 1).bad = false ∧
    clog2 recordTable.code.ell = 29 ∧ recordTable.answers = 1 := by decide +kernel

/-- The first round of the entry's plan, as `finishHeld` returns it, has the name RECORD and the
typed price. -/
theorem rr_first : ((finishHeld recordSet .once
    (linkPlan ⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩)).toOption.any fun P =>
      decide ((P.rounds.head?.map fun r => (r.entry.name, r.error)) =
        some ("RECORD", recordPrice))) = true := by decide +kernel

/-- The typed radius is at most 1 less the one-time test's agreement, times the length. -/
theorem record_radius_le : (recordRadius : ℝ) ≤
    (1 - (wordOf recordTable.code).agreeAt recordTable.distances.mOnce true) *
      ((wordOf recordTable.code).n : ℝ) := by
  have e1 := (tableAnalysis_fromM (s := recordSet) (T := recordTable) (by decide)).1
  rw [rr_set.1] at e1
  have hn : (wordOf recordTable.code).n = 2 ^ 32 := by
    rw [rr_word]
    rfl
  obtain ⟨r1, _, r3⟩ := rr_radius
  rw [e1] at r1 r3
  have h := lowerRadius_le
    (enclR_johnson_delta (wordOf recordTable.code) recordTable.distances.mOnce true) r3
  rw [r1] at h
  rw [hn]
  exact_mod_cast h

/-- 1 less the one-time test's agreement, times the length, lies below the typed radius and one. -/
theorem record_radius_top :
    (1 - (wordOf recordTable.code).agreeAt recordTable.distances.mOnce true) *
      ((wordOf recordTable.code).n : ℝ) < (recordRadius : ℝ) + 1 := by
  have e1 := (tableAnalysis_fromM (s := recordSet) (T := recordTable) (by decide)).1
  rw [rr_set.1] at e1
  have hn : (wordOf recordTable.code).n = 2 ^ 32 := by
    rw [rr_word]
    rfl
  obtain ⟨_, r2, r3⟩ := rr_radius
  rw [e1] at r2 r3
  have h := lt_upperRadius
    (enclR_johnson_delta (wordOf recordTable.code) recordTable.distances.mOnce true) r3
  rw [r2] at h
  rw [hn]
  exact_mod_cast h

/-- The typed radius is below the library's Johnson radius and below the distance of a row's code.
-/
theorem record_radius_inJohnson :
    Cb.InJohnson (2 ^ 32) 3848273922 recordRadius ∧ recordRadius < 3848273922 := by
  unfold Cb.InJohnson recordRadius
  constructor <;> norm_num

/-- **At the full-size lines the typed price of the record's round covers the library's count of the
record's clashes at the typed radius, with any bias (1 + x) ^ 140 for 0 ≤ x and 7280 x ≤ 1.** -/
theorem record_full_covers_at {x : ℝ} (hx : 0 ≤ x) (hx1 : 7280 * x ≤ 1) :
    (1 + x) ^ 140 *
        ((((Cb.listMax (2 ^ 32) 3848273922 recordRadius).choose 2 *
          clashSeeds recordSet.cardE 29 ^ 1 : ℕ) : ℝ) /
            ((allSeeds recordSet.cardE 29 ^ 1 : ℕ) : ℝ)) ≤ ((recordPrice.val : ℚ) : ℝ) := by
  obtain ⟨o1, o2⟩ := rr_once
  obtain ⟨_, p2, p3, _, _⟩ := rr_price
  have hk : 0 < (wordOf recordTable.code).k := by
    rw [rr_word]
    decide
  have h := record_round_covers (s := recordSet) (T := recordTable) (e := recordRadius) (lg := 29)
    (a := 1) (b := 140) (x := x) (by decide) rr_set.1 rr_set.2 o1 hk
    record_radius_le hx
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
  rw [o2, p2, rr_word] at h
  exact h

/-- **The same with the bias (1 + 2 ^ -128) ^ 140.** -/
theorem record_full_covers :
    (1 + ((2 : ℝ) ^ 128)⁻¹) ^ 140 *
        ((((Cb.listMax (2 ^ 32) 3848273922 recordRadius).choose 2 *
          clashSeeds recordSet.cardE 29 ^ 1 : ℕ) : ℝ) /
            ((allSeeds recordSet.cardE 29 ^ 1 : ℕ) : ℝ)) ≤ ((recordPrice.val : ℚ) : ℝ) :=
  record_full_covers_at (by positivity) (by norm_num)

/-- **At `recordLines` the first round of the entry's plan is the record's, at the typed price.** -/
theorem record_first_round : ∃ P, entrySized recordLines =
      .ok (⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩, recordCodes, P) ∧
    (P.rounds.head?.map fun r => (r.entry.name, r.error)) = some ("RECORD", recordPrice) := by
  have hp := rr_first
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

#print axioms OnBytes.Params.planRecord_run
#print axioms OnBytes.Params.rr_word
#print axioms OnBytes.Params.rr_set
#print axioms OnBytes.Params.rr_once
#print axioms OnBytes.Params.rr_radius
#print axioms OnBytes.Params.rr_price
#print axioms OnBytes.Params.rr_first
#print axioms OnBytes.Params.record_radius_le
#print axioms OnBytes.Params.record_radius_inJohnson
#print axioms OnBytes.Params.record_radius_top
#print axioms OnBytes.Params.record_full_covers_at
#print axioms OnBytes.Params.record_full_covers
#print axioms OnBytes.Params.record_first_round
