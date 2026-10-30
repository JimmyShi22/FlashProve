-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryCoveredRecord.lean: at the full-size and at the small lines of the setting
"record with work", every round of an entry's plan is covered: its count is at most the error of its
round in the plan.

`recordCounts b x` lists, in the order of `recordBounds` (OnBytes/Params/EntryPricesRecord.lean), a
number for each of the 42 rounds of an entry's plan at the full-size lines, made of the definitions
of OnBytes/Params/EntryCovered.lean at the typed table, groups and radii: for the record's entry the
pairs of the table's list times the share of the seeds at which a pair can clash, with a bias (1 +
x) ^ b; for the link's fold point its count in whole numbers; for the link's round of seeds twice
the like number at the first group's list; for the round of the answers, in which the verifier says
nothing, 0; for the two lists of columns the larger share; for the link's last point 29 / q; for the
batching the first group's list times 128 / q; then the folds and code switches of four stages, and
the last step's two rounds. For any bias with 0 ≤ x and 52 b x ≤ 1 each number is at most the error
of its bound (`record_entry_covered`), and so at most the error of its round in the plan that
`entrySized` returns at `recordLines` (`record_entry_covered_plan`, by `record_plan_prices`). The
like at the small lines: `smallRecordCounts`, 25 rounds, for 228 b x ≤ 1
(`small_record_entry_covered`, `small_record_entry_covered_plan`, by `small_record_plan_prices`,
OnBytes/Params/EntryPricesRecordSmall.lean). The first round of each plan is the entry RECORD, whose
seeds are drawn on a chain of their own; the other 41 and 24 are the rounds of the entry's chain.
The groups' typed radii lie below the library's Johnson radius, for the main and for the repeated
mask code (`record_groups_inJohnson`, `small_record_groups_inJohnson`): beyond it `Cb.listMax` is 0
and a count would say less than it seems to. Beside them, by evaluations in Lean's kernel: a later
test's upper radius is the typed radius (`rl_later`, `rls_later`), and two marks at the small lines
(`rls_pow`); the record's law with any exponent b of the bias (`record_full_covers_any`); and that
no member of `smallRecordBounds` is marked bad (`smallRecordBounds_good_at`).

Main definitions: `recordCounts`, `smallRecordCounts`.
Main theorems: `record_full_covers_any`, `rl_later`, `record_entry_covered`,
`record_entry_covered_plan`, `record_groups_inJohnson`, `smallRecordBounds_good_at`, `rls_pow`,
`rls_later`, `small_record_entry_covered`, `small_record_entry_covered_plan`,
`small_record_groups_inJohnson`.
What is not claimed: that a number in these lists bounds a prover's chance in its round, or is the
count of any lemma: the forms are meant to be those of the library's lemmas on the blocks, none of
which is imported or compared here; the 0 for the round of the answers is this file's own.
OnBytes/Slice/PricedRound.lean compares the forms. OnBytes/Slice/FullRecNum.lean and
OnBytes/Slice/SmallRecNum.lean take the numbers of the two lists, but for the first of each, as
prices of the 41 and 24 written rounds of the entry's chain (`fr_counts`, `fr_priced`; `sr_counts`,
`sr_priced`); with the planner's yes on the two plans, each count in the conclusions of
`fr_link_joh` and `sr_link_joh` is at most 2 ^ -128 as a share of its round's written verifier
messages, work counted, which is no bound on the chance of a false proof (`fr_err_below`,
`sr_err_below`). That the second numbers in the two laws on the Johnson radius are the typed groups'
n - k: they were reckoned by hand. What the heads of OnBytes/Params/EntryCovered.lean and of the
files of laws do not claim: above all the statement on codes behind `Cb.bchksBound`, and that the
repeated mask code is a code of which it speaks. The error is a round's own: the planner adds the
distance from uniform of the round's draws before it compares, and counts the round's work toward
the target; six rounds at full size and four at the small lines have 32 bits of work, and their
errors alone are far above 2 ^ -128. No sum over the rounds. A key's and a proof's plans. For proofs
only; the program, that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.EntryCovered
import OnBytes.Params.EntryPricesRecordSmall

set_option autoImplicit false

namespace OnBytes.Params
open Bound

/-- At the full-size lines the typed price of the record's round covers the library's count of the
record's clashes at the typed radius, with any bias (1 + x) ^ b for 0 ≤ x and 52 b x ≤ 1. -/
theorem record_full_covers_any {b : ℕ} {x : ℝ} (hx : 0 ≤ x) (hx1 : 52 * (b : ℝ) * x ≤ 1) :
    (1 + x) ^ b *
        ((((Cb.listMax (2 ^ 32) 3848273922 recordRadius).choose 2 *
          clashSeeds recordSet.cardE 29 ^ 1 : ℕ) : ℝ) /
            ((allSeeds recordSet.cardE 29 ^ 1 : ℕ) : ℝ)) ≤ ((recordPrice.val : ℚ) : ℝ) := by
  obtain ⟨o1, o2⟩ := rr_once
  obtain ⟨_, p2, p3, _, _⟩ := rr_price
  have hk : 0 < (wordOf recordTable.code).k := by
    rw [rr_word]
    decide
  have h := record_round_covers (s := recordSet) (T := recordTable) (e := recordRadius) (lg := 29)
    (a := 1) (b := b) (x := x) (by decide) rr_set.1 rr_set.2 o1 hk
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

/-- The counts of the 42 rounds of an entry's plan at the full-size lines, in the order of
`recordBounds`: in whole positions, lists and whole numbers of exceptional points, each over the
number of its round's draws. The record's has the bias (1 + x) ^ b. -/
noncomputable def recordCounts (b : ℕ) (x : ℝ) : List ℝ :=
  [(1 + x) ^ b * seedsShare recordSet (Cb.listMax (2 ^ 32) 3848273922 recordRadius) 29 1,
    linkPointCount recordSet recordTable recordRadius recordRadius,
    2 * seedsShare recordSet (groupList recordG1 8342420) 29 1,
    0,
    linkPositionsShare recordTable recordRadius recordRadius 62 62,
    ((29 : ℕ) : ℝ) / (recordSet.cardE : ℝ),
    (groupList recordG1 8342420 : ℝ) * ((129 - 1 : ℕ) : ℝ) / (recordSet.cardE : ℝ)] ++
  foldCounts recordSet recordG1 8342420 ++
  switchCounts recordSet recordG1 recordG2 8342420 1569886 23 97 293 ++
  foldCounts recordSet recordG2 1569886 ++
  switchCounts recordSet recordG2 recordG3 1569886 98104 18 49 149 ++
  foldCounts recordSet recordG3 98104 ++
  switchCounts recordSet recordG3 recordG4 98104 6044 14 49 149 ++
  foldCounts recordSet recordG4 6044 ++
  switchCounts recordSet recordG4 recordG5 6044 13370 10 50 152 ++
  [lastStepCount recordSet recordG5 13370, positionsShare recordG5 13370 40]

/-- A later test's distance at these lines: its upper radius is the typed radius, and the product is
not marked bad. -/
theorem rl_later :
    upperRadius (tableAnalysis recordSet recordTable).later.delta (2 ^ 32) = recordRadius ∧
      ((tableAnalysis recordSet recordTable).later.delta * Bound.ofNat (2 ^ 32)).bad = false := by
  decide +kernel

/-- **At the full-size lines every one of the 42 rounds of an entry's plan is covered**: its count
is at most the error of its formula in `recordBounds`, for any bias of the record's seeds with 0 ≤ x
and 52 b x ≤ 1. -/
theorem record_entry_covered {b : ℕ} {x : ℝ} (hx : 0 ≤ x) (hx1 : 52 * (b : ℝ) * x ≤ 1) :
    List.Forall₂ Covered (recordCounts b x) recordBounds := by
  have hb : ∀ y ∈ recordBounds, y.2.bad = false := fun y hy => recordBounds_good_at hy
  have mk : ∀ (nm : String) (B : Bound), (nm, B) ∈ recordBounds → B.bad = false :=
    fun nm B h => hb (nm, B) h
  have hn : (wordOf recordTable.code).n = 2 ^ 32 := by
    rw [rr_word]
    rfl
  have hk : 0 < (wordOf recordTable.code).k := by
    rw [rr_word]
    decide
  have J1 := record_groups_johnson.1
  have Jn := record_groups_johnson.2.2.2.2
  obtain ⟨m0, g0, gLP, gP0, gPj⟩ := rl_facts
  have h0 : (recordRadius : ℝ) ≤
      (1 - (wordOf recordTable.code).agreeAt recordTable.distances.mLater true) *
        ((wordOf recordTable.code).n : ℝ) := by
    rw [m0]
    exact record_radius_le
  -- the seven rounds before the test's folds
  have c1 : Covered ((1 + x) ^ b *
      seedsShare recordSet (Cb.listMax (2 ^ 32) 3848273922 recordRadius) 29 1)
      ("RECORD", sampleError recordSet (tableAnalysis recordSet recordTable).once.list 29 1) := by
    unfold Covered seedsShare
    dsimp only
    rw [rr_once.2, rr_price.2.1]
    exact record_full_covers_any hx hx1
  have c2 : Covered (linkPointCount recordSet recordTable recordRadius recordRadius)
      ("LINK point", fieldError recordSet recordTable.v +
        tableFoldError recordSet recordTable (tableAnalysis recordSet recordTable).once +
        tableFoldError recordSet recordTable (tableAnalysis recordSet recordTable).later) :=
    link_point_covers_floor (by decide) rr_set.1 rr_once.1 g0 hk record_radius_le h0 gLP
  have c3 : Covered (2 * seedsShare recordSet (groupList recordG1 8342420) 29 1)
      ("SEND seed", Bound.ofWord 2 *
        sampleError recordSet (max (analysisOfM recordSet recordG1).list 1) 29 1) :=
    send_two_covers recordSet rr_set.2 ((listMax_le_group J1).trans (le_max_left _ _))
      (le_max_right _ _) (mk "SEND seed" _ (by
        unfold recordBounds
        simp only [List.mem_append, List.mem_cons, true_or, or_true]))
  have c4 : Covered 0 ("SEND answer", Bound.ofWord 0) := zero_covers
  have c5 : Covered (linkPositionsShare recordTable recordRadius recordRadius 62 62)
      ("LINK", if (Bound.pow (tableAnalysis recordSet recordTable).later.agree 62).hi.lt
          (Bound.pow (tableAnalysis recordSet recordTable).once.agree 62).hi
        then Bound.pow (tableAnalysis recordSet recordTable).once.agree 62
        else Bound.pow (tableAnalysis recordSet recordTable).later.agree 62) := by
    obtain ⟨l1, l2⟩ := rl_later
    obtain ⟨_, r2, r3⟩ := rr_radius
    have h := link_positions_cover_johnson (s := recordSet) (T := recordTable) (e0 := recordRadius)
      (ej := recordRadius) 62 62 (by decide) rr_set.1 (by rw [hn]; exact l2)
      (by rw [hn]; exact l1.le) (by rw [hn]; exact r3) (by rw [hn]; exact r2.le) gP0 gPj
    unfold Covered linkPositionsShare
    dsimp only
    exact h
  have c6 : Covered (((29 : ℕ) : ℝ) / (recordSet.cardE : ℝ))
      ("LINK phi", fieldError recordSet 29) :=
    field_covers recordSet 29 (mk "LINK phi" _ (by
      unfold recordBounds
      simp only [List.mem_append, List.mem_cons, true_or, or_true]))
  have c7 : Covered ((groupList recordG1 8342420 : ℝ) * ((129 - 1 : ℕ) : ℝ) /
      (recordSet.cardE : ℝ))
      ("BAT", Bound.ofNat (max (analysisOfM recordSet recordG1).list 1) *
        powersError recordSet 129) :=
    list_powers_covers recordSet 129 ((listMax_le_group J1).trans (le_max_left _ _))
      (mk "BAT" _ (by
        unfold recordBounds
        simp only [List.mem_append, List.mem_cons, true_or, or_true]))
  have h7 := List.Forall₂.cons c1 (List.Forall₂.cons c2 (List.Forall₂.cons c3 (List.Forall₂.cons c4
    (List.Forall₂.cons c5 (List.Forall₂.cons c6 (List.Forall₂.cons c7 List.Forall₂.nil))))))
  -- the folds and the code switches
  have f1 := fold_covered record_groups_johnson.1 (fun x hx => hb x (by
      unfold recordBounds
      simp only [List.mem_append, hx, true_or, or_true]))
  have s1 := switch_covered record_groups_johnson.1 record_groups_johnson.2.1
    record_groups_upper.1 rr_set.2 23 97 293
    (fun x hx => hb x (by
      unfold recordBounds
      simp only [List.mem_append, hx, true_or, or_true]))
  have f2 := fold_covered record_groups_johnson.2.1 (fun x hx => hb x (by
      unfold recordBounds
      simp only [List.mem_append, hx, true_or, or_true]))
  have s2 := switch_covered record_groups_johnson.2.1 record_groups_johnson.2.2.1
    record_groups_upper.2.1 rr_set.2 18 49 149
    (fun x hx => hb x (by
      unfold recordBounds
      simp only [List.mem_append, hx, true_or, or_true]))
  have f3 := fold_covered record_groups_johnson.2.2.1 (fun x hx => hb x (by
      unfold recordBounds
      simp only [List.mem_append, hx, true_or, or_true]))
  have s3 := switch_covered record_groups_johnson.2.2.1 record_groups_johnson.2.2.2.1
    record_groups_upper.2.2.1 rr_set.2 14 49 149
    (fun x hx => hb x (by
      unfold recordBounds
      simp only [List.mem_append, hx, true_or, or_true]))
  have f4 := fold_covered record_groups_johnson.2.2.2.1 (fun x hx => hb x (by
      unfold recordBounds
      simp only [List.mem_append, hx, true_or, or_true]))
  have s4 := switch_covered record_groups_johnson.2.2.2.1 record_groups_johnson.2.2.2.2
    record_groups_upper.2.2.2.1 rr_set.2 10 50 152
    (fun x hx => hb x (by
      unfold recordBounds
      simp only [List.mem_append, hx, true_or, or_true]))
  -- the last step
  have hBL : Covered (lastStepCount recordSet recordG5 13370)
      ("BASE lambda", baseError recordSet recordG5 (analysisOfM recordSet recordG5)) :=
    base_covers_floor Jn (mk "BASE lambda" _ (by
      unfold recordBounds
      simp only [List.mem_append, List.mem_cons, true_or, or_true]))
  have hBP : Covered (positionsShare recordG5 13370 40)
      ("BASE", Bound.pow (analysisOfM recordSet recordG5).mainAt.agree 40) := by
    obtain ⟨gp, hu⟩ := upperRadius_of_test (record_groups_upper.2.2.2.2)
    exact group_positions_cover Jn gp hu 40 (mk "BASE" _ (by
      unfold recordBounds
      simp only [List.mem_append, List.mem_cons, true_or, or_true]))
  have hZ := List.Forall₂.cons hBL (List.Forall₂.cons hBP List.Forall₂.nil)
  exact covered_append (covered_append (covered_append (covered_append (covered_append
    (covered_append (covered_append (covered_append (covered_append h7 f1) s1) f2) s2) f3) s3) f4)
    s4) hZ

/-- **At `recordLines` each count is at most the error of its round in the plan that `entrySized`
returns.** -/
theorem record_entry_covered_plan {b : ℕ} {x : ℝ} (hx : 0 ≤ x) (hx1 : 52 * (b : ℝ) * x ≤ 1) :
    ∃ P, entrySized recordLines =
        .ok (⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩, recordCodes, P) ∧
      List.Forall₂ (fun (c : ℝ) (r : PlanRound) => c ≤ ((r.error.val : ℚ) : ℝ))
        (recordCounts b x) P.rounds := by
  obtain ⟨P, hP, hm⟩ := record_plan_prices
  refine ⟨P, hP, ?_⟩
  have he : P.rounds.map (·.error) = recordBounds.map (·.2.error) := by
    have h := congrArg (List.map Prod.snd) hm
    simpa [List.map_map, Function.comp_def] using h
  have h : List.Forall₂ (fun (c : ℝ) (e : Binary) => c ≤ ((e.val : ℚ) : ℝ)) (recordCounts b x)
      (recordBounds.map (·.2.error)) :=
    List.forall₂_map_right_iff.mpr (record_entry_covered hx hx1)
  rw [← he] at h
  exact (List.forall₂_map_right_iff (f := fun r : PlanRound => r.error)
    (R := fun (c : ℝ) (e : Binary) => c ≤ ((e.val : ℚ) : ℝ))).mp h

/-- The groups' typed radii at the full-size lines are below the library's Johnson radius, for the
main code and for the repeated mask code. -/
theorem record_groups_inJohnson :
    Cb.InJohnson (2 ^ 24) 12582816 8342420 ∧ Cb.InJohnson (2 ^ 24) 16449536 8342420 ∧
      Cb.InJohnson (2 ^ 21) 1966032 1569886 ∧ Cb.InJohnson (2 ^ 21) 2007040 1569886 ∧
      Cb.InJohnson (2 ^ 17) 122832 98104 ∧ Cb.InJohnson (2 ^ 17) 125440 98104 ∧
      Cb.InJohnson (2 ^ 13) 7631 6044 ∧ Cb.InJohnson (2 ^ 13) 7838 6044 ∧
      Cb.InJohnson (2 ^ 14) 15833 13370 := by
  unfold Cb.InJohnson
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- No member of `smallRecordBounds` is marked bad. -/
theorem smallRecordBounds_good_at {x : String × Bound} (h : x ∈ smallRecordBounds) :
    x.2.bad = false := by
  simpa using List.all_eq_true.mp smallRecordBounds_good.2 x h

/-- The two prices of a link's lists of 51 columns at the small lines are not marked bad. -/
theorem rls_pow :
    (Bound.pow (tableAnalysis smallRecordSet smallRecordTable).later.agree 51).bad = false ∧
      (Bound.pow (tableAnalysis smallRecordSet smallRecordTable).once.agree 51).bad = false := by
  decide +kernel

/-- The counts of the 25 rounds of an entry's plan at the small lines, in the order of
`smallRecordBounds`: in whole positions, lists and whole numbers of exceptional points, each over
the number of its round's draws. The record's has the bias (1 + x) ^ b. -/
noncomputable def smallRecordCounts (b : ℕ) (x : ℝ) : List ℝ :=
  [(1 + x) ^ b * seedsShare smallRecordSet (Cb.listMax (2 ^ 23) 7798786 smallRecordRadius) 19 1,
    linkPointCount smallRecordSet smallRecordTable smallRecordRadius smallRecordRadius,
    2 * seedsShare smallRecordSet (groupList smallRecordG1 65304) 20 1,
    0,
    linkPositionsShare smallRecordTable smallRecordRadius smallRecordRadius 51 51,
    ((19 : ℕ) : ℝ) / (smallRecordSet.cardE : ℝ),
    (groupList smallRecordG1 65304 : ℝ) * ((107 - 1 : ℕ) : ℝ) / (smallRecordSet.cardE : ℝ)] ++
  foldCounts smallRecordSet smallRecordG1 65304 ++
  switchCounts smallRecordSet smallRecordG1 smallRecordG2 65304 10490 16 97 293 ++
  foldCounts smallRecordSet smallRecordG2 10490 ++
  switchCounts smallRecordSet smallRecordG2 smallRecordG3 10490 10490 12 66 200 ++
  [lastStepCount smallRecordSet smallRecordG3 10490, positionsShare smallRecordG3 10490 66]

/-- A later test's distance at these lines: its upper radius is the typed radius, and the product is
not marked bad. -/
theorem rls_later :
    upperRadius (tableAnalysis smallRecordSet smallRecordTable).later.delta (2 ^ 23) =
        smallRecordRadius ∧
      ((tableAnalysis smallRecordSet smallRecordTable).later.delta * Bound.ofNat (2 ^ 23)).bad =
        false := by
  decide +kernel

/-- **At the small lines every one of the 25 rounds of an entry's plan is covered**: its count is
at most the error of its formula in `smallRecordBounds`, for any bias of the record's seeds with 0 ≤
x and 228 b x ≤ 1. -/
theorem small_record_entry_covered {b : ℕ} {x : ℝ} (hx : 0 ≤ x) (hx1 : 228 * (b : ℝ) * x ≤ 1) :
    List.Forall₂ Covered (smallRecordCounts b x) smallRecordBounds := by
  have hb : ∀ y ∈ smallRecordBounds, y.2.bad = false := fun y hy => smallRecordBounds_good_at hy
  have mk : ∀ (nm : String) (B : Bound), (nm, B) ∈ smallRecordBounds → B.bad = false :=
    fun nm B h => hb (nm, B) h
  have hn : (wordOf smallRecordTable.code).n = 2 ^ 23 := by
    rw [rs_word]
    rfl
  have hk : 0 < (wordOf smallRecordTable.code).k := by
    rw [rs_word]
    decide
  have J1 := small_record_groups_johnson.1
  have Jn := small_record_groups_johnson.2.2
  obtain ⟨m0, g0, gLP⟩ := rls_facts
  have h0 : (smallRecordRadius : ℝ) ≤
      (1 - (wordOf smallRecordTable.code).agreeAt smallRecordTable.distances.mLater true) *
        ((wordOf smallRecordTable.code).n : ℝ) := by
    rw [m0]
    exact small_record_radius_le
  -- the seven rounds before the test's folds
  have c1 : Covered ((1 + x) ^ b *
      seedsShare smallRecordSet (Cb.listMax (2 ^ 23) 7798786 smallRecordRadius) 19 1)
      ("RECORD",
        sampleError smallRecordSet (tableAnalysis smallRecordSet smallRecordTable).once.list 19
          1) := by
    unfold Covered seedsShare
    dsimp only
    rw [rs_once.2, rs_price.2.1]
    exact small_record_covers_at hx hx1
  have c2 : Covered
      (linkPointCount smallRecordSet smallRecordTable smallRecordRadius smallRecordRadius)
      ("LINK point", fieldError smallRecordSet smallRecordTable.v +
        tableFoldError smallRecordSet smallRecordTable
          (tableAnalysis smallRecordSet smallRecordTable).once +
        tableFoldError smallRecordSet smallRecordTable
          (tableAnalysis smallRecordSet smallRecordTable).later) :=
    link_point_covers_floor (by decide) rs_set.1 rs_once.1 g0 hk small_record_radius_le h0 gLP
  have c3 : Covered (2 * seedsShare smallRecordSet (groupList smallRecordG1 65304) 20 1)
      ("SEND seed", Bound.ofWord 2 *
        sampleError smallRecordSet (max (analysisOfM smallRecordSet smallRecordG1).list 1) 20 1) :=
    send_two_covers smallRecordSet rs_set.2 ((listMax_le_group J1).trans (le_max_left _ _))
      (le_max_right _ _) (mk "SEND seed" _ (by
        unfold smallRecordBounds
        simp only [List.mem_append, List.mem_cons, true_or, or_true]))
  have c4 : Covered 0 ("SEND answer", Bound.ofWord 0) := zero_covers
  have c5 : Covered (linkPositionsShare smallRecordTable smallRecordRadius smallRecordRadius 51 51)
      ("LINK", if (Bound.pow (tableAnalysis smallRecordSet smallRecordTable).later.agree 51).hi.lt
          (Bound.pow (tableAnalysis smallRecordSet smallRecordTable).once.agree 51).hi
        then Bound.pow (tableAnalysis smallRecordSet smallRecordTable).once.agree 51
        else Bound.pow (tableAnalysis smallRecordSet smallRecordTable).later.agree 51) := by
    obtain ⟨l1, l2⟩ := rls_later
    obtain ⟨_, r2, r3⟩ := rs_radius
    have h := link_positions_cover_johnson (s := smallRecordSet) (T := smallRecordTable)
      (e0 := smallRecordRadius) (ej := smallRecordRadius) 51 51 (by decide) rs_set.1
      (by rw [hn]; exact l2)
      (by rw [hn]; exact l1.le) (by rw [hn]; exact r3) (by rw [hn]; exact r2.le) rls_pow.1 rls_pow.2
    unfold Covered linkPositionsShare
    dsimp only
    exact h
  have c6 : Covered (((19 : ℕ) : ℝ) / (smallRecordSet.cardE : ℝ))
      ("LINK phi", fieldError smallRecordSet 19) :=
    field_covers smallRecordSet 19 (mk "LINK phi" _ (by
      unfold smallRecordBounds
      simp only [List.mem_append, List.mem_cons, true_or, or_true]))
  have c7 : Covered ((groupList smallRecordG1 65304 : ℝ) * ((107 - 1 : ℕ) : ℝ) /
      (smallRecordSet.cardE : ℝ))
      ("BAT", Bound.ofNat (max (analysisOfM smallRecordSet smallRecordG1).list 1) *
        powersError smallRecordSet 107) :=
    list_powers_covers smallRecordSet 107 ((listMax_le_group J1).trans (le_max_left _ _))
      (mk "BAT" _ (by
        unfold smallRecordBounds
        simp only [List.mem_append, List.mem_cons, true_or, or_true]))
  have h7 := List.Forall₂.cons c1 (List.Forall₂.cons c2 (List.Forall₂.cons c3 (List.Forall₂.cons c4
    (List.Forall₂.cons c5 (List.Forall₂.cons c6 (List.Forall₂.cons c7 List.Forall₂.nil))))))
  -- the folds and the code switches
  have f1 := fold_covered small_record_groups_johnson.1 (fun x hx => hb x (by
      unfold smallRecordBounds
      simp only [List.mem_append, hx, true_or, or_true]))
  have s1 := switch_covered small_record_groups_johnson.1 small_record_groups_johnson.2.1
    small_record_groups_upper.1 rs_set.2 16 97 293
    (fun x hx => hb x (by
      unfold smallRecordBounds
      simp only [List.mem_append, hx, true_or, or_true]))
  have f2 := fold_covered small_record_groups_johnson.2.1 (fun x hx => hb x (by
      unfold smallRecordBounds
      simp only [List.mem_append, hx, true_or, or_true]))
  have s2 := switch_covered small_record_groups_johnson.2.1 small_record_groups_johnson.2.2
    small_record_groups_upper.2.1 rs_set.2 12 66 200
    (fun x hx => hb x (by
      unfold smallRecordBounds
      simp only [List.mem_append, hx, true_or, or_true]))
  -- the last step
  have hBL : Covered (lastStepCount smallRecordSet smallRecordG3 10490)
      ("BASE lambda",
        baseError smallRecordSet smallRecordG3 (analysisOfM smallRecordSet smallRecordG3)) :=
    base_covers_floor Jn (mk "BASE lambda" _ (by
      unfold smallRecordBounds
      simp only [List.mem_append, List.mem_cons, true_or, or_true]))
  have hBP : Covered (positionsShare smallRecordG3 10490 66)
      ("BASE", Bound.pow (analysisOfM smallRecordSet smallRecordG3).mainAt.agree 66) := by
    obtain ⟨gp, hu⟩ := upperRadius_of_test (small_record_groups_upper.2.2)
    exact group_positions_cover Jn gp hu 66 (mk "BASE" _ (by
      unfold smallRecordBounds
      simp only [List.mem_append, List.mem_cons, true_or, or_true]))
  have hZ := List.Forall₂.cons hBL (List.Forall₂.cons hBP List.Forall₂.nil)
  exact covered_append
    (covered_append (covered_append (covered_append (covered_append h7 f1) s1) f2) s2) hZ

/-- **At `smallRecordLines` each count is at most the error of its round in the plan that
`entrySized` returns.** -/
theorem small_record_entry_covered_plan {b : ℕ} {x : ℝ} (hx : 0 ≤ x) (hx1 : 228 * (b : ℝ) * x ≤ 1) :
    ∃ P, entrySized smallRecordLines =
        .ok (⟨smallRecordLink, smallRecordTable, ⟨smallRecordG1, 97, smallRecordStages⟩⟩,
          smallRecordCodes, P) ∧
      List.Forall₂ (fun (c : ℝ) (r : PlanRound) => c ≤ ((r.error.val : ℚ) : ℝ))
        (smallRecordCounts b x) P.rounds := by
  obtain ⟨P, hP, hm⟩ := small_record_plan_prices
  refine ⟨P, hP, ?_⟩
  have he : P.rounds.map (·.error) = smallRecordBounds.map (·.2.error) := by
    have h := congrArg (List.map Prod.snd) hm
    simpa [List.map_map, Function.comp_def] using h
  have h : List.Forall₂ (fun (c : ℝ) (e : Binary) => c ≤ ((e.val : ℚ) : ℝ)) (smallRecordCounts b x)
      (smallRecordBounds.map (·.2.error)) :=
    List.forall₂_map_right_iff.mpr (small_record_entry_covered hx hx1)
  rw [← he] at h
  exact (List.forall₂_map_right_iff (f := fun r : PlanRound => r.error)
    (R := fun (c : ℝ) (e : Binary) => c ≤ ((e.val : ℚ) : ℝ))).mp h

/-- The groups' typed radii at the small lines are below the library's Johnson radius, for the main
code and for the repeated mask code. -/
theorem small_record_groups_inJohnson :
    Cb.InJohnson (2 ^ 17) 98208 65304 ∧ Cb.InJohnson (2 ^ 17) 128512 65304 ∧
      Cb.InJohnson (2 ^ 14) 14271 10490 ∧ Cb.InJohnson (2 ^ 14) 15612 10490 ∧
      Cb.InJohnson (2 ^ 14) 15807 10490 := by
  unfold Cb.InJohnson
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

end OnBytes.Params

#print axioms OnBytes.Params.record_entry_covered_plan
#print axioms OnBytes.Params.record_groups_inJohnson
#print axioms OnBytes.Params.small_record_entry_covered_plan
#print axioms OnBytes.Params.small_record_groups_inJohnson
#print axioms OnBytes.Params.record_full_covers_any
#print axioms OnBytes.Params.rl_later
#print axioms OnBytes.Params.record_entry_covered
#print axioms OnBytes.Params.smallRecordBounds_good_at
#print axioms OnBytes.Params.rls_pow
#print axioms OnBytes.Params.rls_later
#print axioms OnBytes.Params.small_record_entry_covered
