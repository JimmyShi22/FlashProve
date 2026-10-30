-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/TableJohnson.lean: the planner's list size up to the Johnson radius, against the
counting form of the Johnson bound; and the analysis of a table whose distances are given by
integers.

The planner's list size at an agreement is `johnsonList`: the upper end of (a - lambda) / (a ^ 2 -
lambda), rounded down; `johnson` and `atDistance` call it with the code's rate k / n for lambda
(OnBytes/Params/Distance.lean). With OnBytes/Params/SqrtLaws.lean: where the formula was not asked
outside its range, its value at what the two bounds enclose lies below the list size and one
(`johnsonList_lt`). For `johnson c m printed` with a count that is not marked bad the formula was
not asked outside its range (`johnson_list_good`), so the formula at the agreement that belongs to m
lies below the code's list size and one (`johnson_list_lt`). The formula falls as the agreement
grows (`counting_anti`). So, with m as printed and k > 0, for a radius e in whole positions that is
at most 1 less the agreement, times the length, the formula at the agreement (n - e) / n, cleared of
its denominators, lies below the list size and one: n (n - e - k) < (list + 1) ((n - e) ^ 2 - k n),
over the real numbers (`johnson_list_whole`). A table with a record can have its two distances by
integers (`mOnce` other than 0) or in whole positions. With integers its analysis is `johnson` at
the table's code and these integers (`tableAnalysis_fromM`), so that the laws here and in
OnBytes/Params/JohnsonLaws.lean speak of it.

Main theorems: `johnsonList_lt`, `johnson_list_good`, `johnson_list_lt`, `counting_anti`,
`johnson_list_whole`, `tableAnalysis_fromM`.
What is not claimed: that the formula bounds the number of code words near a word: the docstring of
`johnsonList` says so of codes with a given minimum distance; nothing of it is proved here. Nothing
on the list size that `atDistance` gives, or on a group's list size. Nothing on the other reading of
m in `johnson_list_whole`. Nothing on a table whose distances are named in positions. That a table
with a record has integers other than 0: `sizeRecordedTable` derives them; no law here. Nothing on
the price of the record's round, which is made of the list size. For proofs only; the program, that
is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.GroupJohnson

set_option autoImplicit false

namespace OnBytes.Params
open Bound

/-- **The planner's list size by the counting form of the Johnson bound**, where the formula was not
asked outside its range: the formula at what the two bounds enclose lies below the list size and
one. -/
theorem johnsonList_lt {agree lambda : Bound} {a l : ℝ} (ha : EnclR agree a) (hl : EnclR lambda l)
    (h : (johnsonList agree lambda).2 = false) :
    (a - l) / (a * a - l) < ((johnsonList agree lambda).1 : ℝ) + 1 := by
  unfold johnsonList at h ⊢
  dsimp only at h ⊢
  rw [h]
  simp only [Bool.false_eq_true, if_false]
  have e := (enclR_div (enclR_sub ha hl) (enclR_sub (enclR_mul ha ha) hl) h).2
  have f : ((((agree - lambda) / (agree * agree - lambda)).hi.val : ℚ) : ℝ) <
      (((((agree - lambda) / (agree * agree - lambda)).hi.floor : ℕ) : ℚ) : ℝ) + 1 := by
    exact_mod_cast Binary.lt_floor _
  have f' := lt_of_le_of_lt e f
  simpa using f'

/-- What a count at m that is not marked bad says of the list's formula. -/
theorem johnson_list_good {c : Word} {m : ℕ} {printed : Bool}
    (g : (johnson c m printed).count.bad = false) :
    (johnsonList (johnson c m printed).agree (rhoOf c)).2 = false := by
  have e : (johnson c m printed).count =
      if (decide (m < 3) || decide (c.n ≤ c.k) ||
        (johnsonList (johnson c m printed).agree (rhoOf c)).2) = true then Bound.failed
      else johnsonCount c (rhoOf c) (johnson c m printed).delta m := rfl
  rw [e] at g
  split at g
  · cases g
  · rename_i hb
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hb
    exact hb.2

/-- **The list size of a code at m**, where the count is not marked bad: the counting form of the
Johnson bound at the agreement that belongs to m lies below the list size and one. -/
theorem johnson_list_lt {c : Word} {m : ℕ} {printed : Bool}
    (g : (johnson c m printed).count.bad = false) :
    (c.agreeAt m printed - c.rho) / (c.agreeAt m printed * c.agreeAt m printed - c.rho) <
      ((johnson c m printed).list : ℝ) + 1 :=
  johnsonList_lt (enclR_johnson_agree c m printed) (enclR_rhoOf c) (johnson_list_good g)

/-- The counting form falls as the agreement grows: for 0 ≤ r ≤ 1 and r < a * a, a ≤ x. -/
theorem counting_anti {r a x : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (ha0 : 0 ≤ a) (ha : r < a * a)
    (hx : a ≤ x) : (x - r) / (x * x - r) ≤ (a - r) / (a * a - r) := by
  have hxx : a * a ≤ x * x := mul_self_le_mul_self ha0 hx
  have d1 : 0 < a * a - r := by linarith
  have d2 : 0 < x * x - r := by linarith
  have har : r ≤ a := by
    by_contra hc
    have hc' : a < r := lt_of_not_ge hc
    have : a * a ≤ r * 1 := by nlinarith
    linarith
  rw [div_le_div_iff₀ d2 d1]
  have key : (a - r) * (x * x - r) - (x - r) * (a * a - r) =
      (x - a) * ((a - r) * (x - r) + r * (1 - r)) := by ring
  have hnn : 0 ≤ (x - a) * ((a - r) * (x - r) + r * (1 - r)) := by
    apply mul_nonneg (by linarith)
    have : 0 ≤ (a - r) * (x - r) := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ r * (1 - r) := mul_nonneg h0 (by linarith)
    linarith
  linarith

/-- **The list size of a code at m against a radius in whole positions**, with m as printed: for a
radius e that is at most 1 less the agreement, times the length, the counting form of the Johnson
bound at the agreement (n - e) / n, cleared of its denominators, lies below the list size and one:
n (n - e - k) < (list + 1) ((n - e) ^ 2 - k n). -/
theorem johnson_list_whole {c : Word} {m e : ℕ} (g : (johnson c m true).count.bad = false)
    (hk : 0 < c.k) (he : (e : ℝ) ≤ (1 - c.agreeAt m true) * (c.n : ℝ)) :
    (c.n : ℝ) * (((c.n : ℝ) - (e : ℝ)) - (c.k : ℝ)) <
      (((johnson c m true).list : ℝ) + 1) *
        (((c.n : ℝ) - (e : ℝ)) * ((c.n : ℝ) - (e : ℝ)) - (c.k : ℝ) * (c.n : ℝ)) := by
  obtain ⟨h3, hkn⟩ := johnson_count_good g
  have hn : (0 : ℝ) < (c.n : ℝ) := by
    have : 0 < c.n := by omega
    exact_mod_cast this
  have hk' : (0 : ℝ) < (c.k : ℝ) := by exact_mod_cast hk
  have hkn' : (c.k : ℝ) < (c.n : ℝ) := by exact_mod_cast hkn
  have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hr0 : 0 < c.rho := by unfold Word.rho; positivity
  have hr1 : c.rho ≤ 1 := by
    unfold Word.rho
    rw [div_le_one hn]
    exact hkn'.le
  set s := Real.sqrt c.rho with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hr0
  have hss : s * s = c.rho := Real.mul_self_sqrt hr0.le
  have ha : c.agreeAt m true = s + s / (m : ℝ) := by
    unfold Word.agreeAt
    simp [hs]
  set a := c.agreeAt m true with hadef
  have hsm : 0 < s / (m : ℝ) := by positivity
  have has : s < a := by rw [ha]; linarith
  have ha0 : 0 ≤ a := by linarith
  have haa : c.rho < a * a := by
    rw [← hss]
    exact mul_self_lt_mul_self hs0.le has
  set t := (c.n : ℝ) - (e : ℝ) with ht
  have hta : a * (c.n : ℝ) ≤ t := by rw [ht]; linarith
  have hx : a ≤ t / (c.n : ℝ) := by rw [le_div_iff₀ hn]; exact hta
  have hc := counting_anti hr0.le hr1 ha0 haa hx
  have hl := johnson_list_lt g
  have hlt := lt_of_le_of_lt hc hl
  have hxx : a * a ≤ t / (c.n : ℝ) * (t / (c.n : ℝ)) := mul_self_le_mul_self ha0 hx
  have hd : 0 < t / (c.n : ℝ) * (t / (c.n : ℝ)) - c.rho := by linarith
  rw [div_lt_iff₀ hd] at hlt
  have e1 : t / (c.n : ℝ) - c.rho = (t - (c.k : ℝ)) / (c.n : ℝ) := by
    unfold Word.rho
    field_simp
  have e2 : t / (c.n : ℝ) * (t / (c.n : ℝ)) - c.rho =
      (t * t - (c.k : ℝ) * (c.n : ℝ)) / ((c.n : ℝ) * (c.n : ℝ)) := by
    unfold Word.rho
    field_simp
  rw [e1, e2] at hlt
  have hnn : 0 < (c.n : ℝ) * (c.n : ℝ) := by positivity
  have h5 := mul_lt_mul_of_pos_right hlt hnn
  have l1 : (t - (c.k : ℝ)) / (c.n : ℝ) * ((c.n : ℝ) * (c.n : ℝ)) =
      (c.n : ℝ) * (t - (c.k : ℝ)) := by
    field_simp
  have l2 : (((johnson c m true).list : ℝ) + 1) *
      ((t * t - (c.k : ℝ) * (c.n : ℝ)) / ((c.n : ℝ) * (c.n : ℝ))) * ((c.n : ℝ) * (c.n : ℝ)) =
      (((johnson c m true).list : ℝ) + 1) * (t * t - (c.k : ℝ) * (c.n : ℝ)) := by
    field_simp
  rw [l1, l2] at h5
  exact h5

/-- **A table whose distances are given by integers**: its analysis is `johnson` at the table's code
and the two integers. -/
theorem tableAnalysis_fromM {s : Setting} {T : TableSize} (h : T.distances.mOnce ≠ 0) :
    (tableAnalysis s T).once = johnson (wordOf T.code) T.distances.mOnce s.printed ∧
      (tableAnalysis s T).later = johnson (wordOf T.code) T.distances.mLater s.printed := by
  unfold tableAnalysis
  have hb : (T.distances.mOnce != 0) = true := by simpa using h
  dsimp only
  rw [if_pos hb]
  exact ⟨rfl, rfl⟩

end OnBytes.Params

#print axioms OnBytes.Params.johnsonList_lt
#print axioms OnBytes.Params.johnson_list_good
#print axioms OnBytes.Params.johnson_list_lt
#print axioms OnBytes.Params.counting_anti
#print axioms OnBytes.Params.johnson_list_whole
#print axioms OnBytes.Params.tableAnalysis_fromM
