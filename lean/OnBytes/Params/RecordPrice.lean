-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/RecordPrice.lean: the planner's price of the round of a table's record covers a count
of the seeds at which the record does not single one table out, with a bias.

A stored table with a record answers a sample whose seeds follow from the table's name. The planner
has an entry for it, RECORD (`planRecord`, OnBytes/Params/Planner.lean), whose error is
`sampleError` at the list size of the one-time test, the cube of the table's messages and the
table's number of answers. A proof bounds the chance that two members of the table's list have the
same answers by a count of seeds: (L choose 2) times, for each answer, the seeds at which one pair
can clash, among all seeds; and, where the seeds are made from hash blocks, a bias (1 + x) ^ b. This
file compares the numbers. `clashSeeds q lg` and `allSeeds q lg` are these numbers of seeds for one
answer, over a field of q elements: a point of lg coordinates and a factor other than 0. Their
quotient is the planner's error of a pair and one answer: lg / q for a cube of two variables or
more, else 1 / (q - 1) (`clash_share`). For 0 ≤ x with 2 b x ≤ 1, (1 + x) ^ b ≤ 1 + 2 b x
(`one_add_pow_le`). So for L at most the planner's list size, and a bias with 2 b x list ≤ 1, the
count with its bias is at most the number that the planner's price encloses (`record_share_le`: the
room is that between (list choose 2) and list ^ 2 / 2), and so at most the price, where that is not
marked bad (`record_price_covers`). For a table whose distances are given by integers, with m as
printed, L can be the proof library's `Cb.listMax` at the table's code and a radius e that is at
most 1 less the one-time test's agreement, times the length (`record_round_covers`, by
`listMax_le_list`, OnBytes/Params/LibraryJohnson.lean).

Main definitions: `clashSeeds`, `allSeeds`.
Main theorems: `one_add_pow_le`, `clash_share`, `record_share_le`, `record_price_covers`,
`record_round_covers`.
What is not claimed: that the count bounds a chance: that is a matter of the proof that counts. That
`clashSeeds` and `allSeeds` are the numbers of any sample map: `clashSeeds` is typed after the
planner's docstring of `sampleError` and after `recZ_err` (OnBytes/Slice/RecordColl.lean),
`allSeeds` after the docstring of `recZ` (OnBytes/Slice/RecordRead.lean); this file imports neither.
OnBytes/Slice/RecordPriceGlue.lean proves it of the sample map `recZ`: its `err` is `clashSeeds` and
its number of seeds is `allSeeds`, at the number of elements of the extension field, each to the
power of the number of answers (`recZ_err_clash`, `recZ_card_all`). That lg and a in
`record_round_covers` are the cube and the answers that `planRecord` takes: they are arguments. A
committer that tries many names: one table, one try. Nothing on proof of work. That the bias's
condition holds at any numbers; that the price is not marked bad; that k > 0. For proofs only; the
program, that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.LibraryJohnson
import OnBytes.Params.SampleLaws

set_option autoImplicit false

namespace OnBytes.Params
open Bound

/-- For 0 ≤ x with 2 b x ≤ 1: (1 + x) ^ b ≤ 1 + 2 b x. -/
theorem one_add_pow_le {x : ℝ} (hx : 0 ≤ x) : ∀ b : ℕ, 2 * (b : ℝ) * x ≤ 1 →
    (1 + x) ^ b ≤ 1 + 2 * (b : ℝ) * x
  | 0, _ => by simp
  | b + 1, h => by
    have hb : 2 * (b : ℝ) * x ≤ 1 := by
      push_cast at h
      nlinarith
    have ih := one_add_pow_le hx b hb
    have h1 : (0 : ℝ) ≤ 1 + x := by linarith
    calc (1 + x) ^ (b + 1) = (1 + x) ^ b * (1 + x) := pow_succ _ _
      _ ≤ (1 + 2 * (b : ℝ) * x) * (1 + x) := mul_le_mul_of_nonneg_right ih h1
      _ ≤ 1 + 2 * ((b + 1 : ℕ) : ℝ) * x := by
        push_cast
        nlinarith [mul_nonneg hx hx, mul_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ (b : ℝ)) hx]

/-- The seeds at which one pair and one answer can clash, among all seeds of one answer: over a
field of q elements, a point of lg coordinates and a factor other than 0. -/
def clashSeeds (q lg : ℕ) : ℕ := max (lg * q ^ (lg - 1) * (q - 1)) (q ^ lg)

/-- All seeds of one answer. -/
def allSeeds (q lg : ℕ) : ℕ := q ^ lg * (q - 1)

/-- **The share of the clashing seeds is the planner's error of a pair and one answer**: lg / q for
a cube of two variables or more, else 1 / (q - 1). -/
theorem clash_share {q : ℕ} (hq : 2 ≤ q) (lg : ℕ) :
    ((clashSeeds q lg : ℕ) : ℝ) / ((allSeeds q lg : ℕ) : ℝ) =
      if 2 ≤ lg then (lg : ℝ) / (q : ℝ) else 1 / ((q - 1 : ℕ) : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < q - 1)
  unfold clashSeeds allSeeds
  split
  · rename_i h2
    obtain ⟨j, rfl⟩ : ∃ j, lg = j + 1 := ⟨lg - 1, by omega⟩
    have hmax : q ^ (j + 1) ≤ (j + 1) * q ^ (j + 1 - 1) * (q - 1) := by
      rw [Nat.add_sub_cancel, pow_succ]
      have : q ≤ (j + 1) * (q - 1) := by
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
        simp only [show r + 2 - 1 = r + 1 by omega]
        nlinarith
      calc q ^ j * q ≤ q ^ j * ((j + 1) * (q - 1)) := Nat.mul_le_mul_left _ this
        _ = (j + 1) * q ^ j * (q - 1) := by ring
    rw [max_eq_left hmax, Nat.add_sub_cancel]
    push_cast
    rw [pow_succ]
    field_simp
  · rename_i h2
    have hmax : lg * q ^ (lg - 1) * (q - 1) ≤ q ^ lg := by
      have hl : lg = 0 ∨ lg = 1 := by omega
      rcases hl with rfl | rfl
      · simp
      · simp
    rw [max_eq_right hmax]
    push_cast
    field_simp

/-- **The count of a record's clashes, with a bias, against the number that the planner's price of
the record's round encloses.** L: a bound on the list; list: the planner's list size, at least L; a:
the answers; (1 + x) ^ b: the bias, with 2 b x list ≤ 1. -/
theorem record_share_le (s : Setting) {L list lg a b : ℕ} {x : ℝ} (hq : 2 ≤ s.cardE) (hL : L ≤ list)
    (hx : 0 ≤ x) (hb : 2 * (b : ℝ) * x * (list : ℝ) ≤ 1) (h1 : 1 ≤ list) :
    (1 + x) ^ b * (((L.choose 2 * clashSeeds s.cardE lg ^ a : ℕ) : ℝ) /
        ((allSeeds s.cardE lg ^ a : ℕ) : ℝ)) ≤ ((sampleShare s list lg a : ℚ) : ℝ) := by
  have hl1 : (1 : ℝ) ≤ (list : ℝ) := by exact_mod_cast h1
  have hbx0 : 0 ≤ 2 * (b : ℝ) * x := by positivity
  have hbx : 2 * (b : ℝ) * x ≤ 1 := by nlinarith
  have hk := one_add_pow_le hx b hbx
  have hsh := clash_share hq lg
  set w : ℝ := if 2 ≤ lg then (lg : ℝ) / (s.cardE : ℝ) else 1 / ((s.cardE - 1 : ℕ) : ℝ) with hw
  have hw0 : 0 ≤ w := by
    rw [hw]
    split <;> positivity
  have e1 : ((L.choose 2 * clashSeeds s.cardE lg ^ a : ℕ) : ℝ) /
      ((allSeeds s.cardE lg ^ a : ℕ) : ℝ) = (L.choose 2 : ℝ) * w ^ a := by
    push_cast
    rw [mul_div_assoc, ← div_pow, hsh]
  have e2 : ((sampleShare s list lg a : ℚ) : ℝ) = (list : ℝ) * (list : ℝ) / 2 * w ^ a := by
    unfold sampleShare
    rw [hw]
    split <;> push_cast <;> ring
  rw [e1, e2, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hw0 a)
  have hc : (L.choose 2 : ℝ) ≤ (list : ℝ) * ((list : ℝ) - 1) / 2 := by
    have hmono : L.choose 2 ≤ list.choose 2 := Nat.choose_le_choose 2 hL
    have hcl : (list.choose 2 : ℝ) = (list : ℝ) * ((list : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ list
    calc (L.choose 2 : ℝ) ≤ (list.choose 2 : ℝ) := by exact_mod_cast hmono
      _ = _ := hcl
  have hc0 : (0 : ℝ) ≤ (L.choose 2 : ℝ) := Nat.cast_nonneg _
  calc (1 + x) ^ b * (L.choose 2 : ℝ) ≤
        (1 + 2 * (b : ℝ) * x) * ((list : ℝ) * ((list : ℝ) - 1) / 2) :=
        mul_le_mul hk hc hc0 (by linarith)
    _ ≤ (list : ℝ) * (list : ℝ) / 2 := by nlinarith

/-- **The same against the planner's price itself**: the error of `sampleError`, where that bound is
not marked bad. -/
theorem record_price_covers (s : Setting) {L list lg a b : ℕ} {x : ℝ} (hq : 2 ≤ s.cardE)
    (hL : L ≤ list) (hx : 0 ≤ x) (hb : 2 * (b : ℝ) * x * (list : ℝ) ≤ 1) (h1 : 1 ≤ list)
    (g : (sampleError s list lg a).bad = false) :
    (1 + x) ^ b * (((L.choose 2 * clashSeeds s.cardE lg ^ a : ℕ) : ℝ) /
        ((allSeeds s.cardE lg ^ a : ℕ) : ℝ)) ≤ (((sampleError s list lg a).error.val : ℚ) : ℝ) := by
  refine (record_share_le s hq hL hx hb h1).trans ?_
  exact_mod_cast le_error (encl_sampleError s list lg a) g

/-- **The price of the record's round of a table with integers covers the library's count of the
record's clashes, with a bias.** The list on the left is the library's `Cb.listMax` at the table's
code (distance n - k, k being the dimension less 1) and a radius e that is at most 1 less the
one-time test's agreement, times the length; the price on the right is `sampleError` at the list
size of the one-time test, at any cube lg and number of answers a; by its text `planRecord` takes it
at the cube of the table's messages and the table's answers; no law here says so. With m as printed.
-/
theorem record_round_covers {s : Setting} {T : TableSize} {e lg a b : ℕ} {x : ℝ}
    (hM : T.distances.mOnce ≠ 0) (hp : s.printed = true) (hq : 2 ≤ s.cardE)
    (gc : (tableAnalysis s T).once.count.bad = false) (hk : 0 < (wordOf T.code).k)
    (he : (e : ℝ) ≤ (1 - (wordOf T.code).agreeAt T.distances.mOnce true) * ((wordOf T.code).n : ℝ))
    (hx : 0 ≤ x) (hb : 2 * (b : ℝ) * x * ((tableAnalysis s T).once.list : ℝ) ≤ 1)
    (h1 : 1 ≤ (tableAnalysis s T).once.list)
    (g : (sampleError s (tableAnalysis s T).once.list lg a).bad = false) :
    (1 + x) ^ b *
        ((((Cb.listMax (wordOf T.code).n ((wordOf T.code).n - (wordOf T.code).k) e).choose 2 *
          clashSeeds s.cardE lg ^ a : ℕ) : ℝ) / ((allSeeds s.cardE lg ^ a : ℕ) : ℝ)) ≤
      (((sampleError s (tableAnalysis s T).once.list lg a).error.val : ℚ) : ℝ) := by
  have e1 := (tableAnalysis_fromM (s := s) hM).1
  rw [hp] at e1
  have gc' : (johnson (wordOf T.code) T.distances.mOnce true).count.bad = false := by
    rw [← e1]
    exact gc
  have hL : Cb.listMax (wordOf T.code).n ((wordOf T.code).n - (wordOf T.code).k) e ≤
      (tableAnalysis s T).once.list := by
    rw [e1]
    exact listMax_le_list gc' hk he
  exact record_price_covers s hq hL hx hb h1 g

end OnBytes.Params

#print axioms OnBytes.Params.record_price_covers
#print axioms OnBytes.Params.record_round_covers
#print axioms OnBytes.Params.one_add_pow_le
#print axioms OnBytes.Params.clash_share
#print axioms OnBytes.Params.record_share_le
