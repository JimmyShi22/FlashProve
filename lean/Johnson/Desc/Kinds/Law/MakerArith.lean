--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/MakerArith.lean.
WHAT IT DOES NOT SHOW. Nothing on cells, forms or a protocol: arithmetic alone, for Law/CellsOfSays.
WHAT IT IS.
  topD, midD        a number q cut in a top and a middle digit, the top's unit being 2^15 middles,
                    SO THAT THE MIDDLE DIGIT IS 0 ONLY WHERE q IS 0: below 2^16 all of q is the
                    middle digit; from there on the middle digit is q mod 2^15 + 2^15.
  digits_add, midD_range, midD_pos, topD_range   2^15 top + mid = q; 0 <= mid < 2^16; mid is not 0
                    where 1 <= q; 0 <= top < 2^16 where q < (2^16 + 1) 2^15.
  share, share_le, share_sum   a sum S dealt over n places: S / n each, and 1 more at the first
                    S mod n: at most b each where S <= b n; they add up to S.
  sum_costed_run    a sum over the positions with a cost is a sum over their numbers from 0.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.CellsWithCosts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open Norm (lt ls d lPd T S2)

/-- The middle digit. -/
def midD (q : Int) : Int := if q < 2 ^ 16 then q else q % 2 ^ 15 + 2 ^ 15
/-- The top digit. -/
def topD (q : Int) : Int := if q < 2 ^ 16 then 0 else q / 2 ^ 15 - 1

theorem digits_add (q : Int) : 2 ^ 15 * topD q + midD q = q := by
  unfold topD midD
  split
  · ring
  · have := Int.mul_ediv_add_emod q (2 ^ 15)
    linarith

theorem midD_range {q : Int} (h : 0 ≤ q) : 0 ≤ midD q ∧ midD q < 2 ^ 16 := by
  unfold midD
  split
  · exact ⟨h, by assumption⟩
  · have h1 := Int.emod_nonneg q (show (2 : Int) ^ 15 ≠ 0 by norm_num)
    have h2 := Int.emod_lt_of_pos q (show (0 : Int) < 2 ^ 15 by norm_num)
    constructor
    · positivity
    · norm_num at h2 ⊢
      omega

theorem midD_pos {q : Int} (h : 1 ≤ q) : 1 ≤ midD q := by
  unfold midD
  split
  · exact h
  · have h1 := Int.emod_nonneg q (show (2 : Int) ^ 15 ≠ 0 by norm_num)
    norm_num
    omega

theorem midD_zero : midD 0 = 0 := by
  unfold midD
  norm_num

theorem topD_range {q : Int} (h : q < (2 ^ 16 + 1) * 2 ^ 15) : 0 ≤ topD q ∧ topD q < 2 ^ 16 := by
  unfold topD
  split
  · norm_num
  · rename_i hq
    have hq' : (2 : Int) ^ 16 ≤ q := not_lt.mp hq
    have h1 : 2 ≤ q / 2 ^ 15 := Int.le_ediv_of_mul_le (by norm_num) (by norm_num at hq' ⊢; omega)
    have h2 : q / 2 ^ 15 < 2 ^ 16 + 1 := Int.ediv_lt_of_lt_mul (by norm_num) h
    constructor <;> omega

/-- The share of place i where S is dealt over n places. -/
def share (S n i : Nat) : Nat := S / n + if i < S % n then 1 else 0

theorem share_le {S n b : Nat} (h : S ≤ b * n) (hn : 0 < n) (i : Nat) : share S n i ≤ b := by
  unfold share
  have h1 : S / n ≤ b := Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact h)
  split
  · rename_i hi
    by_contra hc
    have e : S / n = b := by omega
    have h2 := Nat.div_add_mod S n
    rw [e] at h2
    have : n * b = b * n := Nat.mul_comm _ _
    omega
  · omega

theorem share_sum (S : Nat) {n : Nat} (hn : 0 < n) :
    (Finset.range n).sum (share S n) = S := by
  unfold share
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.sum_filter,
    Finset.sum_const]
  have hm := Nat.mod_lt S hn
  have : (Finset.range n).filter (fun i => i < S % n) = Finset.range (S % n) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range]
    omega
  rw [this, Finset.card_range]
  have := Nat.div_add_mod S n
  simp only [smul_eq_mul, mul_one]
  omega

variable [Sizes] [Policy] [Request] [Token]

/-- **A sum over the positions with a cost is a sum over their numbers, counted from 0.** -/
theorem sum_costed_run (f : Nat → Int) :
    ((Finset.range T).sum fun t => if costed t = true then f (t - r) else 0) =
      (Finset.range RC).sum f := by
  rw [← Finset.sum_filter]
  have : (Finset.range T).filter (fun t => costed t = true) = Finset.Ico r (min e (T - 1)) := by
    ext t
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, costed_iff_min]
    omega
  rw [this, Finset.sum_Ico_eq_sum_range]
  unfold RC
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.add_sub_cancel_left]

end VerifiableInference.Desc.Kinds.Head.Law
