-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Forest/FoEq.lean.
Equality weights on lists, in a commutative ring.

TwV.eqN xs e is the equality weight of the point xs at the corner number e: coordinate i goes with
bit i of e, the lowest first.

States:
  lsum, sum_mul: a list's sum over List.range as a sum over Finset.range; a sum over a product of
    two ranges.
  eqN_append, eqN_total, eqN_split: the weight of a point in two parts is a product; the weights sum
    to 1; a weighted sum over a product of two cubes.
  eqN_low: a table that is repeated reads the low k coordinates alone, for k at most the length.
  binK, eqN_bin: the extension of the table "row s holds s" is the sum of 2^i times coordinate i.
  eqTabK: a plain form of the shipped verifier's eqTab (OnBytes/Model/Frame.lean), where coordinate
    0 belongs to the top bit; eqTabK_len, eqTabK_get: its entry c is eqN of the reversed point at c.
Not claimed here: that eqTab, read into K, is eqTabK. "The shipped verifier" and, in the docstrings,
"the port" are the Lean verifier under OnBytes/, not the C++ verifier.

-/
import Cb.Pv.Lookup.Out.TwV
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Fo
open TwV Finset

section
variable {K : Type} [CommRing K]

theorem lsum (f : ℕ → K) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, lsum f n, Finset.sum_range_succ]
    simp

theorem sum_mul (a : ℕ) (F : ℕ → K) : ∀ b, ∑ r ∈ range (a * b), F r = ∑ j ∈ range b, ∑ i ∈ range a,
    F (a * j + i)
  | 0 => by simp
  | b + 1 => by
    rw [Nat.mul_succ, Finset.sum_range_add, sum_mul a F b, Finset.sum_range_succ]

theorem eqN_append : ∀ (xs ys : List K) (e : ℕ),
    eqN (xs ++ ys) e = eqN xs (e % 2 ^ xs.length) * eqN ys (e / 2 ^ xs.length)
  | [], ys, e => by simp [eqN]
  | x :: xs, ys, e => by
    show (if e % 2 = 1 then x else 1 - x) * eqN (xs ++ ys) (e / 2) =
      ((if e % 2 ^ (xs.length + 1) % 2 = 1 then x else 1 - x) * eqN xs (e % 2 ^ (xs.length + 1) /
          2)) *
        eqN ys (e / 2 ^ (xs.length + 1))
    rw [eqN_append xs ys (e / 2), pow_succ', Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul,
      Nat.mod_mul_right_mod, mul_assoc]

theorem eqN_total : ∀ xs : List K, ∑ e ∈ range (2 ^ xs.length), eqN xs e = 1
  | [] => by simp [eqN]
  | x :: xs => by
    show ∑ e ∈ range (2 ^ (xs.length + 1)), eqN (x :: xs) e = 1
    rw [pow_succ', sum_mul 2]
    have h : ∀ j, ∑ i ∈ range 2, eqN (x :: xs) (2 * j + i) = eqN xs j := by
      intro j
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      show (if (2 * j + 0) % 2 = 1 then x else 1 - x) * eqN xs ((2 * j + 0) / 2) +
        (if (2 * j + 1) % 2 = 1 then x else 1 - x) * eqN xs ((2 * j + 1) / 2) = _
      have e1 : (2 * j + 0) % 2 = 0 := by omega
      have e2 : (2 * j + 0) / 2 = j := by omega
      have e3 : (2 * j + 1) % 2 = 1 := by omega
      have e4 : (2 * j + 1) / 2 = j := by omega
      rw [e1, e2, e3, e4, if_neg (by norm_num), if_pos rfl]
      ring
    rw [Finset.sum_congr rfl fun j _ => h j]
    exact eqN_total xs

/-- A product of two cubes. -/
theorem eqN_split (xs ys : List K) (F : ℕ → ℕ → K) :
    ∑ r ∈ range (2 ^ (xs.length + ys.length)), eqN (xs ++ ys) r * F (r % 2 ^ xs.length) (r / 2 ^
        xs.length) =
      ∑ i ∈ range (2 ^ xs.length), eqN xs i * ∑ j ∈ range (2 ^ ys.length), eqN ys j * F i j := by
  rw [pow_add, sum_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hi' : i < 2 ^ xs.length := Finset.mem_range.mp hi
  have e1 : (2 ^ xs.length * j + i) % 2 ^ xs.length = i := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi']
  have e2 : (2 ^ xs.length * j + i) / 2 ^ xs.length = j := by
    rw [Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hi', Nat.add_zero]
  rw [eqN_append, e1, e2]
  ring

/-- A table that is repeated reads the low k coordinates alone. -/
theorem eqN_low (x : List K) (k : ℕ) (hk : k ≤ x.length) (f : ℕ → K) :
    ∑ t ∈ range (2 ^ x.length), eqN x t * f (t % 2 ^ k) = ∑ s ∈ range (2 ^ k), eqN (x.take k) s * f
        s := by
  have hl : (x.take k).length = k := by rw [List.length_take]; omega
  have hd : (x.take k).length + (x.drop k).length = x.length := by
    rw [← List.length_append, List.take_append_drop]
  have h := eqN_split (x.take k) (x.drop k) fun i _ => f i
  rw [List.take_append_drop, hd, hl] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul, eqN_total, one_mul]

/-- Σ_i 2^i y_i -/
def binK : List K → K
  | [] => 0
  | x :: xs => x + 2 * binK xs

theorem eqN_bin : ∀ y : List K, ∑ s ∈ range (2 ^ y.length), eqN y s * (s : K) = binK y
  | [] => by simp [eqN, binK]
  | x :: xs => by
    show ∑ e ∈ range (2 ^ (xs.length + 1)), eqN (x :: xs) e * (e : K) = x + 2 * binK xs
    rw [pow_succ', sum_mul 2]
    have h : ∀ j : ℕ, ∑ i ∈ range 2, eqN (x :: xs) (2 * j + i) * ((2 * j + i : ℕ) : K) =
        2 * (eqN xs j * (j : K)) + x * eqN xs j := by
      intro j
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      show (if (2 * j + 0) % 2 = 1 then x else 1 - x) * eqN xs ((2 * j + 0) / 2) * ((2 * j + 0 : ℕ)
          : K) +
        (if (2 * j + 1) % 2 = 1 then x else 1 - x) * eqN xs ((2 * j + 1) / 2) * ((2 * j + 1 : ℕ) :
            K) = _
      have e1 : (2 * j + 0) % 2 = 0 := by omega
      have e2 : (2 * j + 0) / 2 = j := by omega
      have e3 : (2 * j + 1) % 2 = 1 := by omega
      have e4 : (2 * j + 1) / 2 = j := by omega
      rw [e1, e2, e3, e4, if_neg (by norm_num), if_pos rfl]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib, ← Finset.mul_sum, ←
        Finset.mul_sum,
      eqN_bin xs, eqN_total xs]
    ring

/-! ### the port's table of equality weights -/

def eqTabStepK (t : List K) (zv : K) : List K := t.flatMap fun a => [a - a * zv, a * zv]
/-- The plain twin of the port's eqTab. -/
def eqTabK (z : List K) : List K := z.foldl eqTabStepK [1]

theorem step_len (t : List K) (zv : K) : (eqTabStepK t zv).length = 2 * t.length := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    show (([a - a * zv, a * zv] : List K) ++ eqTabStepK t zv).length = _
    rw [List.length_append, ih]
    simp
    ring

theorem step_get (zv : K) : ∀ (t : List K) (c : ℕ),
    (eqTabStepK t zv).getD c 0 = (if c % 2 = 1 then zv else 1 - zv) * t.getD (c / 2) 0
  | [], c => by simp [eqTabStepK]
  | a :: t, 0 => by
    show a - a * zv = (if 0 % 2 = 1 then zv else 1 - zv) * a
    rw [if_neg (by norm_num)]
    ring
  | a :: t, 1 => by
    show a * zv = (if 1 % 2 = 1 then zv else 1 - zv) * a
    rw [if_pos rfl]
    ring
  | a :: t, c + 2 => by
    show (eqTabStepK t zv).getD c 0 = (if (c + 2) % 2 = 1 then zv else 1 - zv) * (a :: t).getD ((c +
        2) / 2) 0
    have e1 : (c + 2) % 2 = c % 2 := by omega
    have e2 : (c + 2) / 2 = c / 2 + 1 := by omega
    rw [step_get zv t c, e1, e2]
    rfl

theorem eqTabK_snoc (z : List K) (zv : K) : eqTabK (z ++ [zv]) = eqTabStepK (eqTabK z) zv := by
  unfold eqTabK
  rw [List.foldl_append]
  rfl

theorem eqTabK_len (z : List K) : (eqTabK z).length = 2 ^ z.length := by
  induction z using List.reverseRecOn with
  | nil => rfl
  | append_singleton z zv ih =>
    rw [eqTabK_snoc, step_len, ih, List.length_append, List.length_singleton, pow_succ']

theorem eqTabK_get (z : List K) : ∀ c, (eqTabK z).getD c 0 = if c < 2 ^ z.length then eqN z.reverse
    c else 0 := by
  induction z using List.reverseRecOn with
  | nil =>
    intro c
    cases c with
    | zero => rfl
    | succ c => simp [eqTabK]
  | append_singleton z zv ih =>
    intro c
    rw [eqTabK_snoc, step_get, ih, List.reverse_append, List.length_append, List.length_singleton,
        pow_succ']
    show _ = if c < 2 * 2 ^ z.length then (if c % 2 = 1 then zv else 1 - zv) * eqN z.reverse (c / 2)
        else 0
    by_cases hc : c < 2 * 2 ^ z.length
    · have h2 : c / 2 < 2 ^ z.length := by omega
      rw [if_pos hc, if_pos h2]
    · have h2 : ¬ c / 2 < 2 ^ z.length := by omega
      rw [if_neg hc, if_neg h2, mul_zero]

end
end Fo
