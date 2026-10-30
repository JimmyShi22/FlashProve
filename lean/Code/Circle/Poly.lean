-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Code/Circle/Poly.lean: the polynomial algebra behind circle codes.

Any field; where needed, 2 ≠ 0 is a hypothesis.

If 2 ≠ 0, a point (x, y) of the circle x^2 + y^2 = 1 other than (-1, 0) is given by its projection
from (-1, 0), the element t = y / (1 + x) (`theta` in Code/Circle/Basis.lean), so that
x = (1 - t^2) / (1 + t^2) and y = 2 t / (1 + t^2). In this file the basis functions are functions
of t. `basis B j` reads the lowest B + 1 binary digits of j. Code/Circle/Basis.lean relates these
functions to bas_j on points.

The file shows, for a vector c of K coefficients with K ≤ 2^(B+1):
 * `wordPoly B K c` is a polynomial in t of degree at most 2 (K / 2)
   (`wordPoly_natDegree_le_two_mul`);
 * its value at t, if 1 + t^2 ≠ 0, is (1 + t^2)^(K/2) times the linear combination of the first K
   basis functions with the coefficients c (`wordPoly_eval_any`);
 * if 2 ≠ 0, it is 0 only for c = 0 (`wordPoly_eq_zero` for even K, `wordPoly_eq_zero_odd` for odd
   K).

The argument for the last point. The polynomial has the form u(t^2) + t v(t^2), because the basis
functions with an even index are even in t and those with an odd index are odd. So it is 0 only if u
and v are 0. In the variable s = t^2, u is a sum of terms a_k (1 + s)^(K/2 - k) q_k in which q_k is
not 0 at s = -1. The terms vanish at s = -1 to different orders, so the sum is 0 only if every a_k
is 0. The same holds for v.

Notation: B: a natural number; `basis B j` is basis function `j`, for `j < 2^(B+1)`; `pl`
(`sum_testBit`): a natural number; the sum there is over the indices j < pl; s: in part 3 and in the
argument above, s = t^2; in `wordPoly_eval_any`, a value of t.
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Code.Circle

open Polynomial

/-- The sum of 2^j over the indices j < pl at which n has the binary digit 1 is n % 2^pl. -/
theorem sum_testBit (pl n : ℕ) :
    (∑ j ∈ Finset.range pl, if n.testBit j then 2 ^ j else 0) = n % 2 ^ pl := by
  induction pl with
  | zero => simp [Nat.mod_one]
  | succ pl ih =>
    rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ pl) with h | h <;> simp [h]

variable {E : Type*} [Field E]

/-! ## 1. The basis functions in the variable t, and their numerators -/

/-- The first coordinate x of the point with the projection `t`. -/
def xAt (t : E) : E := (1 - t ^ 2) / (1 + t ^ 2)

/-- The second coordinate y of the point with the projection `t`. -/
def yAt (t : E) : E := 2 * t / (1 + t ^ 2)

/-- The point with the projection `t` is on the circle, if `1 + t ^ 2 ≠ 0`. -/
theorem on_circle (t : E) (h : 1 + t ^ 2 ≠ 0) : xAt t ^ 2 + yAt t ^ 2 = 1 := by
  unfold xAt yAt
  field_simp
  ring

/-- In a field in which 2 is non-zero, every point (x, y) of the circle other than (-1, 0) is the
point with the projection y / (1 + x). -/
theorem proj (h2 : (2 : E) ≠ 0) (x y : E) (hxy : x ^ 2 + y ^ 2 = 1) (hx : 1 + x ≠ 0) :
    1 + (y / (1 + x)) ^ 2 ≠ 0 ∧ xAt (y / (1 + x)) = x ∧ yAt (y / (1 + x)) = y := by
  have hy : y ^ 2 = 1 - x ^ 2 := by linear_combination hxy
  have hden : 1 + (y / (1 + x)) ^ 2 = 2 / (1 + x) := by
    field_simp
    rw [hy]
    ring
  have hne : 1 + (y / (1 + x)) ^ 2 ≠ 0 := by
    rw [hden]
    exact div_ne_zero h2 hx
  refine ⟨hne, ?_, ?_⟩
  · unfold xAt
    rw [hden]
    field_simp
    rw [hy]
    ring
  · unfold yAt
    rw [hden]
    field_simp

/-- `Xs 0 = x` and `Xs (i + 1) = 2 (Xs i)^2 - 1`. `Xs i` is the first coordinate of the 2^i-th power
of the point (Code/Circle/Basis.lean). -/
def Xs : ℕ → E → E
  | 0, t => xAt t
  | i + 1, t => 2 * Xs i t ^ 2 - 1

/-- Basis function `j`, for `j < 2^(B+1)`: the factor y if binary digit 0 of `j` is 1, times `Xs i`
for each `i < B` such that binary digit `i + 1` of `j` is 1. -/
def basis (B j : ℕ) (t : E) : E :=
  (if j.testBit 0 then yAt t else 1) * ∏ i ∈ Finset.range B, if j.testBit (i + 1) then Xs i t else 1

theorem basis_zero (B : ℕ) (t : E) : basis B 0 t = 1 := by
  simp [basis]

theorem basis_one (B : ℕ) (t : E) : basis B 1 t = yAt t := by
  have h : ∀ i, (1 : ℕ).testBit (i + 1) = false := fun i => by
    rw [Nat.testBit_succ]
    simp
  simp [basis, h]

/-- The recursion of the basis functions: `basis B (2^(k+1) + j) = basis B j * Xs k`, for `j <
2^(k+1)` and `k < B`. -/
theorem basis_add (B k j : ℕ) (hk : k < B) (hj : j < 2 ^ (k + 1)) (t : E) :
    basis B (2 ^ (k + 1) + j) t = basis B j t * Xs k t := by
  have h0 : (2 ^ (k + 1) + j).testBit 0 = j.testBit 0 :=
    Nat.testBit_two_pow_add_gt (Nat.succ_pos k) j
  have hself : (2 ^ (k + 1) + j).testBit (k + 1) = true := by
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hj]
    rfl
  have hjk : j.testBit (k + 1) = false := Nat.testBit_lt_two_pow hj
  have hoff : ∀ i, i ≠ k → (2 ^ (k + 1) + j).testBit (i + 1) = j.testBit (i + 1) := fun i hi => by
    rcases Nat.lt_or_gt_of_ne hi with h | h
    · exact Nat.testBit_two_pow_add_gt (Nat.succ_lt_succ h) j
    · have hle : 2 ^ (k + 2) ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h1 : 2 ^ (k + 1) + j < 2 ^ (i + 1) := by
        have h2 : 2 ^ (k + 2) = 2 ^ (k + 1) * 2 := pow_succ 2 (k + 1)
        omega
      have h3 : j < 2 ^ (i + 1) := by omega
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h3]
  unfold basis
  rw [h0, mul_assoc]
  congr 1
  rw [← Finset.mul_prod_erase (Finset.range B) _ (Finset.mem_range.mpr hk),
    ← Finset.mul_prod_erase (Finset.range B)
      (fun i => if j.testBit (i + 1) then Xs i t else 1) (Finset.mem_range.mpr hk),
    if_pos hself, if_neg (by rw [hjk]; exact Bool.false_ne_true), one_mul, mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun i hi => by rw [hoff i (Finset.ne_of_mem_erase hi)]

/-- The total degree of basis function `j` in the two coordinates x and y. -/
def deg (B j : ℕ) : ℕ :=
  (if j.testBit 0 then 1 else 0) + ∑ i ∈ Finset.range B, if j.testBit (i + 1) then 2 ^ i else 0

/-- The polynomial in t that equals `(1 + t^2)^(2^i) * Xs i t` at every t with `1 + t^2 ≠ 0`
(`xP_eval`). -/
def xP : ℕ → E[X]
  | 0 => 1 - X ^ 2
  | i + 1 => 2 * xP i ^ 2 - (1 + X ^ 2) ^ 2 ^ (i + 1)

theorem xP_eval (t : E) (h : 1 + t ^ 2 ≠ 0) : ∀ i : ℕ, (xP i).eval t = (1 + t ^ 2) ^ 2 ^ i * Xs i t
  | 0 => by
    simp only [xP, Xs, xAt, eval_sub, eval_one, eval_pow, eval_X, pow_zero, pow_one]
    field_simp
  | i + 1 => by
    have ih := xP_eval t h i
    simp only [xP, Xs, eval_sub, eval_mul, eval_pow, eval_add, eval_one, eval_X, eval_ofNat]
    rw [ih, pow_succ 2 i, pow_mul]
    ring

theorem natDegree_den_pow_le (k : ℕ) : ((1 + X ^ 2 : E[X]) ^ k).natDegree ≤ 2 * k := by
  refine le_trans natDegree_pow_le ?_
  have h : (1 + X ^ 2 : E[X]).natDegree ≤ 2 := by
    refine le_trans (natDegree_add_le _ _) ?_
    rw [natDegree_one]
    exact max_le (Nat.zero_le _) (natDegree_X_pow_le 2)
  calc k * (1 + X ^ 2 : E[X]).natDegree ≤ k * 2 := Nat.mul_le_mul_left _ h
    _ = 2 * k := Nat.mul_comm _ _

theorem xP_natDegree_le : ∀ i : ℕ, (xP (E := E) i).natDegree ≤ 2 * 2 ^ i
  | 0 => by
    refine le_trans (natDegree_sub_le _ _) ?_
    rw [natDegree_one]
    exact max_le (Nat.zero_le _) (le_trans (natDegree_X_pow_le 2) (by norm_num))
  | i + 1 => by
    have ih := xP_natDegree_le i
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ (natDegree_den_pow_le _))
    refine le_trans (natDegree_mul_le) ?_
    have h2 : (2 : E[X]).natDegree = 0 := natDegree_ofNat 2
    have h3 : (xP (E := E) i ^ 2).natDegree ≤ 2 * (2 * 2 ^ i) :=
      le_trans natDegree_pow_le (Nat.mul_le_mul_left _ ih)
    rw [h2, Nat.zero_add, pow_succ]
    calc (xP (E := E) i ^ 2).natDegree ≤ 2 * (2 * 2 ^ i) := h3
      _ = 2 * (2 ^ i * 2) := by ring

/-- The polynomial in t that equals `(1 + t^2) * yAt t` at every t with `1 + t^2 ≠ 0`
(`yP_eval`). -/
def yP : E[X] := 2 * X

theorem yP_eval (t : E) (h : 1 + t ^ 2 ≠ 0) : (yP (E := E)).eval t = (1 + t ^ 2) * yAt t := by
  simp only [yP, yAt, eval_mul, eval_X, eval_ofNat]
  field_simp

theorem yP_natDegree_le : (yP (E := E)).natDegree ≤ 2 := by
  refine le_trans natDegree_mul_le ?_
  rw [natDegree_ofNat]
  exact le_trans (Nat.add_le_add_left natDegree_X_le 0) (by norm_num)

/-- The polynomial in t that equals `(1 + t^2)^(deg B j) * basis B j t` at every t with
`1 + t^2 ≠ 0` (`bP_eval`). -/
def bP (B j : ℕ) : E[X] :=
  (if j.testBit 0 then yP else 1) * ∏ i ∈ Finset.range B, if j.testBit (i + 1) then xP i else 1

theorem bP_eval (t : E) (h : 1 + t ^ 2 ≠ 0) (B j : ℕ) :
    (bP B j).eval t = (1 + t ^ 2) ^ deg B j * basis B j t := by
  have h0 : (if j.testBit 0 then (yP : E[X]) else 1).eval t =
      (1 + t ^ 2) ^ (if j.testBit 0 then 1 else 0) * (if j.testBit 0 then yAt t else 1) := by
    by_cases hb : j.testBit 0 = true
    · rw [if_pos hb, if_pos hb, if_pos hb, yP_eval t h, pow_one]
    · rw [if_neg hb, if_neg hb, if_neg hb, eval_one, pow_zero, one_mul]
  have h1 : ∀ i, (if j.testBit (i + 1) then (xP i : E[X]) else 1).eval t =
      (1 + t ^ 2) ^ (if j.testBit (i + 1) then 2 ^ i else 0) *
        (if j.testBit (i + 1) then Xs i t else 1) := fun i => by
    by_cases hb : j.testBit (i + 1) = true
    · rw [if_pos hb, if_pos hb, if_pos hb, xP_eval t h i]
    · rw [if_neg hb, if_neg hb, if_neg hb, eval_one, pow_zero, one_mul]
  rw [bP, eval_mul, eval_prod, h0, Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, deg, basis, pow_add]
  ring

theorem bP_natDegree_le (B j : ℕ) : (bP (E := E) B j).natDegree ≤ 2 * deg B j := by
  have h0 : (if j.testBit 0 then (yP : E[X]) else 1).natDegree ≤
      2 * (if j.testBit 0 then 1 else 0) := by
    by_cases hb : j.testBit 0 = true
    · rw [if_pos hb, if_pos hb]
      exact yP_natDegree_le
    · rw [if_neg hb, if_neg hb, natDegree_one]
  have h1 : ∀ i, (if j.testBit (i + 1) then (xP i : E[X]) else 1).natDegree ≤
      2 * (if j.testBit (i + 1) then 2 ^ i else 0) := fun i => by
    by_cases hb : j.testBit (i + 1) = true
    · rw [if_pos hb, if_pos hb]
      exact xP_natDegree_le i
    · rw [if_neg hb, if_neg hb, natDegree_one]
  refine le_trans natDegree_mul_le ?_
  rw [deg, Nat.mul_add, Finset.mul_sum]
  exact Nat.add_le_add h0 (le_trans (natDegree_prod_le _ _) (Finset.sum_le_sum fun i _ => h1 i))

/-- For `j < 2^(B+1)`, the degree of basis function `j` is `j % 2 + j / 2`. -/
theorem deg_eq (B j : ℕ) (hj : j < 2 ^ (B + 1)) : deg B j = j % 2 + j / 2 := by
  have h0 : (if j.testBit 0 then 1 else 0) = j % 2 := by
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h]
  have h1 : (∑ i ∈ Finset.range B, if j.testBit (i + 1) then 2 ^ i else 0) = (j / 2) % 2 ^ B := by
    rw [← sum_testBit B (j / 2)]
    exact Finset.sum_congr rfl fun i _ => by rw [Nat.testBit_succ]
  have h2 : j / 2 < 2 ^ B := by
    rw [pow_succ] at hj
    omega
  rw [deg, h0, h1, Nat.mod_eq_of_lt h2]

/-! ## 2. The polynomial of a codeword -/

/-- The polynomial of a codeword: `(1 + t^2)^(K/2)` times the linear combination of the basis
functions with the coefficients `c`, as a polynomial in t, for `K ≤ 2^(B+1)`, at every t with
`1 + t^2 ≠ 0` (`wordPoly_eval_any`). -/
def wordPoly (B K : ℕ) (c : Fin K → E) : E[X] :=
  ∑ j : Fin K, C (c j) * ((1 + X ^ 2) ^ (K / 2 - deg B j) * bP B j)

/-- For every `K ≤ 2^(B+1)`, even or odd, and `j < K`, the number `deg B j` of basis function `j` is
at most `K / 2`, rounded down. -/
theorem deg_le_half (B K j : ℕ) (hj : j < K) (hB : K ≤ 2 ^ (B + 1)) : deg B j ≤ K / 2 := by
  rw [deg_eq B j (lt_of_lt_of_le hj hB)]
  omega

/-- For every `K ≤ 2^(B+1)`, the polynomial of a codeword has degree at most `2 * (K / 2)`: this is
`K` for even `K` and `K - 1` for odd `K`. -/
theorem wordPoly_natDegree_le_two_mul (B K : ℕ) (hB : K ≤ 2 ^ (B + 1)) (c : Fin K → E) :
    (wordPoly B K c).natDegree ≤ 2 * (K / 2) := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  have hd := deg_le_half B K j j.isLt hB
  refine le_trans (natDegree_C_mul_le _ _) (le_trans natDegree_mul_le ?_)
  have h1 := natDegree_den_pow_le (E := E) (K / 2 - deg B j)
  have h2 := bP_natDegree_le (E := E) B j
  omega

/-- For every `K ≤ 2^(B+1)`, even or odd: at a value `s` of t with `1 + s^2 ≠ 0`, the polynomial of
a codeword has the value `(1 + s^2)^(K/2)` times the linear combination of the basis functions. -/
theorem wordPoly_eval_any (B K : ℕ) (hB : K ≤ 2 ^ (B + 1)) (c : Fin K → E)
    (s : E) (h : 1 + s ^ 2 ≠ 0) :
    (wordPoly B K c).eval s = (1 + s ^ 2) ^ (K / 2) * ∑ j : Fin K, c j * basis B j s := by
  rw [wordPoly, eval_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hd := deg_le_half B K j j.isLt hB
  have hp : (1 + s ^ 2) ^ (K / 2) = (1 + s ^ 2) ^ (K / 2 - deg B j) * (1 + s ^ 2) ^ deg B j := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_one, eval_X]
  rw [bP_eval s h, hp]
  ring

/-! ## 3. When the polynomial of a codeword is 0 -/

/-- The polynomial in s = t^2 that equals `(1 + s)^(2^i) * Xs i` where `1 + s ≠ 0`: substituting X^2
for X in `xq i` gives `xP i` (`xP_expand`). -/
def xq : ℕ → E[X]
  | 0 => 1 - X
  | i + 1 => 2 * xq i ^ 2 - (1 + X) ^ 2 ^ (i + 1)

theorem xP_expand : ∀ i : ℕ, xP (E := E) i = expand E 2 (xq i)
  | 0 => by simp only [xP, xq, map_sub, map_one, expand_X]
  | i + 1 => by
    simp only [xP, xq, map_sub, map_mul, map_pow, map_add, map_one, expand_X, map_ofNat]
    rw [xP_expand i]

theorem xq_eval_ne_zero (h2 : (2 : E) ≠ 0) : ∀ i : ℕ, (xq (E := E) i).eval (-1) ≠ 0
  | 0 => by
    simp only [xq, eval_sub, eval_one, eval_X, sub_neg_eq_add]
    rw [one_add_one_eq_two]
    exact h2
  | i + 1 => by
    have ih := xq_eval_ne_zero h2 i
    simp only [xq, eval_sub, eval_mul, eval_pow, eval_add, eval_one, eval_X,
      eval_ofNat, add_neg_cancel]
    rw [zero_pow (pow_ne_zero _ (by norm_num)), sub_zero]
    exact mul_ne_zero h2 (pow_ne_zero _ ih)

/-- The product of the `xq i` over the `i < B` at which `k` has the binary digit 1. -/
def Qs (B k : ℕ) : E[X] := ∏ i ∈ Finset.range B, if k.testBit i then xq i else 1

theorem Qs_eval_ne_zero (h2 : (2 : E) ≠ 0) (B k : ℕ) : (Qs (E := E) B k).eval (-1) ≠ 0 := by
  rw [Qs, eval_prod, Finset.prod_ne_zero_iff]
  intro i _
  by_cases hb : k.testBit i = true
  · rw [if_pos hb]
    exact xq_eval_ne_zero h2 i
  · rw [if_neg hb, eval_one]
    exact one_ne_zero

theorem bP_even (B k : ℕ) : bP (E := E) B (2 * k) = expand E 2 (Qs B k) := by
  have h0 : (2 * k).testBit 0 = false := by
    rw [Nat.testBit_zero]
    simp
  have h1 : ∀ i, (2 * k).testBit (i + 1) = k.testBit i := fun i => by
    rw [Nat.testBit_succ, Nat.mul_div_cancel_left k (by norm_num)]
  rw [bP, h0, if_neg Bool.false_ne_true, one_mul, Qs, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [h1 i]
  by_cases hb : k.testBit i = true
  · rw [if_pos hb, if_pos hb, xP_expand]
  · rw [if_neg hb, if_neg hb, map_one]

theorem bP_odd (B k : ℕ) : bP (E := E) B (2 * k + 1) = 2 * X * expand E 2 (Qs B k) := by
  have h0 : (2 * k + 1).testBit 0 = true := by
    rw [Nat.testBit_zero]
    simp
  have h1 : ∀ i, (2 * k + 1).testBit (i + 1) = k.testBit i := fun i => by
    have hd : (2 * k + 1) / 2 = k := by omega
    rw [Nat.testBit_succ, hd]
  rw [bP, if_pos h0, yP, Qs, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [h1 i]
  by_cases hb : k.testBit i = true
  · rw [if_pos hb, if_pos hb, xP_expand]
  · rw [if_neg hb, if_neg hb, map_one]

/-- A polynomial u(X^2) + X v(X^2) is 0 only if u and v are 0. -/
theorem split_zero (u v : E[X]) (h : expand E 2 u + X * expand E 2 v = 0) : u = 0 ∧ v = 0 := by
  have hodd : ∀ (w : E[X]) (m : ℕ), (expand E 2 w).coeff (2 * m + 1) = 0 := fun w m => by
    rw [coeff_expand (by norm_num : 0 < 2), if_neg (by omega)]
  constructor
  · ext m
    have hc := congrArg (fun p : E[X] => p.coeff (2 * m)) h
    simp only [coeff_add, coeff_zero] at hc
    rw [coeff_expand_mul' (by norm_num : 0 < 2)] at hc
    rcases m with _ | m
    · rw [Nat.mul_zero, coeff_X_mul_zero, add_zero] at hc
      rw [hc, coeff_zero]
    · have e1 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
      rw [e1, coeff_X_mul, hodd, add_zero] at hc
      rw [hc, coeff_zero]
  · ext m
    have hc := congrArg (fun p : E[X] => p.coeff (2 * m + 1)) h
    simp only [coeff_add, coeff_zero] at hc
    rw [hodd, zero_add, coeff_X_mul, coeff_expand_mul' (by norm_num : 0 < 2)] at hc
    rw [hc, coeff_zero]

/-- A sum of terms that vanish at -1 to different orders. Suppose that each `T r` is 0 whenever it
vanishes at -1. Then a sum of `(1 + X)^r * T r` over `r < S` is 0 only if every `T r` with `r < S`
is 0. -/
theorem seq_zero :
    ∀ (S : ℕ) (T : ℕ → E[X]), (∀ r, (T r).eval (-1) = 0 → T r = 0) →
      ∑ r ∈ Finset.range S, (1 + X) ^ r * T r = 0 → ∀ r, r < S → T r = 0
  | 0, _, _, _ => fun r hr => absurd hr (Nat.not_lt_zero r)
  | S + 1, T, hT, hsum => by
    rw [Finset.sum_range_succ', pow_zero, one_mul] at hsum
    have hfac : ∑ r ∈ Finset.range S, (1 + X : E[X]) ^ (r + 1) * T (r + 1) =
        (1 + X) * ∑ r ∈ Finset.range S, (1 + X) ^ r * T (r + 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by rw [pow_succ']; ring
    rw [hfac] at hsum
    have h0 : T 0 = 0 := by
      refine hT 0 ?_
      have he := congrArg (eval (-1 : E)) hsum
      simp only [eval_add, eval_mul, eval_one, eval_X, add_neg_cancel, zero_mul,
        zero_add, eval_zero] at he
      exact he
    rw [h0, add_zero] at hsum
    have hne : (1 + X : E[X]) ≠ 0 := fun h => by
      have hc := congrArg (fun p : E[X] => p.coeff 1) h
      simp [coeff_one] at hc
    have hrest := (mul_eq_zero.mp hsum).resolve_left hne
    have ih := seq_zero S (fun r => T (r + 1)) (fun r => hT (r + 1)) hrest
    intro r hr
    rcases r with _ | r
    · exact h0
    · exact ih r (Nat.lt_of_succ_lt_succ hr)

/-- In a field in which 2 is non-zero, a sum of `a k * (1 + X)^(N - 1 - k) * Qs B k` over `k < N` is
0 only if every `a k` with `k < N` is 0. -/
theorem coeffs_zero (h2 : (2 : E) ≠ 0) (B N : ℕ) (a : ℕ → E)
    (h : ∑ k ∈ Finset.range N, C (a k) * ((1 + X) ^ (N - 1 - k) * Qs B k) = 0) :
    ∀ k, k < N → a k = 0 := by
  have hre : ∑ r ∈ Finset.range N, (1 + X : E[X]) ^ r * (C (a (N - 1 - r)) * Qs B (N - 1 - r)) =
      0 := by
    rw [← h, ← Finset.sum_range_reflect (fun k => C (a k) * ((1 + X) ^ (N - 1 - k) * Qs B k)) N]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' := Finset.mem_range.mp hr
    have e1 : N - 1 - (N - 1 - r) = r := by omega
    rw [e1]
    ring
  have hT : ∀ r, (C (a (N - 1 - r)) * Qs (E := E) B (N - 1 - r)).eval (-1) = 0 →
      C (a (N - 1 - r)) * Qs (E := E) B (N - 1 - r) = 0 := fun r he => by
    rw [eval_mul, eval_C] at he
    rw [(mul_eq_zero.mp he).resolve_right (Qs_eval_ne_zero h2 B _), C_0, zero_mul]
  have hz := seq_zero N (fun r => C (a (N - 1 - r)) * Qs B (N - 1 - r)) hT hre
  intro k hk
  have hk' := hz (N - 1 - k) (by omega)
  have e1 : N - 1 - (N - 1 - k) = k := by omega
  simp only [e1] at hk'
  have hQ : Qs (E := E) B k ≠ 0 := fun h0 => Qs_eval_ne_zero h2 B k (by rw [h0, eval_zero])
  exact C_eq_zero.mp ((mul_eq_zero.mp hk').resolve_right hQ)

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ N : ℕ, ∑ j ∈ Finset.range (2 * N), f j = ∑ k ∈ Finset.range N, (f (2 * k) + f (2 * k + 1))
  | 0 => by simp
  | N + 1 => by
    have e1 : 2 * (N + 1) = 2 * N + 1 + 1 := by ring
    rw [e1, Finset.sum_range_succ, Finset.sum_range_succ, sum_range_two_mul f N,
      Finset.sum_range_succ, add_assoc]

/-- The polynomial of a codeword, `wordPoly B (2 * N) c`, is 0 only for the message `c = 0`, in a
field in which 2 is non-zero and for `2 * N ≤ 2^(B+1)`. -/
theorem wordPoly_eq_zero (h2 : (2 : E) ≠ 0) (B N : ℕ) (hB : 2 * N ≤ 2 ^ (B + 1))
    (c : Fin (2 * N) → E) (h : wordPoly B (2 * N) c = 0) : c = 0 := by
  let c' : ℕ → E := fun j => if hj : j < 2 * N then c ⟨j, hj⟩ else 0
  have hN : 2 * N / 2 = N := Nat.mul_div_cancel_left N (by norm_num)
  have hw : wordPoly B (2 * N) c =
      ∑ j ∈ Finset.range (2 * N), C (c' j) * ((1 + X ^ 2) ^ (N - deg B j) * bP B j) := by
    rw [wordPoly, hN,
      ← Fin.sum_univ_eq_sum_range
        (fun j => C (c' j) * ((1 + X ^ 2 : E[X]) ^ (N - deg B j) * bP B j)) (2 * N)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hc : c' j = c j := dif_pos j.isLt
    rw [hc]
  have hden : (1 + X ^ 2 : E[X]) = expand E 2 (1 + X) := by rw [map_add, map_one, expand_X]
  have hterm : ∀ k, k < N →
      C (c' (2 * k)) * ((1 + X ^ 2 : E[X]) ^ (N - deg B (2 * k)) * bP B (2 * k)) +
          C (c' (2 * k + 1)) * ((1 + X ^ 2 : E[X]) ^ (N - deg B (2 * k + 1)) * bP B (2 * k + 1)) =
        expand E 2 ((1 + X) * (C (c' (2 * k)) * ((1 + X) ^ (N - 1 - k) * Qs B k))) +
          X *
            expand E 2 (C (2 * c' (2 * k + 1)) * ((1 + X) ^ (N - 1 - k) * Qs B k)) := fun k hk => by
    have d0 : deg B (2 * k) = k := by
      rw [deg_eq B (2 * k) (by omega)]
      omega
    have d1 : deg B (2 * k + 1) = k + 1 := by
      rw [deg_eq B (2 * k + 1) (by omega)]
      omega
    have e0 : N - k = (N - 1 - k) + 1 := by omega
    have e1 : N - (k + 1) = N - 1 - k := by omega
    rw [d0, d1, bP_even, bP_odd, hden, e0, e1]
    simp only [map_mul, map_pow, expand_C, map_ofNat]
    ring
  have h' : ∑ k ∈ Finset.range N,
        (expand E 2 ((1 + X) * (C (c' (2 * k)) * ((1 + X) ^ (N - 1 - k) * Qs B k))) +
          X * expand E 2 (C (2 * c' (2 * k + 1)) * ((1 + X) ^ (N - 1 - k) * Qs B k))) = 0 := by
    rw [← h, hw, sum_range_two_mul]
    exact Finset.sum_congr rfl fun k hk => (hterm k (Finset.mem_range.mp hk)).symm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← map_sum, ← map_sum] at h'
  obtain ⟨hu, hv⟩ := split_zero _ _ h'
  rw [← Finset.mul_sum] at hu
  have hne : (1 + X : E[X]) ≠ 0 := fun h0 => by
    have hc := congrArg (fun p : E[X] => p.coeff 1) h0
    simp [coeff_one] at hc
  have ha := coeffs_zero h2 B N (fun k => c' (2 * k)) ((mul_eq_zero.mp hu).resolve_left hne)
  have hb := coeffs_zero h2 B N (fun k => 2 * c' (2 * k + 1)) hv
  funext j
  have hc : c' j = c j := dif_pos j.isLt
  rw [← hc, Pi.zero_apply]
  rcases Nat.even_or_odd' j.val with ⟨k, hk | hk⟩
  · rw [hk]
    exact ha k (by have := j.isLt; omega)
  · rw [hk]
    exact (mul_eq_zero.mp (hb k (by have := j.isLt; omega))).resolve_left h2

/-- Lengthen a message `c` of `2 * N + 1` symbols by one symbol 0. For `2 * N + 2 ≤ 2^(B+1)`, the
polynomial of the longer message, at `2 * (N + 1)` basis functions, is `1 + X ^ 2` times the
polynomial of `c`. -/
theorem wordPoly_pad (B N : ℕ) (hB : 2 * N + 2 ≤ 2 ^ (B + 1)) (c : Fin (2 * N + 1) → E) :
    wordPoly B (2 * (N + 1)) (fun j => if h : (j : ℕ) < 2 * N + 1 then c ⟨j, h⟩ else 0) =
      (1 + X ^ 2) * wordPoly B (2 * N + 1) c := by
  let c' : ℕ → E := fun j => if h : j < 2 * N + 1 then c ⟨j, h⟩ else 0
  have hN1 : 2 * (N + 1) / 2 = N + 1 := Nat.mul_div_cancel_left _ (by norm_num)
  have hN : (2 * N + 1) / 2 = N := by omega
  have hl : wordPoly B (2 * (N + 1)) (fun j => if h : (j : ℕ) < 2 * N + 1 then c ⟨j, h⟩ else 0) =
      ∑ j ∈ Finset.range (2 * (N + 1)), C (c' j) * ((1 + X ^ 2) ^ (N + 1 - deg B j) * bP B j) := by
    rw [wordPoly, hN1]
    exact Fin.sum_univ_eq_sum_range
      (fun j => C (c' j) * ((1 + X ^ 2 : E[X]) ^ (N + 1 - deg B j) * bP B j)) (2 * (N + 1))
  have hr : wordPoly B (2 * N + 1) c =
      ∑ j ∈ Finset.range (2 * N + 1), C (c' j) * ((1 + X ^ 2) ^ (N - deg B j) * bP B j) := by
    rw [wordPoly, hN,
      ← Fin.sum_univ_eq_sum_range
        (fun j => C (c' j) * ((1 + X ^ 2 : E[X]) ^ (N - deg B j) * bP B j)) (2 * N + 1)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hc : c' j = c j := dif_pos j.isLt
    rw [hc]
  have e1 : 2 * (N + 1) = 2 * N + 1 + 1 := by ring
  have hlast : c' (2 * N + 1) = 0 := dif_neg (lt_irrefl _)
  rw [hl, hr, e1, Finset.sum_range_succ, hlast, C_0, zero_mul, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hd := deg_le_half B (2 * N + 1) j (Finset.mem_range.mp hj) (by omega)
  have e2 : N + 1 - deg B j = (N - deg B j) + 1 := by omega
  rw [e2, pow_succ]
  ring

/-- The polynomial of a codeword with an odd number of basis functions, `wordPoly B (2 * N + 1) c`,
is 0 only for the message `c = 0`, in a field in which 2 is non-zero and for `2 * N + 2 ≤
2^(B+1)`. -/
theorem wordPoly_eq_zero_odd (h2 : (2 : E) ≠ 0) (B N : ℕ) (hB : 2 * N + 2 ≤ 2 ^ (B + 1))
    (c : Fin (2 * N + 1) → E) (h : wordPoly B (2 * N + 1) c = 0) : c = 0 := by
  have hp := wordPoly_pad B N hB c
  rw [h, mul_zero] at hp
  have hz := wordPoly_eq_zero h2 B (N + 1) (by omega) _ hp
  funext j
  have hj : (if h : (j : ℕ) < 2 * N + 1 then c ⟨j, h⟩ else 0) = 0 :=
    congrFun hz ⟨j, by have := j.isLt; omega⟩
  rw [dif_pos j.isLt] at hj
  exact hj

end Code.Circle
