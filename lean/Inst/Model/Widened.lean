-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Widened.lean: the widened cell rule.

A value is written in cells, its digits to the base 256. With signed bytes, in [-128, 127], two
cells reach 32,639 and five reach 547,599,908,735 (the bounds in `Fit2` and `Fit3` of
Inst/Model/Program.lean), while the program admits quotients up to 32,767 and stream values below
2^39. So under that rule a prompt on which the program runs need not fit, and completeness could be
stated only for a smaller relation than binding (R_inf).
The widened rule: the digits are balanced low bytes, and the top cell may be 128 as well. So honest
cells have absolute value at most 128.
The bound on the window event of a range proof (`Prob.pr_win_le`, Prob/Window.lean) asks no more of
honest cells than that.
    `cellW`, `Writable`     the rule, and "the rule is defined"
    `sum_cellW`, `writable_of_abs_le`, `writable_iff`, `cellW_unique`
                            for 1 ≤ n: the cells give the value; where the rule is defined; unique
                            digits
Limits: it does not define (Fit2), (Fit3) or Fit for the widened rule, and it does not prove that
every prompt on which the program runs fits, nor completeness on R_inf.
Also: the rule is widened here for every array.
-/
import Inst.Model.Program
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

namespace Inst.Model

/-! ## The rule -/

/-- what is left of a above its l lowest balanced bytes -/
def rest (a : ℤ) : ℕ → ℤ
  | 0 => a
  | l + 1 => (rest a l - lowByte (rest a l)) / 256

/-- The widened cell rule: cell l of the value a in an array of n cells: balanced low bytes, and the
rest in the top cell. -/
def cellW (n : ℕ) (a : ℤ) (l : ℕ) : ℤ := if l + 1 < n then lowByte (rest a l) else rest a l

/-- The rule is defined at a: every cell has absolute value at most 128. -/
def Writable (n : ℕ) (a : ℤ) : Prop := ∀ l < n, |cellW n a l| ≤ 128

theorem lowByte_range (a : ℤ) : -128 ≤ lowByte a ∧ lowByte a ≤ 127 := by
  unfold lowByte
  have h1 := Int.emod_nonneg (a + 128) (by norm_num : (256 : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos (a + 128) (by norm_num : (0 : ℤ) < 256)
  constructor <;> linarith

theorem rest_succ (a : ℤ) (l : ℕ) : rest a l = lowByte (rest a l) + 256 * rest a (l + 1) := by
  have hd : (256 : ℤ) ∣ rest a l - lowByte (rest a l) := by
    unfold lowByte
    have h := Int.emod_add_mul_ediv (rest a l + 128) 256
    exact ⟨(rest a l + 128) / 256, by linarith⟩
  show rest a l = lowByte (rest a l) + 256 * ((rest a l - lowByte (rest a l)) / 256)
  rw [Int.mul_ediv_cancel' hd]
  ring

theorem sum_low_add_rest (a : ℤ) :
    ∀ k : ℕ, ∑ l ∈ Finset.range k, 256 ^ l * lowByte (rest a l) + 256 ^ k * rest a k = a
  | 0 => by simp [rest]
  | k + 1 => by
    have ih := sum_low_add_rest a k
    rw [Finset.sum_range_succ]
    rw [rest_succ a k] at ih
    rw [pow_succ]
    linarith

/-- For 1 ≤ n the cells, read to the base 256, give the value. -/
theorem sum_cellW {n : ℕ} (hn : 1 ≤ n) (a : ℤ) :
    ∑ l ∈ Finset.range n, 256 ^ l * cellW n a l = a := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ]
  have h1 : ∑ l ∈ Finset.range k, 256 ^ l * cellW (k + 1) a l =
      ∑ l ∈ Finset.range k, 256 ^ l * lowByte (rest a l) :=
    Finset.sum_congr rfl fun l hl => by
      have : l + 1 < k + 1 := by have := Finset.mem_range.mp hl; omega
      rw [cellW, if_pos this]
  have h2 : cellW (k + 1) a k = rest a k := by rw [cellW, if_neg (lt_irrefl _)]
  rw [h1, h2]
  exact sum_low_add_rest a k

theorem abs_rest_le (a : ℤ) : ∀ k : ℕ, |a| ≤ 128 * 256 ^ k → |rest a k| ≤ 128
  | 0, h => by simpa [rest] using h
  | k + 1, h => by
    -- one byte down: |rest a 1| ≤ 128 · 256^k, and rest (rest a 1) k = rest a (k + 1)
    have hshift : ∀ (b : ℤ) (j : ℕ), rest (rest b 1) j = rest b (j + 1) := by
      intro b j
      induction j with
      | zero => rfl
      | succ j ih => show (rest (rest b 1) j - lowByte (rest (rest b 1) j)) / 256 = _; rw [ih]; rfl
    have h0 := rest_succ a 0
    have hb := lowByte_range (rest a 0)
    have ha : rest a 0 = a := rfl
    rw [ha] at h0 hb
    have hp : (0 : ℤ) < 256 ^ k := by positivity
    rw [pow_succ] at h
    obtain ⟨hl, hu⟩ := abs_le.mp h
    have h1 : |rest a 1| ≤ 128 * 256 ^ k := by
      rw [abs_le]
      constructor
      · by_contra hc
        have : rest a 1 + 1 ≤ -(128 * 256 ^ k) := by linarith [not_le.mp hc]
        nlinarith
      · by_contra hc
        have : 128 * 256 ^ k + 1 ≤ rest a 1 := by linarith [not_le.mp hc]
        nlinarith
    rw [← hshift a k]
    exact abs_rest_le (rest a 1) k h1

/-- The rule with n cells is defined at every value of absolute value at most 128 · 256^(n-1). -/
theorem writable_of_abs_le {n : ℕ} (a : ℤ) (h : |a| ≤ 128 * 256 ^ (n - 1)) : Writable n a := by
  intro l hl
  unfold cellW
  by_cases h1 : l + 1 < n
  · rw [if_pos h1]
    have := lowByte_range (rest a l)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [if_neg h1]
    have : l = n - 1 := by omega
    rw [this]
    exact abs_rest_le a (n - 1) h

/-! ## The exact interval, uniqueness -/

/-- u_n = (256^n - 1) / 255 = ∑_(l<n) 256^l -/
def un (n : ℕ) : ℤ := ∑ l ∈ Finset.range n, 256 ^ l

theorem un_succ (n : ℕ) : un (n + 1) = un n + 256 ^ n := Finset.sum_range_succ _ _

theorem un_mul (n : ℕ) : 255 * un n = 256 ^ n - 1 := by
  induction n with
  | zero => simp [un]
  | succ n ih => rw [un_succ, pow_succ]; linarith

theorem sum_low_bounds (a : ℤ) (k : ℕ) :
    -128 * un k ≤ ∑ l ∈ Finset.range k, 256 ^ l * lowByte (rest a l) ∧
    ∑ l ∈ Finset.range k, 256 ^ l * lowByte (rest a l) ≤ 127 * un k := by
  unfold un
  rw [Finset.mul_sum, Finset.mul_sum]
  constructor
  · refine Finset.sum_le_sum fun l _ => ?_
    have hp : (0 : ℤ) < 256 ^ l := by positivity
    nlinarith [(lowByte_range (rest a l)).1]
  · refine Finset.sum_le_sum fun l _ => ?_
    have hp : (0 : ℤ) < 256 ^ l := by positivity
    nlinarith [(lowByte_range (rest a l)).2]

/-- What is left above the k lowest bytes is in [lo, hi] exactly if the value is in the interval
that k balanced bytes and such a rest reach. -/
theorem rest_mem_iff (a : ℤ) (k : ℕ) (lo hi : ℤ) :
    (lo ≤ rest a k ∧ rest a k ≤ hi) ↔
    (256 ^ k * lo - 128 * un k ≤ a ∧ a ≤ 256 ^ k * hi + 127 * un k) := by
  have hs := sum_low_add_rest a k
  obtain ⟨h1, h2⟩ := sum_low_bounds a k
  have hu := un_mul k
  have hp : (0 : ℤ) < 256 ^ k := by positivity
  constructor
  · rintro ⟨hl, hh⟩
    constructor <;> nlinarith
  · rintro ⟨hl, hh⟩
    constructor
    · by_contra hc
      have h3 : rest a k + 1 ≤ lo := by linarith [not_le.mp hc]
      nlinarith
    · by_contra hc
      have h3 : hi + 1 ≤ rest a k := by linarith [not_le.mp hc]
      nlinarith

theorem cellW_top {n : ℕ} (hn : 1 ≤ n) (a : ℤ) : cellW n a (n - 1) = rest a (n - 1) := by
  rw [cellW, if_neg (by omega)]

/-- The exact interval of the widened rule, for 1 ≤ n: `Writable n a` exactly if -128 u_n ≤ a ≤
127 u_(n-1) + 128 · 256^(n-1). -/
theorem writable_iff {n : ℕ} (hn : 1 ≤ n) (a : ℤ) :
    Writable n a ↔ (-128 * un n ≤ a ∧ a ≤ 127 * un (n - 1) + 128 * 256 ^ (n - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hr := rest_mem_iff a k (-128) 128
  rw [Nat.add_sub_cancel, un_succ]
  constructor
  · intro h
    have h1 := abs_le.mp (h k (Nat.lt_succ_self k))
    rw [show cellW (k + 1) a k = rest a k from cellW_top (Nat.succ_le_succ (Nat.zero_le k)) a] at h1
    obtain ⟨h2, h3⟩ := hr.mp h1
    constructor <;> linarith
  · rintro ⟨h2, h3⟩
    have h1 := hr.mpr ⟨by linarith, by linarith⟩
    intro l hl
    unfold cellW
    by_cases hlt : l + 1 < k + 1
    · rw [if_pos hlt]
      have := lowByte_range (rest a l)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [if_neg hlt]
      have : l = k := by omega
      rw [this]
      exact abs_le.mpr h1


theorem rest_shift (b : ℤ) : ∀ j : ℕ, rest (rest b 1) j = rest b (j + 1)
  | 0 => rfl
  | j + 1 => by
    show (rest (rest b 1) j - lowByte (rest (rest b 1) j)) / 256 = _
    rw [rest_shift b j]
    rfl

/-- The balanced low byte of a is the only number of [-128, 127] that is congruent to a modulo
256. -/
theorem lowByte_unique {a b : ℤ} (h1 : -128 ≤ b) (h2 : b ≤ 127) (hd : (256 : ℤ) ∣ a - b) :
    lowByte a = b := by
  obtain ⟨q, hq⟩ := hd
  have hr := lowByte_range a
  have h0 := rest_succ a 0
  have ha : rest a 0 = a := rfl
  rw [ha] at h0
  -- lowByte a - b = 256 (q - rest a 1), and it is in (-256, 256)
  have h3 : lowByte a - b = 256 * (q - rest a 1) := by linarith
  have h4 : q - rest a 1 = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : q - rest a 1 ≤ -1 := by linarith [Int.lt_iff_add_one_le.mp h]
      linarith [hr.1]
    · have : 1 ≤ q - rest a 1 := Int.lt_iff_add_one_le.mp h
      linarith [hr.2]
  rw [h4] at h3
  linarith

/-- The digits are unique: for 1 ≤ n, integers c_0, .., c_(n-1) whose value to the base 256 is a,
all but the top one in [-128, 127], are the cells of the rule. -/
theorem cellW_unique :
    ∀ {n : ℕ}, 1 ≤ n →
      ∀ (a : ℤ) (c : ℕ → ℤ), (∀ l, l + 1 < n → -128 ≤ c l ∧ c l ≤ 127) →
        ∑ l ∈ Finset.range n, 256 ^ l * c l = a → ∀ l < n, c l = cellW n a l
  | 0, h, _, _, _, _ => absurd h (by norm_num)
  | 1, _, a, c, _, hs => by
    intro l hl
    have : l = 0 := by omega
    subst this
    simp at hs
    rw [cellW, if_neg (by norm_num)]
    exact hs
  | n + 2, _, a, c, hc, hs => by
    rw [Finset.sum_range_succ'] at hs
    have hfac : ∑ l ∈ Finset.range (n + 1), 256 ^ (l + 1) * c (l + 1) =
        256 * ∑ l ∈ Finset.range (n + 1), 256 ^ l * c (l + 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [pow_succ]; ring
    rw [hfac] at hs
    simp only [pow_zero, one_mul] at hs
    have h0 : lowByte a = c 0 := lowByte_unique (hc 0 (by omega)).1 (hc 0 (by omega)).2
      ⟨∑ l ∈ Finset.range (n + 1), 256 ^ l * c (l + 1), by linarith⟩
    have h1 : rest a 1 = ∑ l ∈ Finset.range (n + 1), 256 ^ l * c (l + 1) := by
      have h2 := rest_succ a 0
      have ha : rest a 0 = a := rfl
      rw [ha, h0] at h2
      linarith
    have ih := cellW_unique (n := n + 1) (by omega) (rest a 1) (fun l => c (l + 1))
      (fun l hl => hc (l + 1) (by omega)) h1.symm
    intro l hl
    cases l with
    | zero =>
      rw [cellW, if_pos (by omega)]
      exact h0.symm
    | succ l =>
      have ihl : c (l + 1) = cellW (n + 1) (rest a 1) l := ih l (by omega)
      rw [ihl]
      unfold cellW
      by_cases hlt : l + 1 < n + 1
      · rw [if_pos hlt, if_pos (by omega), rest_shift]
      · rw [if_neg hlt, if_neg (by omega), rest_shift]

theorem writable_two_of_fits16 {a : ℤ} (h : Fits16 a) : Writable 2 a :=
  writable_of_abs_le a
    (abs_le.mpr
      ⟨by have := h.1; norm_num at this ⊢; linarith, by have := h.2; norm_num at this ⊢; linarith⟩)

/-! ## What test (N1) gives for the widened rule -/

section Program
variable (P : Params) (tb : Tables) (i : Weights) (prompt : Fin P.T → Fin P.V)


variable {P tb i prompt}

/-- For 1 ≤ ϵ test (N1) bounds every entry of the stream: x[j]² ≤ V < 2^78, so |x[j]| ≤ 128 · 256^4.
-/
theorem abs_le_of_normOK {np : NormPar} {d : ℕ} {x : Vec} (heps : 1 ≤ np.eps)
    (h : NORM.OK np d x) {j : ℕ} (hj : j < d) :
    |x j| ≤ 128 * 256 ^ (5 - 1) := by
  have h1 : x j ^ 2 ≤ NORM.V d x :=
    Finset.single_le_sum (f := fun j => x j ^ 2)
      (fun k _ => sq_nonneg (x k)) (Finset.mem_range.mpr hj)
  have h2 : x j ^ 2 < 2 ^ 78 := by linarith [h.1]
  by_contra hc
  have h3 : (128 * 256 ^ (5 - 1) : ℤ) < |x j| := not_le.mp hc
  have h4 : |x j| ^ 2 = x j ^ 2 := sq_abs (x j)
  norm_num at h3
  nlinarith [abs_nonneg (x j)]


end Program


end Inst.Model
