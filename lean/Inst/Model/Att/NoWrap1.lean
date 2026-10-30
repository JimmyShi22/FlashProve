-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/Att/NoWrap1.lean: no wrap-around in an attention segment, first half: what does not
  read the modulus: bits, the index of the greatest score (`jst`), the bounds on a score and on mx
  (`mxV`).

  No wrap-around: a congruence modulo p between integers whose difference is below p in absolute
  value is an equality (`NW.eq_of_dvd`, Inst/Model/Att/NoWrap0.lean). Regions and their entries: the
  head of Inst/Model/Att/Index.lean; the cells and their values: Inst/Model/Att/Trace.lean.
  All statements are over the integers.
  Part 1: bits (a number from its bits; for bits and j < 2^n, the product of the eq1 is the
  indicator of equality).
  Part 2 holds what does not read the modulus: `jst_def` (no hypothesis), `step_fa5` (under hch,
  hin) and `Half1.mx_abs` (under `Half1`). The steps that read it are in
  Inst/Model/Bound/Att1.lean, for a number p with `Big p`, under `IntRel`
  (Inst/Model/Att/NoWrap0.lean) and, where stated, D.lT ≤ 10, D.ch ≤ 128 and `InB`.
  Labels such as (FA5) and Step A3 link docstrings, here and in Inst/Model/Bound/Att1.lean.

  Notation, for this file and for Inst/Model/Bound/Att1.lean, whose head points here:
    `rm` (Inst/Model/Att/Trace.lean): an integer: the remainder rm = r0 + 256 r1;
    `flV` (Inst/Model/Att/Trace.lean): an integer: the flag: cell number 2, fl, of an entry of a
      region (`Raw.c`);
    `qhV`, `qhV'` (Inst/Model/Att/Trace.lean): integers: the cells qh, qh', each plus 128
      (`step_fa2`'s docstring, Inst/Model/Bound/Att1.lean: "the two bytes of the division");
    `scV` (Inst/Model/Att/Trace.lean): an integer: sc_b[g, i, j] = ∑_n qry_b[g, i, n] key_λ[g, j,
      n];
    `mxV` (Inst/Model/Att/Trace.lean): an integer: mx: the value ∑_k 256^k c_k of the four cells mx;
    `sel` (Inst/Model/Att/Trace.lean): an integer: sel_b[g, i, n] = ∑_j key_λ[g, j, n] ∏_k
      eq1(ib_(b,k)[g, i], bit_k(j));
    `eq1` (Inst/Model/Att/Trace.lean): an integer: eq1(u, y) = u y + (1 - u)(1 - y);
    `Smax` (Inst/Model/Tables.lean): an integer: see its definition;
    `D.lT` (Inst/Model/Att/Index.lean): a natural number: bits of a position;
    b, g, i, j, n (Inst/Model/Att/Index.lean), in Part 2: natural numbers: pairs b = na λ + a of a
      layer λ of the segment and the number a of a query head among those of its key/value head
      (`Dim.nb`); key/value heads g (`Dim.nG`); positions i, j (`Dim.T`); channels n (`Dim.ch`).
-/
import Inst.Model.Att.NoWrap0

set_option autoImplicit false

namespace Inst.Model.AttSeg

open Finset

/-! ## Part 1. Bits -/

namespace Bits

/-- the number with the bits u 0, .., u (n - 1) -/
def num (u : ℕ → ℤ) (n : ℕ) : ℕ := ∑ k ∈ range n, 2 ^ k * (u k).toNat

variable {u : ℕ → ℤ}

theorem num_succ (u : ℕ → ℤ) (n : ℕ) : num u (n + 1) = 2 ^ n * (u n).toNat + num u n := by
  unfold num
  rw [sum_range_succ, Nat.add_comm]

theorem toNat_le_one {a : ℤ} (h : a = 0 ∨ a = 1) : a.toNat ≤ 1 := by
  rcases h with rfl | rfl <;> simp

theorem num_lt : ∀ n : ℕ, (∀ k < n, u k = 0 ∨ u k = 1) → num u n < 2 ^ n
  | 0, _ => by simp [num]
  | n + 1, h => by
    have h1 := num_lt n fun k hk => h k (Nat.lt_succ_of_lt hk)
    have h2 := toNat_le_one (h n (Nat.lt_succ_self n))
    rw [num_succ, pow_succ]
    nlinarith [Nat.two_pow_pos n]

theorem cast_num :
    ∀ n : ℕ, (∀ k < n, u k = 0 ∨ u k = 1) → ((num u n : ℕ) : ℤ) = ∑ k ∈ range n, 2 ^ k * u k
  | 0, _ => by simp [num]
  | n + 1, h => by
    have h1 := cast_num n fun k hk => h k (Nat.lt_succ_of_lt hk)
    have h2 : (((u n).toNat : ℕ) : ℤ) = u n := by
      rcases h n (Nat.lt_succ_self n) with h0 | h0 <;> rw [h0] <;> rfl
    rw [num_succ, sum_range_succ, ← h1]
    push_cast
    rw [h2]
    ring

theorem testBit_num :
    ∀ n : ℕ, (∀ k < n, u k = 0 ∨ u k = 1) → ∀ k < n, (num u n).testBit k = decide (u k = 1)
  | n + 1, h, k, hk => by
    have hn := num_lt n fun k hk => h k (Nat.lt_succ_of_lt hk)
    rw [num_succ, Nat.testBit_two_pow_mul_add _ hn]
    by_cases hkn : k < n
    · rw [if_pos hkn]
      exact testBit_num n (fun k hk => h k (Nat.lt_succ_of_lt hk)) k hkn
    · obtain rfl : k = n := by omega
      rw [if_neg hkn, Nat.sub_self]
      rcases h k hk with h0 | h0 <;> rw [h0] <;> simp

/-- eq1 on bits is the indicator of equality. -/
theorem eq1_bit {a : ℤ} (h : a = 0 ∨ a = 1) (k j : ℕ) :
    eq1 a (bitR ℤ k j) = if j.testBit k = decide (a = 1) then 1 else 0 := by
  unfold eq1 bitR
  rcases h with rfl | rfl <;> by_cases hb : j.testBit k = true <;> simp [hb]

/-- For u k in {0, 1} (h) and j < 2^n (hj): the product of the eq1 over all bits is the indicator of
j = the number with these bits. -/
theorem prod_eq1 (n : ℕ) (h : ∀ k < n, u k = 0 ∨ u k = 1) {j : ℕ} (hj : j < 2 ^ n) :
    (∏ k ∈ range n, eq1 (u k) (bitR ℤ k j)) = if j = num u n then 1 else 0 := by
  by_cases he : j = num u n
  · rw [if_pos he]
    refine prod_eq_one fun k hk => ?_
    rw [eq1_bit (h k (mem_range.mp hk)), if_pos]
    rw [he]
    exact testBit_num n h k (mem_range.mp hk)
  · rw [if_neg he]
    have : ∃ k < n, j.testBit k ≠ (num u n).testBit k := by
      by_contra hc
      refine he (Nat.eq_of_testBit_eq fun k => ?_)
      by_cases hk : k < n
      · exact by_contra fun hne => hc ⟨k, hk, hne⟩
      · rw [Nat.testBit_lt_two_pow
              (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hk))),
          Nat.testBit_lt_two_pow
            (lt_of_lt_of_le (num_lt n h)
              (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hk)))]
    obtain ⟨k, hk, hne⟩ := this
    refine prod_eq_zero (mem_range.mpr hk) ?_
    rw [eq1_bit (h k hk), if_neg]
    rw [← testBit_num n h k hk]
    exact hne

end Bits

/-! ## Part 2. What does not read the modulus: Step A3, and the second half of (FA6) -/

section Steps
variable [scl : Scl]
variable {D : Dim} {t : Raw → ℤ}

/-- j*: the number whose bits are the cells of the index -/
def jst (D : Dim) (t : Raw → ℤ) (b g i : ℕ) : ℕ := Bits.num (fun k => ibV t k b g i) D.lT

omit [scl : Scl] in
theorem jst_def (b g i : ℕ) : jst D t b g i = Bits.num (fun k => ibV t k b g i) D.lT := rfl

omit [scl : Scl] in
/-- Step A3, (FA5): under hch, hin and for indices in range (hg, hi, hj), a score is at most S_max
in absolute value. -/
theorem step_fa5 (hch : D.ch ≤ 128) {b : ℕ} (hin : InB D t b) {g i j : ℕ} (hg : g < D.nG)
    (hi : i < D.T) (hj : j < D.T) : |scV D t b g i j| ≤ Smax := by
  unfold scV
  calc |∑ n ∈ range D.ch, qryV t b g i n * keyV t (D.lamOf b) g j n| ≤ ∑ n ∈ range D.ch, |qryV t b g i n * keyV t (D.lamOf b) g j n| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ range D.ch, (2047 * 2047 : ℤ) := sum_le_sum fun n hn => by
        rw [abs_mul]
        exact mul_le_mul (hin.1 g hg i hi n (mem_range.mp hn))
          (hin.2 g hg j hj n (mem_range.mp hn)).1 (abs_nonneg _) (by norm_num)
    _ = D.ch * (2047 * 2047) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ Smax := by
        have : (D.ch : ℤ) ≤ 128 := by exact_mod_cast hch
        unfold Smax
        nlinarith

end Steps

/-- (FA6), second half: under `Half1` (h), for g, i in range, mx (`mxV`) is at most S_max in
absolute value. -/
theorem Half1.mx_abs [scl : Scl] {D : Dim} {t : Raw → ℤ} {b : ℕ} (h : Half1 D t b) {g i : ℕ}
    (hg : g < D.nG) (hi : i < D.T) : |mxV t b g i| ≤ Smax := by
  obtain ⟨js, hjs, he⟩ := h.fa6 g i hg hi
  rw [he]
  exact h.fa5 g i js hg hi (lt_of_le_of_lt hjs hi)

end Inst.Model.AttSeg
