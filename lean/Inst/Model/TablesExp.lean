-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/TablesExp.lean: the numbers of the exponential's lookup table as functions of the shift
sh and of the number u0 of rows in use: what the proofs use of them.

Inst/Model/Tables.lean defines C = 2^sh u0 (`cutC`), st = 2^16 − 2^sh (`stp`), nd = ⌊4 S_max / st⌋ +
1 and the valid pairs (`ExpOK`). Here, for a valid pair:
    `un_bounds`      16 ≤ 2^sh ≤ 4,096
    `stp_bounds`     61,440 ≤ st ≤ 65,520
    `nd_spec`        st (nd − 1) ≤ 4 S_max < st nd: nd is ⌈(4 S_max + 1)/st⌉
    `nd_pos`         0 < nd
    `cutC_bounds`    0 < C ≤ 2^24 − 2^16
    `expOK_ref`, `cutC_ref`, `stp_ref`, `nd_ref`
        the reference pair (8; 2,307) is valid; the numbers at it
    `expOK_5`
        another pair is valid (sh = 5 with 1,000 rows in use: these two numbers are synthetic,
        fitted to nothing)
-/
import Inst.Model.Tables
import Mathlib.Tactic

set_option autoImplicit false

namespace Inst.Model

variable {sh u0 : ℕ}

theorem un_bounds (h : ExpOK sh u0) : (16 : ℤ) ≤ 2 ^ sh ∧ (2 : ℤ) ^ sh ≤ 4096 :=
  ⟨by calc (16 : ℤ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ sh := pow_le_pow_right₀ (by norm_num) h.lo,
   by calc (2 : ℤ) ^ sh ≤ 2 ^ 12 := pow_le_pow_right₀ (by norm_num) h.hi
        _ = 4096 := by norm_num⟩

theorem stp_bounds (h : ExpOK sh u0) : 61440 ≤ stp sh ∧ stp sh ≤ 65520 := by
  obtain ⟨a, b⟩ := un_bounds h
  unfold stp
  constructor <;> omega

theorem nd_pos (sh : ℕ) : 0 < nd sh := Nat.succ_pos _

/-- For a valid pair: nd = ⌈(4 S_max + 1)/st⌉. -/
theorem nd_spec (h : ExpOK sh u0) :
    stp sh * ((nd sh : ℤ) - 1) ≤ 4 * Smax ∧ 4 * Smax < stp sh * (nd sh : ℤ) := by
  have hs : 0 < stp sh := lt_of_lt_of_le (by norm_num) (stp_bounds h).1
  have hS : (0 : ℤ) ≤ 4 * Smax := by norm_num [Smax]
  have hq : 0 ≤ 4 * Smax / stp sh := Int.ediv_nonneg hS hs.le
  have hn : (nd sh : ℤ) = 4 * Smax / stp sh + 1 := by
    unfold nd
    push_cast
    rw [Int.toNat_of_nonneg hq]
  rw [hn]
  constructor
  · have := Int.mul_ediv_self_le (x := 4 * Smax) (k := stp sh) hs.ne'
    linarith
  · have := Int.lt_mul_ediv_self_add (x := 4 * Smax) hs
    linarith

theorem cutC_bounds (h : ExpOK sh u0) : 0 < cutC sh u0 ∧ cutC sh u0 ≤ 2 ^ 24 - 2 ^ 16 := by
  refine ⟨?_, by have := h.cut; omega⟩
  unfold cutC
  have := h.pos
  positivity

/-- For a valid pair there is a row in use: the cut-off C is at least 2^sh. -/
theorem un_le_cutC (h : ExpOK sh u0) : (2 : ℤ) ^ sh ≤ cutC sh u0 := by
  unfold cutC
  have h1 : (1 : ℤ) ≤ u0 := by exact_mod_cast h.pos
  have h2 : (0 : ℤ) < 2 ^ sh := by positivity
  nlinarith

theorem expOK_ref : ExpOK 8 2307 := by decide +kernel
theorem cutC_ref : cutC 8 2307 = 590592 := by norm_num [cutC]
theorem stp_ref : stp 8 = 65280 := by norm_num [stp]
theorem nd_ref : nd 8 = 32865 := by decide +kernel

/-- the conditions have another instance than the reference pair. The numbers 5 and 1,000 are made
up -/
theorem expOK_5 : ExpOK 5 1000 := by decide +kernel

end Inst.Model
