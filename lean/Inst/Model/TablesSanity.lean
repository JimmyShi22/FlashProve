-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/TablesSanity.lean: checks of Inst/Model/Tables.lean. Theorems only.
  the constants and padding values of the lookup tables; (Tab9) for `EX`; the rounding `rnd` at
  sample points.

Notation: (in the words of the comments of Inst/Model/Tables.lean)
  `FC`, `FL tb`, `FS tb`, `tau1 sh` (τ1), `tau2 sh u0 tb` (τ2), `tau4` (τ4), `FE`: of type `Lut`: a
      table: its number of rows, the entry τ(ι) of each row, and its padding value; among the
      look-up tables of the main look-up arguments; FC: (clamp); FL: (SiLU); FS: (sigmoid; clamp of
      the gate); FE: the table through which `EX` is looked up
  `exG`: a function ℕ → ℕ: `exG u` is G_u (its recurrence: Part 2 there)
  `EX`: a function ℕ → ℤ: a sixth table function, by its recurrence: EX[u] = ⌈G_u / 2^17⌉
-/
import Inst.Model.Tables
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

namespace Inst.Model.TablesSanity
open Inst.Model

theorem smax_eq : Smax = 536346752 := by norm_num [Smax]
theorem cutC_eq : cutC 8 2307 = 590592 := by norm_num [cutC]
theorem stp_eq : stp 8 = 65280 := by norm_num [stp]
theorem nd_val : nd 8 = 32865 := by decide +kernel
/-- at sh = 8: nd = ⌈(4 S_max + 1)/st⌉ -/
theorem nd_eq : ((nd 8 : ℕ) : ℤ) = (4 * Smax + 1 + (stp 8 - 1)) / stp 8 := by
  rw [nd_val]; norm_num [Smax, stp]
theorem live_dead : 2307 + nd 8 = 35172 := by rw [nd_val]

/-- the padding value of FC, FL, FS, τ1, τ2, τ4, FE (this theorem and the six below) is the entry at
a named row; for τ2 at u0, a row of the table if u0 < 2^16 (what the tables are: the comment at the
top of this file) -/
theorem fc_pad : FC.row (2 ^ 15) = FC.pad := by norm_num [FC, clamp]
theorem fl_pad (tb : Tables) : (FL tb).row (2 ^ 15) = (FL tb).pad := by simp [FL]
theorem fs_pad (tb : Tables) : (FS tb).row (2 ^ 15) = (FS tb).pad := by simp [FS]
theorem tau1_pad (sh : ℕ) : (tau1 sh).row 0 = (tau1 sh).pad := by simp [tau1]
theorem tau2_pad (sh u0 : ℕ) (tb : Tables) : (tau2 sh u0 tb).row u0 = (tau2 sh u0 tb).pad := by
  simp [tau2, nd]
theorem tau4_pad : tau4.row 0 = tau4.pad := by norm_num [tau4]
theorem fe_pad : FE.row 0 = FE.pad := by norm_num [FE, EX, exG]

/-! (Tab9): "EX[0] = 2^24 and 1 ≤ EX[u] ≤ 2^24 for all u" -/
theorem exG_bounds : ∀ u, 1 ≤ exG u ∧ exG u ≤ 2 ^ 41
  | 0 => by norm_num [exG]
  | u + 1 => by
      obtain ⟨h1, h2⟩ := exG_bounds u
      simp only [exG]
      constructor
      · apply (Nat.le_div_iff_mul_le (by norm_num)).2
        omega
      · apply Nat.div_le_of_le_mul
        omega

theorem tab9 : EX 0 = 2 ^ 24 ∧ ∀ u, 1 ≤ EX u ∧ EX u ≤ 2 ^ 24 := by
  refine ⟨by norm_num [EX, exG], fun u => ?_⟩
  obtain ⟨h1, h2⟩ := exG_bounds u
  simp only [EX]
  constructor
  · have : 1 ≤ (exG u + (2 ^ 17 - 1)) / 2 ^ 17 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
    exact_mod_cast this
  · have h3 : (exG u + (2 ^ 17 - 1)) / 2 ^ 17 < 2 ^ 24 + 1 :=
      (Nat.div_lt_iff_lt_mul (by norm_num)).2 (by omega)
    have : (exG u + (2 ^ 17 - 1)) / 2 ^ 17 ≤ 2 ^ 24 := by omega
    exact_mod_cast this

/-! the roundings at sample points -/
theorem rnd_half : rnd (1 / 2) = 1 ∧ rnd (-(1 / 2)) = -1 ∧ rnd (5 / 4) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [rnd]; norm_num
  · simp only [rnd]; norm_num
  · simp only [rnd]
    rw [if_pos (by norm_num)]
    rw [Int.floor_eq_iff]
    norm_num


end Inst.Model.TablesSanity
