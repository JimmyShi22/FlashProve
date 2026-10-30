-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/ParBounds.lean: what the bounds below come to at
the reference parameters, as far as that can be said without the shapes of the protocols: in
numerals, as functions of a few counts.

The bound on binding (Compile/Batch/SpecBinding.lean): epsB W M tC tP = (t + tV + 1) · εs + 2 (t +
tV + 2)² / 2^λ, with t = tC + tP the queries of committer and prover, tV = tVB W the queries of the
verifier on one proof, εs the field `εs` of M.

Hypotheses of the lemmas on ε (`epsB_le_frac`, `epsB_ratio`, `epsB_at_64`), to be discharged at the
instance (this file shows them of no W and M): λ = 256; tVB W ≤ tv; M.εs ≤ kap · 2^-132, where
2^-132 = `Cb.Par.epsS` and kap = 1 + 2^-80 stands for the samplers' bias over the blocks of one
round (it bears 2^34 blocks in a round at 1 + 2^-115 a block; its proof is not part of this
library).
These errors are numbers: εs is one that `M` lists (the data field `LH.Nums.εs`, Iop/InteractiveOracleProof.lean):
that an interface is sound at the number that is listed for it is no statement of this file; that
tie is `BatchProtocol.PropsNoAccK.soundK` (Hiop/GrindK.lean), a hypothesis.

  `epsB_le_frac`: ε ≤ epsNum tv t / 2^256 ("the formula" below), epsNum tv t = (t + tv + 1) (2^80 +
    1) 2^44 + 2 (t + tv + 2)².
  Two readings.
  (1) Round by round, the convention of the field: that every round-by-round error is at most
    kap · 2^-132 is the hypothesis above, which this file shows of no M.
  (2) The experiment of the definition (`HasIndexBindingWith`, ZKCP/Gen.lean): `eps_ratio` (the
    formula), `epsB_ratio` (ε): ε · 2^131 ≤ t whenever 4 (tv + 2) ≤ t ≤ 2^121; `eps_lower`: t <
    ε-formula · 2^132 for every t. So on that range, for the formula, "queries divided by chance"
    lies between 2^131 and 2^132.
  `eps_at_64` (the formula), `epsB_at_64` (ε): at t ≤ 2^64 (and tv ≤ 2^32) ε ≤ 2^-67;
    `eps_at_64_lower`: at t ≥ 2^64 the formula is at least 2^-68. `eps_floor`: the formula is never
    below (tv + 1) / 2^132.

THE RANGE CHECK'S EVENT (by the paper's evaluation the one source of a completeness error of a
session; in Lean it is to be the hidden withheld set of a request's preamble: zO, and the hidden
part of pO). For one segment with R rows (padding counted or not), at most C columns, 160
combinations, cells below 2^7 + 1 in absolute value and the window 2^17, the block's bound is R ·
160 · 2 exp(-2^20 / C) (`Spec.pr_event_le`, Cb/Gen/RngAlg.lean).
  `event_le`: the bound is at most R · 320 / 2^k if 0 < C and k · 0.6931471808 · C ≤ 2^20.
  `event_kinds`: k = 252, 210, 314 for at most 5,990, 7,200, 4,816 columns.
  `event_sum`: over 12 + 12 + 1 segments, with the rows padded to powers of two (2^19, 2^18, 2^19):
    at most 2^-180. So zO ≤ 2^-180; 64 instances: 2^-174; 2^20 sessions of 64: 2^-154. (reckoned in
    this comment alone: no declaration of this file names `zO`).



Limits: no number here is a security level: the statements are about the formula of a theorem in the
random oracle model on Lean's scheme. This file says nothing on α's (`alphaBG`) public part
(challenges rejected at 0), on ζ's (`zetaBGen`) hash terms and on tV itself: they need the shapes.
No declaration of this file names zO, pO (fields of `LH.Nums`, Iop/InteractiveOracleProof.lean), a segment, an
instance, a session or `Spec.pr_event_le`, nor a term of the reference but `epsS`: the numerals are
literals of this file; `event_le`, `event_kinds` and `event_sum` are inequalities between numbers,
and the steps between them and after `event_sum` are made in this comment only.

Terms: lean/GLOSSARY.md.
-/
import Compile.Batch.SpecBinding
import Cb.Gen.ParLists
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cm.Par
open Iop Compile.Batch Cb.Par
open scoped ENNReal

/-! ## Binding -/

/-- The samplers' bias that the lemmas allow: 1 + 2^-80. -/
def kap : ℝ≥0∞ := ((2 ^ 80 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 80

/-- The numerator of the formula (`epsB_le_frac`) over 2^256. -/
def epsNum (tv t : ℕ) : ℕ := (t + tv + 1) * ((2 ^ 80 + 1) * 2 ^ 44) + 2 * (t + tv + 2) ^ 2

theorem kap_epsS : kap * epsS = (((2 ^ 80 + 1) * 2 ^ 44 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold kap epsS
  have h : (2 ^ 256 : ℝ≥0∞) = 2 ^ 80 * 2 ^ 132 * 2 ^ 44 := by norm_num
  rw [h, Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (by simp) (by simp), ENNReal.mul_inv (by simp) (by simp)]
  have h44 : ((2 ^ 44 : ℕ) : ℝ≥0∞) * (2 ^ 44 : ℝ≥0∞)⁻¹ = 1 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.mul_inv_cancel (by simp) (by simp)
  calc
    ((2 ^ 80 + 1 : ℕ) : ℝ≥0∞) * (2 ^ 80 : ℝ≥0∞)⁻¹ * (2 ^ 132 : ℝ≥0∞)⁻¹ =
        ((2 ^ 80 + 1 : ℕ) : ℝ≥0∞) * (2 ^ 80 : ℝ≥0∞)⁻¹ * (2 ^ 132 : ℝ≥0∞)⁻¹ *
          (((2 ^ 44 : ℕ) : ℝ≥0∞) * (2 ^ 44 : ℝ≥0∞)⁻¹) := by
      rw [h44, mul_one]
    _ = _ := by ring

/-- The bound on binding, as one fraction. -/
theorem epsB_le_frac {I X : Type} {L : BatchProtocol I X} (W : QueryLayout 256 L) (M : LH.Nums) (tv : ℕ)
    (hv : tVB W ≤ tv) (hε : M.εs ≤ kap * epsS) (tC tP : ℕ) :
    epsB W M tC tP ≤ (epsNum tv (tC + tP) : ℝ≥0∞) / 2 ^ 256 := by
  unfold epsB epsNum
  have h1 : ((tC + tP + tVB W + 1 : ℕ) : ℝ≥0∞) ≤ ((tC + tP + tv + 1 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast (by omega : tC + tP + tVB W + 1 ≤ tC + tP + tv + 1)
  have h2 : ((tC + tP + tVB W + 2 : ℕ) : ℝ≥0∞) ≤ ((tC + tP + tv + 2 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast (by omega : tC + tP + tVB W + 2 ≤ tC + tP + tv + 2)
  calc
    ((tC + tP + tVB W + 1 : ℕ) : ℝ≥0∞) * M.εs +
          2 * ((tC + tP + tVB W + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 ≤
        ((tC + tP + tv + 1 : ℕ) : ℝ≥0∞) * (kap * epsS) +
          2 * ((tC + tP + tv + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by gcongr
    _ = _ := by
      have e : (((tC + tP + tv + 1) * ((2 ^ 80 + 1) * 2 ^ 44) +
            2 * (tC + tP + tv + 2) ^ 2 : ℕ) : ℝ≥0∞) =
          ((tC + tP + tv + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 80 + 1) * 2 ^ 44 : ℕ) : ℝ≥0∞) +
            2 * ((tC + tP + tv + 2 : ℕ) : ℝ≥0∞) ^ 2 := by
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul 2, Nat.cast_pow, Nat.cast_ofNat]
      rw [kap_epsS, e, ENNReal.add_div, mul_div_assoc, mul_div_assoc]

/-- A fraction of natural numbers, times a natural number, against a natural number. -/
theorem frac_mul_le {a b c t : ℕ} (hb : 0 < b) (h : a * c ≤ t * b) :
    (a : ℝ≥0∞) / (b : ℝ≥0∞) * (c : ℝ≥0∞) ≤ (t : ℝ≥0∞) := by
  have hb0 : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb.ne'
  have hbt : (b : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top b
  have h' : (a : ℝ≥0∞) * c ≤ (t : ℝ≥0∞) * b := by exact_mod_cast h
  calc (a : ℝ≥0∞) / b * c = (a : ℝ≥0∞) * c / b := by rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    _ ≤ (t : ℝ≥0∞) * b / b := ENNReal.div_le_div_right h' _
    _ = t := ENNReal.mul_div_cancel_right hb0 hbt

/-- Queries over chance, from below: (the formula) · 2^131 ≤ t on the range 4 (tv + 2) ≤ t ≤ 2^121.
-/
theorem eps_ratio {tv t : ℕ} (h1 : 4 * (tv + 2) ≤ t) (h2 : t ≤ 2 ^ 121) :
    epsNum tv t * 2 ^ 131 ≤ t * 2 ^ 256 := by
  have hu : 4 * (t + tv + 2) ≤ 5 * t := by omega
  have ha : 16 * epsNum tv t ≤ 20 * t * ((2 ^ 80 + 1) * 2 ^ 44) + 50 * t ^ 2 := by
    have e1 : epsNum tv t ≤ (t + tv + 2) * ((2 ^ 80 + 1) * 2 ^ 44) + 2 * (t + tv + 2) ^ 2 := by
      unfold epsNum
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
    have e2 : (4 * (t + tv + 2)) ^ 2 ≤ (5 * t) ^ 2 := Nat.pow_le_pow_left hu 2
    calc
      16 * epsNum tv t ≤ 16 * ((t + tv + 2) * ((2 ^ 80 + 1) * 2 ^ 44) + 2 * (t + tv + 2) ^ 2) :=
        Nat.mul_le_mul_left _ e1
      _ = 4 * (4 * (t + tv + 2)) * ((2 ^ 80 + 1) * 2 ^ 44) + 2 * (4 * (t + tv + 2)) ^ 2 := by ring
      _ ≤ 4 * (5 * t) * ((2 ^ 80 + 1) * 2 ^ 44) + 2 * (5 * t) ^ 2 :=
          Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hu))
            (Nat.mul_le_mul_left _ e2)
      _ = _ := by ring
  have hb : 20 * ((2 ^ 80 + 1) * 2 ^ 44) + 50 * t ≤ 2 ^ 129 := by
    have : 50 * t ≤ 50 * 2 ^ 121 := Nat.mul_le_mul_left _ h2
    have h3 : 20 * ((2 ^ 80 + 1) * 2 ^ 44) + 50 * 2 ^ 121 ≤ 2 ^ 129 := by norm_num
    omega
  have hc : 16 * (epsNum tv t * 2 ^ 131) ≤ 16 * (t * 2 ^ 256) :=
    calc 16 * (epsNum tv t * 2 ^ 131) = 16 * epsNum tv t * 2 ^ 131 := by ring
      _ ≤ (20 * t * ((2 ^ 80 + 1) * 2 ^ 44) + 50 * t ^ 2) * 2 ^ 131 := Nat.mul_le_mul_right _ ha
      _ = t * (20 * ((2 ^ 80 + 1) * 2 ^ 44) + 50 * t) * 2 ^ 131 := by ring
      _ ≤ t * 2 ^ 129 * 2 ^ 131 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb)
      _ = 16 * (t * 2 ^ 256) := by ring
  exact Nat.le_of_mul_le_mul_left hc (by norm_num)

/-- Queries over chance, from above: t < (the formula) · 2^132, for every t and tv. -/
theorem eps_lower (tv t : ℕ) : t * 2 ^ 256 < epsNum tv t * 2 ^ 132 := by
  have h1 : (t + 1) * (2 ^ 80 * 2 ^ 44) ≤ epsNum tv t := by
    unfold epsNum
    refine le_trans (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ (by omega)))
      (Nat.le_add_right _ _)
  calc t * 2 ^ 256 < (t + 1) * 2 ^ 256 := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    _ = (t + 1) * (2 ^ 80 * 2 ^ 44) * 2 ^ 132 := by ring
    _ ≤ epsNum tv t * 2 ^ 132 := Nat.mul_le_mul_right _ h1

/-- The formula is never below (tv + 1) / 2^132. -/
theorem eps_floor (tv t : ℕ) : (tv + 1) * 2 ^ 256 ≤ epsNum tv t * 2 ^ 132 := by
  have h1 : (tv + 1) * (2 ^ 80 * 2 ^ 44) ≤ epsNum tv t := by
    unfold epsNum
    refine le_trans (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ (by omega)))
      (Nat.le_add_right _ _)
  calc (tv + 1) * 2 ^ 256 = (tv + 1) * (2 ^ 80 * 2 ^ 44) * 2 ^ 132 := by ring
    _ ≤ epsNum tv t * 2 ^ 132 := Nat.mul_le_mul_right _ h1

theorem epsNum_mono {tv tv' t t' : ℕ} (hv : tv ≤ tv') (ht : t ≤ t') :
    epsNum tv t ≤ epsNum tv' t' := by
  unfold epsNum
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (by omega))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))

/-- At t ≤ 2^64 queries and tv ≤ 2^32 the formula is at most 2^-67. -/
theorem eps_at_64 {tv t : ℕ} (hv : tv ≤ 2 ^ 32) (ht : t ≤ 2 ^ 64) :
    epsNum tv t * 2 ^ 67 ≤ 2 ^ 256 :=
  le_trans (Nat.mul_le_mul_right _ (epsNum_mono hv ht)) (by unfold epsNum; norm_num)

/-- At t ≥ 2^64 queries the formula is at least 2^-68. -/
theorem eps_at_64_lower {tv t : ℕ} (ht : 2 ^ 64 ≤ t) : 2 ^ 256 ≤ epsNum tv t * 2 ^ 68 :=
  le_trans (by unfold epsNum; norm_num) (Nat.mul_le_mul_right _ (epsNum_mono (Nat.zero_le tv) ht))

/-- Reading (2) on the bound itself. -/
theorem epsB_ratio {I X : Type} {L : BatchProtocol I X} (W : QueryLayout 256 L) (M : LH.Nums) (tv : ℕ)
    (hv : tVB W ≤ tv) (hε : M.εs ≤ kap * epsS) (tC tP : ℕ)
    (h1 : 4 * (tv + 2) ≤ tC + tP) (h2 : tC + tP ≤ 2 ^ 121) :
    epsB W M tC tP * 2 ^ 131 ≤ ((tC + tP : ℕ) : ℝ≥0∞) := by
  have h := frac_mul_le (b := 2 ^ 256) (by positivity) (eps_ratio h1 h2)
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat] at h
  refine le_trans ?_ h
  have h3 := epsB_le_frac W M tv hv hε tC tP
  gcongr

theorem epsB_at_64 {I X : Type} {L : BatchProtocol I X} (W : QueryLayout 256 L) (M : LH.Nums)
    (tv : ℕ) (hv : tVB W ≤ tv) (hε : M.εs ≤ kap * epsS) (tC tP : ℕ)
    (h1 : tv ≤ 2 ^ 32) (h2 : tC + tP ≤ 2 ^ 64) :
    epsB W M tC tP * 2 ^ 67 ≤ 1 := by
  have h := frac_mul_le (a := epsNum tv (tC + tP)) (b := 2 ^ 256) (c := 2 ^ 67) (t := 1)
    (by positivity) (by rw [one_mul]; exact eps_at_64 h1 h2)
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h
  refine le_trans ?_ h
  have h3 := epsB_le_frac W M tv hv hε tC tP
  gcongr

/-! ## The range check's event -/

/-- exp(-x) ≤ 2^-k if k · 0.6931471808 ≤ x. -/
theorem exp_le_half_pow {x : ℝ} {k : ℕ} (h : (k : ℝ) * 0.6931471808 ≤ x) :
    Real.exp (-x) ≤ (1 / 2 : ℝ) ^ k := by
  have h1 : (1 / 2 : ℝ) ^ k = Real.exp (-((k : ℝ) * Real.log 2)) := by
    rw [← Real.exp_log (show (0 : ℝ) < (1 / 2 : ℝ) ^ k by positivity),
      Real.log_pow, one_div, Real.log_inv]
    ring_nf
  rw [h1]
  apply Real.exp_le_exp.2
  have h2 : (k : ℝ) * Real.log 2 ≤ (k : ℝ) * 0.6931471808 := by
    have := Real.log_two_lt_d9
    gcongr
  linarith

/-- The event of one segment: R rows, C columns, 160 combinations, cells below 2^7 + 1, window 2^17.
-/
theorem event_le {R C k : ℕ} (hC : 0 < C) (hk : k * 6931471808 * C ≤ 2 ^ 20 * 10 ^ 10) :
    ((R * 160 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal
          (2 * Real.exp (-(((2 ^ 17 : ℤ) : ℝ) ^ 2 / ((C : ℝ) * (((2 ^ 7 + 1 - 1 : ℤ)) : ℝ) ^ 2)))) ≤
      ((R * 320 : ℕ) : ℝ≥0∞) / 2 ^ k := by
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  have hx : (k : ℝ) * 0.6931471808 ≤
      ((2 ^ 17 : ℤ) : ℝ) ^ 2 / ((C : ℝ) * (((2 ^ 7 + 1 - 1 : ℤ)) : ℝ) ^ 2) := by
    have e : ((2 ^ 17 : ℤ) : ℝ) ^ 2 / ((C : ℝ) * (((2 ^ 7 + 1 - 1 : ℤ)) : ℝ) ^ 2) =
        2 ^ 20 / (C : ℝ) := by
      push_cast
      field_simp
      norm_num
    rw [e, le_div_iff₀ hCr]
    have hk' : ((k * 6931471808 * C : ℕ) : ℝ) ≤ ((2 ^ 20 * 10 ^ 10 : ℕ) : ℝ) := by exact_mod_cast hk
    push_cast at hk'
    nlinarith
  have h1 := exp_le_half_pow hx
  have h2 : ENNReal.ofReal
        (2 * Real.exp (-(((2 ^ 17 : ℤ) : ℝ) ^ 2 / ((C : ℝ) * (((2 ^ 7 + 1 - 1 : ℤ)) : ℝ) ^ 2)))) ≤
      2 / 2 ^ k := by
    refine le_trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h1 (by norm_num)))
      (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num),
      one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat,
      div_eq_mul_inv, ENNReal.inv_pow]
  calc ((R * 160 : ℕ) : ℝ≥0∞) * _ ≤ ((R * 160 : ℕ) : ℝ≥0∞) * (2 / 2 ^ k) := by gcongr
    _ = _ := by
      push_cast
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring

/-- The exponents for the three kinds of segment. -/
theorem event_kinds :
    252 * 6931471808 * 5990 ≤ 2 ^ 20 * 10 ^ 10 ∧
    210 * 6931471808 * 7200 ≤ 2 ^ 20 * 10 ^ 10 ∧
    314 * 6931471808 * 4816 ≤ 2 ^ 20 * 10 ^ 10 := by norm_num

/-- All 25 segments, rows padded to powers of two: the sum of the 25 bounds, of three kinds, is at
most 2^-180. -/
theorem event_sum :
    12 * (2 ^ 19 * 320) * 2 ^ (314 - 252) + 12 * (2 ^ 18 * 320) * 2 ^ (314 - 210) + 2 ^ 19 * 320 ≤
      2 ^ (314 - 180) := by norm_num

end Cm.Par
