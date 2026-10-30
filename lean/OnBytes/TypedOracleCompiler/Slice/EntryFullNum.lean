-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryFullNum.lean: the entry file's bound at the full size as a figure.

OnBytes/TypedOracleCompiler/Slice/EntryFullV.lean has the bound with its count as a numeral: `entryB (2⁻¹)^128 0 142
13545 t` + t^2 / 2^256. Here it is held below a power of one half.

Main theorems.
 `entryB_full_le t N e` for all t up to N the bound is at most (1/2)^e, from ONE inequality between
     natural numbers in N and e, which is evaluated.
 `entryB_full_40`, `entryB_full_64`, `entryB_full_80` up to 2^40 queries at most 2^-85; up to 2^64
     at most 2^-61; up to 2^80 at most 2^-45.
 `full_one_world_le`, `full_one_world_64` `full_one_world_num` with these figures.
Beneath: `half_pow_eq`, `half_128`, `frac_sum`, `num_mono`, `frac_le`.

WITH WORK AND WITHOUT. The figures count, at 6 of the 41 rounds, 32 of the 128 bits as proof of
work, at one query a try. Without that credit the worst round stands at about 2^-96.2, and the bound
would read about 5 t / 2^96: about 2^-53, 2^-29, 2^-13 at 2^40, 2^64, 2^80 queries. THAT IS
ARITHMETIC OUTSIDE LEAN, NO THEOREM: no Lean text states the bound at that error.

What is not claimed. The figures are ceilings, whole exponents, not the bound's value. They are
figures of THE BOUND OF ONE THEOREM, on one of three files, for a checker in Lean over a random
oracle, under the hypothesis on codes; in some rounds 32 of the 128 bits are proof of work, counted
at one query a try. They are no "bits of security" of any program. The limits of
OnBytes/TypedOracleCompiler/Slice/EntryFullTop.lean stand.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryFullV

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open scoped ENNReal

/-- A power of one half, as a fraction with a larger power of two beneath. -/
theorem half_pow_eq (a b : ℕ) (h : a ≤ b) :
    ((2 : ℝ≥0∞)⁻¹) ^ a = (2 : ℝ≥0∞) ^ (b - a) / 2 ^ b := by
  have h0 : ∀ n : ℕ, (2 : ℝ≥0∞) ^ n ≠ 0 := fun n => pow_ne_zero n (by norm_num)
  have ht : ∀ n : ℕ, (2 : ℝ≥0∞) ^ n ≠ ⊤ := fun n => ENNReal.pow_ne_top (by norm_num)
  rw [ENNReal.eq_div_iff (h0 b) (ht b), ← ENNReal.inv_pow]
  have e : (2 : ℝ≥0∞) ^ b = 2 ^ (b - a) * 2 ^ a := by rw [← pow_add, Nat.sub_add_cancel h]
  rw [e, mul_assoc, ENNReal.mul_inv_cancel (h0 a) (ht a), mul_one]

/-- Four fractions over 2^256 as one. -/
theorem frac_sum (T T1 U W : ℕ) :
    (T : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 128 / 2 ^ 256) + 2 * (T1 : ℝ≥0∞) ^ 2 / 2 ^ 256 +
      (U : ℝ≥0∞) / 2 ^ 256 + (W : ℝ≥0∞) / 2 ^ 256 =
      ((T * 2 ^ 128 + 2 * T1 ^ 2 + U + W : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [← mul_div_assoc, ENNReal.div_add_div_same, ENNReal.div_add_div_same,
    ENNReal.div_add_div_same]
  congr 1
  push_cast
  ring

/-- One half to the 128, over 2^256. -/
theorem half_128 : ((2 : ℝ≥0∞)⁻¹) ^ 128 = (2 : ℝ≥0∞) ^ 128 / 2 ^ 256 := by
  have h := half_pow_eq 128 256 (by norm_num)
  simpa using h

/-- The numerator grows with the number of queries. -/
theorem num_mono (a b t N : ℕ) (ht : t ≤ N) :
    (t + 2 + a + b) * 5 * 2 ^ 128 + 2 * ((t + 2 + a + b) * 5 + 1) ^ 2 + (t + a) ^ 2 + t ^ 2 ≤
      (N + 2 + a + b) * 5 * 2 ^ 128 + 2 * ((N + 2 + a + b) * 5 + 1) ^ 2 + (N + a) ^ 2 + N ^ 2 := by
  gcongr

/-- The bound's form below a power of one half, at letters for the two large numbers. -/
theorem frac_le (a b t e : ℕ) (he : e ≤ 256)
    (hX : (t + 2 + a + b) * 5 * 2 ^ 128 + 2 * ((t + 2 + a + b) * 5 + 1) ^ 2 + (t + a) ^ 2 + t ^ 2 ≤
      2 ^ (256 - e)) :
    (((t + 2 + a + b) * 5 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
          2 * (((t + 2 + a + b) * 5 + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 +
        (((t + a) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((2 : ℝ≥0∞)⁻¹) ^ e := by
  rw [half_128, half_pow_eq e 256 he, frac_sum]
  refine ENNReal.div_le_div_right ?_ _
  have h2 : ((2 ^ (256 - e) : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (256 - e) := by push_cast; rfl
  rw [← h2]
  exact Nat.cast_le.2 hX

/-- THE ENTRY FILE's BOUND AT THE FULL SIZE BELOW A POWER OF ONE HALF, from one inequality
between natural numbers: for all t up to N. -/
theorem entryB_full_le (t N e : ℕ) (he : e ≤ 256) (ht : t ≤ N)
    (hN : (N + 2 + 1923390 + 13545) * 5 * 2 ^ 128 + 2 * ((N + 2 + 1923390 + 13545) * 5 + 1) ^ 2 +
      (N + 1923390) ^ 2 + N ^ 2 ≤ 2 ^ (256 - e)) :
    entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 142 13545 t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((2 : ℝ≥0∞)⁻¹) ^ e := by
  have hX := le_trans (num_mono 1923390 13545 t N ht) hN
  rw [entryB_full]
  exact frac_le 1923390 13545 t e he hX

/-- Up to 2^40 queries: at most 2^-85. -/
theorem entryB_full_40 (t : ℕ) (ht : t ≤ 2 ^ 40) :
    entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 142 13545 t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 85 :=
  entryB_full_le t (2 ^ 40) 85 (by norm_num) ht (by norm_num)

/-- Up to 2^64 queries: at most 2^-61. -/
theorem entryB_full_64 (t : ℕ) (ht : t ≤ 2 ^ 64) :
    entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 142 13545 t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 61 :=
  entryB_full_le t (2 ^ 64) 61 (by norm_num) ht (by norm_num)

/-- Up to 2^80 queries: at most 2^-45. -/
theorem entryB_full_80 (t : ℕ) (ht : t ≤ 2 ^ 80) :
    entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 142 13545 t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 45 :=
  entryB_full_le t (2 ^ 80) 45 (by norm_num) ht (by norm_num)

open Prob Cb TypedOracleCompiler.Run Rom _root_.Compile in
open OnBytes.Slice (GE GF) in
open OnBytes.Slice.Shapes (zFull Files Cfg pubS₀ pubS₁ rdC) in
/-- (a) FOR THE ENTRY FILE AT THE FULL SIZE, AS A FIGURE. Under the one hypothesis on codes:
over one uniformly random oracle, for every converter and every maker with at most t queries, t up
to N:
the event `EntryLose` has probability at most one half to the e, whenever the one inequality
between natural numbers holds of N and e. -/
theorem full_one_world_le (d₁ : Sd1 zFull.lg zFull.s) [DecidableEq (Sd1 zFull.lg zFull.s)]
    (hA : Cb.BCHKS46At GF GE) (cfg : Cfg) (conv : (homeFull d₁).Conv cfg)
    (A : OComp (rom 256) Files) (t N e : ℕ) (hA' : A.QueryBound t) (he : e ≤ 256) (ht : t ≤ N)
    (hN : (N + 2 + 1923390 + 13545) * 5 * 2 ^ 128 + 2 * ((N + 2 + 1923390 + 13545) * 5 + 1) ^ 2 +
      (N + 1923390) ^ 2 + N ^ 2 ≤ 2 ^ (256 - e)) :
    Rom.Pr A.withTrace (EntryLose zFull.T zFull.v zFull.eM (anT zFull.v zFull.s)
      ((homeFull d₁).at cfg conv) (((2 : ℝ≥0∞)⁻¹) ^ 128)
      ((homeFull d₁).typ cfg conv (((2 : ℝ≥0∞)⁻¹) ^ 128)) 0 142 (pubS₀ cfg)
      (pubS₁ [(homeFull d₁).prm] cfg) (rdC zFull cfg)) ≤ ((2 : ℝ≥0∞)⁻¹) ^ e :=
  le_trans (full_one_world_num d₁ hA cfg conv A t hA') (entryB_full_le t N e he ht hN)

open Prob Cb TypedOracleCompiler.Run Rom _root_.Compile in
open OnBytes.Slice (GE GF) in
open OnBytes.Slice.Shapes (zFull Files Cfg pubS₀ pubS₁ rdC) in
/-- Up to 2^64 queries: at most 2^-61. -/
theorem full_one_world_64 (d₁ : Sd1 zFull.lg zFull.s) [DecidableEq (Sd1 zFull.lg zFull.s)]
    (hA : Cb.BCHKS46At GF GE) (cfg : Cfg) (conv : (homeFull d₁).Conv cfg)
    (A : OComp (rom 256) Files) (t : ℕ) (hA' : A.QueryBound t) (ht : t ≤ 2 ^ 64) :
    Rom.Pr A.withTrace (EntryLose zFull.T zFull.v zFull.eM (anT zFull.v zFull.s)
      ((homeFull d₁).at cfg conv) (((2 : ℝ≥0∞)⁻¹) ^ 128)
      ((homeFull d₁).typ cfg conv (((2 : ℝ≥0∞)⁻¹) ^ 128)) 0 142 (pubS₀ cfg)
      (pubS₁ [(homeFull d₁).prm] cfg) (rdC zFull cfg)) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 61 :=
  full_one_world_le d₁ hA cfg conv A t (2 ^ 64) 61 hA' (by norm_num) ht (by norm_num)

end TypedOracleCompiler.Slice
