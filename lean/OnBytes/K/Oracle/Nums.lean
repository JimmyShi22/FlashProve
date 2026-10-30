-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/Nums.lean: the entry file's written bound (`entryB`,
OnBytes/TypedOracleCompiler/Slice/EntryData.lean) below a power of one half, with the number tT of strings that the
typing asks the oracle as a letter.

OnBytes/TypedOracleCompiler/Slice/EntryFullNum.lean and EntrySmallNum.lean have this at tT = 0, for a typing that
asks the oracle nothing. In the written bound tT stands beside V * Bk, the blocks of the judge's
typed queries, in one number. So the two lemmas of EntryFullNum.lean that are general in that number
(`frac_le`, and `num_mono` said once more for two numbers) carry over.

Main theorems:
  `entryB_eq`: the written bound, written out, with tT + V * Bk as one number.
  `entryB_le`: below one half to the e, for all t up to N and all tT with tT + V * Bk up to M, from
    one inequality between natural numbers in N, M, V and e.
  `entryB_fullT_64`: at the full size's numbers (Bk = 142, V = 13545), for tT up to 2^32: at most
    2^-61 for t up to 2^64.
  `entryB_smallT_64`: the same at the small example's numbers (Bk = 101, V = 7975).

What is not claimed: arithmetic alone. No event, no probability and no checker stands in this file:
that the written bound bounds anything is another file's theorem, with its own hypotheses. That some
typing asks at most 2^32 strings is not shown here. The exponents are those at tT = 0: they are
ceilings of the written bound at error 2^-128 a round, and that error counts proof of work in some
rounds (the heads of EntryFullNum.lean and EntrySmallNum.lean). They are no level of security of any
program. For proofs only; the program, that is the Lean port built from OnBytes/, does not import
this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntrySmallNum

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open scoped ENNReal

/-- The written bound with the typing's strings as a letter: they stand beside the blocks of the
judge's typed queries, in one number. -/
theorem entryB_eq (εs : ℝ≥0∞) (tT Bk V t : ℕ) :
    entryB εs tT Bk V t =
      (((t + 2 + (tT + V * Bk) + V) * 5 : ℕ) : ℝ≥0∞) * εs +
          2 * (((t + 2 + (tT + V * Bk) + V) * 5 + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 +
        (((t + (tT + V * Bk)) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold entryB
  norm_num

/-- The numerator grows with the number of queries and with the first of the two numbers. -/
theorem num_mono2 (a M b t N : ℕ) (ht : t ≤ N) (ha : a ≤ M) :
    (t + 2 + a + b) * 5 * 2 ^ 128 + 2 * ((t + 2 + a + b) * 5 + 1) ^ 2 + (t + a) ^ 2 + t ^ 2 ≤
      (N + 2 + M + b) * 5 * 2 ^ 128 + 2 * ((N + 2 + M + b) * 5 + 1) ^ 2 + (N + M) ^ 2 + N ^ 2 := by
  gcongr

/-- The written bound below a power of one half, from one inequality between natural numbers: for
all t up to N, and all numbers tT of the typing's strings with tT + V * Bk up to M. -/
theorem entryB_le (tT Bk V t N M e : ℕ) (he : e ≤ 256) (ht : t ≤ N) (hT : tT + V * Bk ≤ M)
    (hN : (N + 2 + M + V) * 5 * 2 ^ 128 + 2 * ((N + 2 + M + V) * 5 + 1) ^ 2 + (N + M) ^ 2 + N ^ 2 ≤
      2 ^ (256 - e)) :
    entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) tT Bk V t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((2 : ℝ≥0∞)⁻¹) ^ e := by
  rw [entryB_eq]
  exact frac_le (tT + V * Bk) V t e he (le_trans (num_mono2 _ M V t N ht hT) hN)

/-- At the full size's numbers, for a typing that asks at most 2^32 strings: up to 2^64 queries the
written bound is at most 2^-61. -/
theorem entryB_fullT_64 (tT t : ℕ) (hT : tT ≤ 2 ^ 32) (ht : t ≤ 2 ^ 64) :
    entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) tT 142 13545 t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 61 :=
  entryB_le tT 142 13545 t (2 ^ 64) (2 ^ 32 + 13545 * 142) 61 (by norm_num) ht
    (Nat.add_le_add_right hT _) (by norm_num)

/-- At the small example's numbers, for a typing that asks at most 2^32 strings: up to 2^64 queries
the written bound is at most 2^-61. -/
theorem entryB_smallT_64 (tT t : ℕ) (hT : tT ≤ 2 ^ 32) (ht : t ≤ 2 ^ 64) :
    entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) tT 101 7975 t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 61 :=
  entryB_le tT 101 7975 t (2 ^ 64) (2 ^ 32 + 7975 * 101) 61 (by norm_num) ht
    (Nat.add_le_add_right hT _) (by norm_num)

end TypedOracleCompiler.Slice
