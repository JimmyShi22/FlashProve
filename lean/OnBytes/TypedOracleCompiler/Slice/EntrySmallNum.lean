-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntrySmallNum.lean: the entry file's bound at the small example, with its count as
a numeral, written out, and as a figure: the small twin of OnBytes/TypedOracleCompiler/Slice/EntryFullV.lean and
EntryFullNum.lean.

Main theorems.
 `smallV_eq`            smallV = 7975: by the kernel's evaluation.
 `entryB_small`         the bound's first part written out: with T = (t + 2 + 805475 + 7975) * 5 it
                        is T * εs + 2 * (T + 1)^2 / 2^256 + (t + 805475)^2 / 2^256.
 `small_one_world_num`  `small_one_world` (OnBytes/TypedOracleCompiler/Slice/EntrySmallTop.lean) with that numeral.
 `entryB_small_le t N e`   for all t up to N the bound is at most (1/2)^e, from ONE inequality
                        between natural numbers in N and e, which is evaluated.
 `entryB_small_40`, `entryB_small_64`, `entryB_small_80`   up to 2^40 queries at most 2^-85; up to
                        2^64 at most 2^-61; up to 2^80 at most 2^-45.
 `small_one_world_le`, `small_one_world_64`   `small_one_world_num` with these figures.

What is not claimed. The figures are ceilings, whole exponents, not the bound's value. They are
figures of THE BOUND OF ONE THEOREM, on one of three files, for a checker in Lean over a random
oracle, under the hypothesis on codes; at four rounds 32 of the 128 bits are proof of work, counted
at one query a try. WITHOUT THE WORK: about 2^-53, 2^-29, 2^-13 at these three numbers of queries:
arithmetic off the shares in the head of OnBytes/Slice/SmallRecNum.lean, NO THEOREM. The figures are
the full size's again, because from 2^40 queries on both bounds are about 5 t / 2^128. They are no
"bits of security" of any program. 7975 is a ceiling by the wiring (every opening is charged the
greatest depth), not the number of queries of a run. The limits of
OnBytes/TypedOracleCompiler/Slice/EntrySmallTop.lean stand. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntrySmallTop
import OnBytes.TypedOracleCompiler.Slice.EntryFullNum

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Prob Cb TypedOracleCompiler.Run
open OnBytes.Slice (GE GF)
open OnBytes.Slice.Shapes (zSmall Files Cfg pubS₀ pubS₁ rdC)
open Rom _root_.Compile
open scoped ENNReal

set_option maxRecDepth 100000 in
/-- The count at the small sizes, as a numeral: by the kernel's evaluation. -/
theorem smallV_eq : smallV = 7975 := by decide +kernel

/-- The written bound at the small sizes' numbers, written out. -/
theorem entryB_small (εs : ℝ≥0∞) (t : ℕ) :
    entryB εs 0 101 7975 t =
      (((t + 2 + 805475 + 7975) * 5 : ℕ) : ℝ≥0∞) * εs +
          2 * (((t + 2 + 805475 + 7975) * 5 + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 +
        (((t + 805475) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold entryB
  norm_num

/-- The bound for the entry file at the small example, with the count as a numeral. -/
theorem small_one_world_num (hA : Cb.BCHKS46At GF GE) (cfg : Cfg) (conv : homeSmall.Conv cfg)
    (A : OComp (rom 256) Files) (t : ℕ) (hA' : A.QueryBound t) :
    Rom.Pr A.withTrace (EntryLose zSmall.T zSmall.v zSmall.eM (anT zSmall.v zSmall.s)
      (homeSmall.at cfg conv) (((2 : ℝ≥0∞)⁻¹) ^ 128)
      (homeSmall.typ cfg conv (((2 : ℝ≥0∞)⁻¹) ^ 128)) 0 101 (pubS₀ cfg)
      (pubS₁ [homeSmall.prm] cfg) (rdC zSmall cfg)) ≤
      entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 101 7975 t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have h := small_one_world hA cfg conv A t hA'
  rw [smallV_eq] at h
  exact h

/-- THE ENTRY FILE'S BOUND AT THE SMALL EXAMPLE BELOW A POWER OF ONE HALF, from one inequality
between natural numbers: for all t up to N. -/
theorem entryB_small_le (t N e : ℕ) (he : e ≤ 256) (ht : t ≤ N)
    (hN : (N + 2 + 805475 + 7975) * 5 * 2 ^ 128 + 2 * ((N + 2 + 805475 + 7975) * 5 + 1) ^ 2 +
      (N + 805475) ^ 2 + N ^ 2 ≤ 2 ^ (256 - e)) :
    entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 101 7975 t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((2 : ℝ≥0∞)⁻¹) ^ e := by
  have hX := le_trans (num_mono 805475 7975 t N ht) hN
  rw [entryB_small]
  exact frac_le 805475 7975 t e he hX

/-- Up to 2^40 queries the written bound is at most 2^-85. A ceiling; the limits of the head stand.
-/
theorem entryB_small_40 (t : ℕ) (ht : t ≤ 2 ^ 40) :
    entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 101 7975 t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 85 :=
  entryB_small_le t (2 ^ 40) 85 (by norm_num) ht (by norm_num)

/-- Up to 2^64 queries the written bound is at most 2^-61. A ceiling; the limits of the head stand.
-/
theorem entryB_small_64 (t : ℕ) (ht : t ≤ 2 ^ 64) :
    entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 101 7975 t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 61 :=
  entryB_small_le t (2 ^ 64) 61 (by norm_num) ht (by norm_num)

/-- Up to 2^80 queries the written bound is at most 2^-45. A ceiling; the limits of the head stand.
-/
theorem entryB_small_80 (t : ℕ) (ht : t ≤ 2 ^ 80) :
    entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 101 7975 t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 45 :=
  entryB_small_le t (2 ^ 80) 45 (by norm_num) ht (by norm_num)

/-- THE BOUND FOR THE ENTRY FILE AT THE SMALL EXAMPLE, AS A FIGURE. Under the one hypothesis on
codes: over one uniformly random oracle, for every converter and every maker with at most t queries,
t up to N: the event `EntryLose` has probability at most one half to the e, whenever the one
inequality between natural numbers holds of N and e. -/
theorem small_one_world_le (hA : Cb.BCHKS46At GF GE) (cfg : Cfg) (conv : homeSmall.Conv cfg)
    (A : OComp (rom 256) Files) (t N e : ℕ) (hA' : A.QueryBound t) (he : e ≤ 256) (ht : t ≤ N)
    (hN : (N + 2 + 805475 + 7975) * 5 * 2 ^ 128 + 2 * ((N + 2 + 805475 + 7975) * 5 + 1) ^ 2 +
      (N + 805475) ^ 2 + N ^ 2 ≤ 2 ^ (256 - e)) :
    Rom.Pr A.withTrace (EntryLose zSmall.T zSmall.v zSmall.eM (anT zSmall.v zSmall.s)
      (homeSmall.at cfg conv) (((2 : ℝ≥0∞)⁻¹) ^ 128)
      (homeSmall.typ cfg conv (((2 : ℝ≥0∞)⁻¹) ^ 128)) 0 101 (pubS₀ cfg)
      (pubS₁ [homeSmall.prm] cfg) (rdC zSmall cfg)) ≤ ((2 : ℝ≥0∞)⁻¹) ^ e :=
  le_trans (small_one_world_num hA cfg conv A t hA') (entryB_small_le t N e he ht hN)

/-- Up to 2^64 queries: at most 2^-61: under the one hypothesis on codes, over one uniformly
random oracle, for every converter. The limits of the head stand. -/
theorem small_one_world_64 (hA : Cb.BCHKS46At GF GE) (cfg : Cfg) (conv : homeSmall.Conv cfg)
    (A : OComp (rom 256) Files) (t : ℕ) (hA' : A.QueryBound t) (ht : t ≤ 2 ^ 64) :
    Rom.Pr A.withTrace (EntryLose zSmall.T zSmall.v zSmall.eM (anT zSmall.v zSmall.s)
      (homeSmall.at cfg conv) (((2 : ℝ≥0∞)⁻¹) ^ 128)
      (homeSmall.typ cfg conv (((2 : ℝ≥0∞)⁻¹) ^ 128)) 0 101 (pubS₀ cfg)
      (pubS₁ [homeSmall.prm] cfg) (rdC zSmall cfg)) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 61 :=
  small_one_world_le hA cfg conv A t (2 ^ 64) 61 hA' (by norm_num) ht (by norm_num)

end TypedOracleCompiler.Slice
