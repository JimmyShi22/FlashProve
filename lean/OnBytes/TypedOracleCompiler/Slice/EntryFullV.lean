-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryFullV.lean: the count at the full size as a numeral, and the entry file's
bound with it.

`fullV` (OnBytes/TypedOracleCompiler/Slice/EntryFullTop.lean) is the bound on the judge's typed queries at the full
size's written rounds: a closed term. Here the kernel evaluates it.

Main theorems.
 `fullV_eq`   fullV = 13545.
 `full_one_world_num`   `full_one_world` with that numeral: the bound is
   `entryB (2⁻¹)^128 0 142 13545 t` + t^2 / 2^256.
 `entryB_full`   that expression written out: with T = (t + 2 + 1923390 + 13545) * 5 it is
   T * (2⁻¹)^128 + 2 * (T + 1)^2 / 2^256 + (t + 1923390)^2 / 2^256.

What is not claimed. No figure "2 to the minus so much" is shown of the bound at any t. 13545 is a
ceiling by the wiring (every opening is charged the greatest depth), not the number of queries of a
run. The limits of OnBytes/TypedOracleCompiler/Slice/EntryFullTop.lean stand.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryFullTop

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Prob Cb TypedOracleCompiler.Run
open OnBytes.Slice (GE GF)
open OnBytes.Slice.Shapes (zFull Files Cfg pubS₀ pubS₁ rdC)
open Rom _root_.Compile
open scoped ENNReal

set_option maxRecDepth 100000 in
/-- The count at the full size, as a numeral: by the kernel's evaluation. -/
theorem fullV_eq : fullV = 13545 := by decide +kernel

/-- The written bound at the full size's numbers, written out. -/
theorem entryB_full (εs : ℝ≥0∞) (t : ℕ) :
    entryB εs 0 142 13545 t =
      (((t + 2 + 1923390 + 13545) * 5 : ℕ) : ℝ≥0∞) * εs +
          2 * (((t + 2 + 1923390 + 13545) * 5 + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 +
        (((t + 1923390) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold entryB
  norm_num

/-- (a) FOR THE ENTRY FILE AT THE FULL SIZE, WITH THE COUNT AS A NUMERAL. -/
theorem full_one_world_num (d₁ : Sd1 zFull.lg zFull.s) [DecidableEq (Sd1 zFull.lg zFull.s)]
    (hA : Cb.BCHKS46At GF GE) (cfg : Cfg) (conv : (homeFull d₁).Conv cfg)
    (A : OComp (rom 256) Files) (t : ℕ) (hA' : A.QueryBound t) :
    Rom.Pr A.withTrace (EntryLose zFull.T zFull.v zFull.eM (anT zFull.v zFull.s)
      ((homeFull d₁).at cfg conv) (((2 : ℝ≥0∞)⁻¹) ^ 128)
      ((homeFull d₁).typ cfg conv (((2 : ℝ≥0∞)⁻¹) ^ 128)) 0 142 (pubS₀ cfg)
      (pubS₁ [(homeFull d₁).prm] cfg) (rdC zFull cfg)) ≤
      entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 142 13545 t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have h := full_one_world d₁ hA cfg conv A t hA'
  rw [fullV_eq] at h
  exact h

end TypedOracleCompiler.Slice
