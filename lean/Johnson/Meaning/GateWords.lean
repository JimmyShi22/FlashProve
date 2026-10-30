-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/GateWords.lean: at every distance a from 0 to 16384 from the tables' middle, the
four words of the verifier's tables SILU and FS (its sigmoid half), made from the power e^(a/256) as
the recursion of Johnson/Meaning/RopeLists.lean has it, are the library's stored words.

By the 257 evaluations in Lean's kernel beneath Johnson/Meaning/GateFineWords.lean (all_ok_fine).
  all_ok: stepOK at every distance. step_neg, step_pos: what stepOK says below and above the middle.
What it does not say by itself: anything on gateTables (Johnson/Meaning/GateRows.lean joins it with
Johnson/Meaning/GateLists.lean) or on the library's refSILU | refSIGM.
-/
import Johnson.Meaning.GateFineWords

set_option autoImplicit false

namespace Meaning.Gate

open OnBytes.Model.Layer (fxOne)
open Meaning.Rope (xAt)
open Inst.Model (dec)

/-- The four comparisons hold at every distance. -/
theorem all_ok {a : ℕ} (ha : a ≤ 16384) : stepOK a (xAt (stepOf 8) a fxOne) = true :=
  all_ok_fine ha

/-- What stepOK says below the middle. -/
theorem step_neg {a x : ℕ} (h : stepOK a x = true) (ha : a ≠ 0) :
    siluOf 8 4095 x a true = dec Inst.Model.Data.silu 13 (16384 - a) + 1 ∧
      dec Inst.Model.Data.silu 13 (16384 - a) ≤ 8190 ∧
      sigOf x true = 16 * min (dec Inst.Model.Data.sigm 13 (16384 - a)) 4096 := by
  unfold stepOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h.1 with h0 | h1
  · exact absurd h0 ha
  · exact ⟨h1.1.1, h1.1.2, h1.2⟩

/-- What stepOK says at and above the middle. -/
theorem step_pos {a x : ℕ} (h : stepOK a x = true) (ha : a ≠ 16384) :
    siluOf 8 4095 x a false = dec Inst.Model.Data.silu 13 (16384 + a) + 1 ∧
      dec Inst.Model.Data.silu 13 (16384 + a) ≤ 8190 ∧
      sigOf x false = 16 * min (dec Inst.Model.Data.sigm 13 (16384 + a)) 4096 := by
  unfold stepOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h.2 with h0 | h1
  · exact absurd h0 ha
  · exact ⟨h1.1.1, h1.1.2, h1.2⟩

#print axioms all_ok

end Meaning.Gate
