-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/OneTableB.lean: no soundness is claimed.
OneTable (ThreeAtW.lean) as a test with code, so that a file of evaluations can evaluate it at the plan's shapes and its accept is the premise by Lean.
  oneTableB cs s · oneTable_iff : oneTableB cs s = true ↔ OneTable cs s
-/
import Johnson.ToldDescR.ThreeAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes OnBytes.Params
open H2K.Pin (mainB maskB)

def oneTableB (cs : Codes) (s : OracleShape) : Bool :=
  decide (¬ (0 < s.mainRows ∧ 0 < s.maskRows)) && decide (0 < s.mainRows ∨ 0 < s.maskRows) &&
    decide ((0 < s.maskRows ∨ s.mainDeg = 3) ∨ (s.maskRows = 0 ∧ s.mainDeg = 1)) &&
    decide (s.mainRows = 0 ∨ 2 ^ ceilLog2 (mainB cs s).ell = (mainB cs s).ell) &&
    decide (s.maskRows = 0 ∨ 2 ^ ceilLog2 (maskB cs s).ell = (maskB cs s).ell)

theorem oneTable_iff (cs : Codes) (s : OracleShape) : oneTableB cs s = true ↔ OneTable cs s := by
  unfold oneTableB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩,
    fun h => ⟨⟨⟨⟨h.one, h.some⟩, h.case⟩, h.powM⟩, h.powZ⟩⟩

end ToldDesc

#print axioms ToldDesc.oneTable_iff
