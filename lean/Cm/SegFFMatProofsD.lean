-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegFFMatProofsD.lean: the number read by a list of sources with one constant bit appended
(`num_bit`; `Src.num`: Cm/SegIdx.lean). Cm/TargetSegFFMatProofsD.lean reads it, for the key family
QK of the feed-forward segment.
-/
import Cm.SegFFMatProofs

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Code Inst.Model Inst.Model.All Finset
open Ex

/-- The number read by a list of sources with a constant bit appended: twice the list's number plus
the bit. -/
theorem num_bit (σ : List Src) (β : Bool) (v b : ℕ) :
    Src.num (σ ++ [.bit β]) v b = Src.num σ v b * 2 + (if β then 1 else 0) := by
  rw [num_append]
  cases β <;> simp [Src.num, numL, Src.bitAt]

end Cm.Seg
