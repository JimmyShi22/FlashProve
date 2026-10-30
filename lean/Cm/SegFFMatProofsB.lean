-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegFFMatProofsB.lean: two lemmas for the key families G and U (gate and up projection) of the
feed-forward segment (`Cm.Seg.TS.matKeyFam`, Cm/TargetSegFFMat.lean): `fOf_le`, `routed_iff`. (Key
families of the model's arithmetisation: what a family, a block and a vertex are is told in the head
of Cm/SegFFMat.lean.)
-/
import Cm.SegFFMatProofs

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Code Inst.Model Inst.Model.All Finset
open Ex

variable [scl : Scl]

theorem fOf_le (L : ℕ) : fOf L ≤ 2 ^ 14 := by
  unfold fOf
  split_ifs
  · show 8192 ≤ 2 ^ 14
    norm_num
  · show 16384 ≤ 2 ^ 14
    norm_num

theorem routed_iff {l x : ℕ} : FFSeg.routed DF l x = true ↔ l % 2 = 1 ∧ DF.fe ≤ x := by
  simp [FFSeg.routed, FFSeg.isExpL]

end Cm.Seg
