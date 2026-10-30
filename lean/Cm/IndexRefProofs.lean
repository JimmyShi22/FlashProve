-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/IndexRefProofs.lean: laws of `ext` and `cut` (Cm/RelBase.lean).








-/
import Cb.Gen.Tensor
import Cm.RelBase
import Inst.Model.IndexM
import Cb.Gen.TensorProofs
import Cb.Gen.CodeProofsComp
import Mathlib.Data.FinEnum

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm
open Iop Prob Blocks Hiop Cb Code Inst.Model
open Inst.Model.Layout (kRef hRef)

theorem ext_in (M : Shape) {y c : ℕ} (hy : y < hRef) (hc : c < 2 ^ kRef) :
    ext M y c = M ⟨y, hy⟩ ⟨c, hc⟩ := dif_pos ⟨hy, hc⟩
theorem ext_out (M : Shape) {y c : ℕ} (h : ¬ (y < hRef ∧ c < 2 ^ kRef)) : ext M y c = 0 := dif_neg h

theorem cut_ext (M : Shape) : cut (ext M) = M := by
  funext y c
  exact ext_in M y.2 c.2

theorem ext_cut_in (W : Mat) {y c : ℕ} (hy : y < hRef) (hc : c < 2 ^ kRef) :
    ext (cut W) y c = W y c := ext_in _ hy hc

end Cm
