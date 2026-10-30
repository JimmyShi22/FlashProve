-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegLayoutPlainProofs.lean: the proof of the statement `Spec.lay_lift_cast` of
Cm/TargetSegLayoutPlain.lean, as it is stated there, over p = 2^64 - 2^32 + 1.

The statement and its limits: Cm/TargetSegLayoutPlain.lean, the head, Limits.
-/
import Cm.SegLayoutPlainProofs
import Cm.TargetSegAll
import Cm.TargetSegLayoutPlain


set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Seg Inst.Model Inst.Model.All

theorem lay_lift_cast : Spec.lay_lift_cast := by
  intro D hD z hz
  obtain ⟨h1, h2⟩ := abs_lt.1 hz
  unfold lift
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩ <;> omega

end Cm.Seg.TS
