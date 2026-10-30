-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegLayoutPlain.lean: the way back from the field with p = 2^64 - 2^32 + 1 elements to the
integers: the integer that an entry of a decoded matrix of cells stands for.

Definitions and statements; the proofs are in Cm/TargetSegLayoutPlainProofs.lean.

Main names:
  `lift`: the integer that an element of `Cb.Gl.F` (Cb/Gl/GlField.lean), the integers modulo p,
    stands for: its representative of least absolute value.
  `Spec.lay_lift_cast`: an integer below 2 D in absolute value, 4 D < p, is read back from its
    image.

Limits: this file says nothing on conditions, codes or protocols.
-/
import Cm.SegLayoutPlain
import Cm.TargetSegAll


set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS

/-- the integer that an entry of a decoded matrix of cells stands for -/
def lift : Cb.Gl.F → ℤ := ZMod.valMinAbs

end Cm.Seg.TS

namespace Cm.Seg.TS.Spec
open Cm.Spec
open Cm.Seg Inst.Model.All

def lay_lift_cast : Prop :=
  ∀ D : ℤ, 4 * D < (Code.pGold : ℤ) → ∀ z : ℤ, |z| < 2 * D → lift ((z : ℤ) : Cb.Gl.F) = z

end Cm.Seg.TS.Spec
