-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegLayoutPlain.lean: the dictionary of Cm/SegLayout.lean (between names of cells and places in
the segments' matrices) at the plain head.

One statement; the proof is in Cm/SegLayoutPlainProofs.lean.

Main names:
  `lay_below_plain`: the bound of the relation with the plain head (`Below2`, Cm/Rel2.lean) is "all
    own cells are below B" (`BelowN`) at `Hd.plain`: the valid names of the dictionary are exactly
    the names on which that relation puts its bound.
`lay_below_plain` is used in Cm/TargetSegModelProofs.lean.

Limits: this file says nothing on conditions, codes or protocols.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegLayout
import Cm.Rel2

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Spec
open Cm.Seg Inst.Model.All

def lay_below_plain : Prop := ∀ (B : ℤ) (T : Trace), Cm.Below2 B T ↔ BelowN Hd.plain B T

end Cm.Spec
