-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegFFAffPass.lean: integer matrices read as an integer trace of the feed-forward segment of group
g (`tM`), and the values of that trace on valid names (`rd_agrees`).

Cm/TargetSegFFAffPass.lean has both again, in `Cm.Seg.TS`, and tells what a (V) statement says.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegPilotKit
import Cm.RelBase
import Inst.Model.FF.CastValid

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Inst.Model Inst.Model.All Finset
open Inst.Model.Layout (kRef)

variable [scl : Scl] (g : ℕ)

/-- integer matrices, read as an integer trace of the feed-forward segment of group g -/
def tM (M : ℕ → ℕ → ℕ → ℤ) : FFSeg.Cell → ℤ := fun c => at' M (ownFF g c).place

variable (M : ℕ → ℕ → ℕ → ℤ)
  (t' : {c : FFSeg.Cell // c.Valid DF} → ℤ) (ht : ∀ c, t' c = tM g M c.val)
include ht

theorem rd_agrees :
    ∀ c : FFSeg.Cell, c.Valid DF → tM g M c = (FFSeg.rd DF t' : FFSeg.Cell → ℤ) c := fun c hc => by
  unfold FFSeg.rd
  rw [dif_pos hc, ht ⟨c, hc⟩]
  exact (Int.cast_id).symm

end Cm.Seg
