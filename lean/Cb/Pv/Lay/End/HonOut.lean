-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/HonOut.lean: for any parameters of the short hiding sumcheck, an output at which all
output claims hold.

Main names:
  `honOut`: for any parameters of a sumcheck, an output, and entries: the output with the maps' own
  values in the places of the shown values and the last value that the first output row asks. Its
  state, drawn coefficient and point are those of the given output.
  `honOut_holds`: all output claims hold at it.
Limits: that such an output is put out by a run of the sumcheck is not said.


-/
import Cb.Ld.LdPsc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.End

open Finset Cb

section Hon
variable {E : Type} [Field E] (Y : PscPar E)

/-- The output o with the maps' own values at the entries m in the places of the shown values, and
the last value that the first output row then asks. -/
noncomputable def honOut (o : Y.Out) (m : Y.J → E) : Y.Out where
  st := o.st
  eps := o.eps
  pt := o.pt
  fin := hU (Y.vars o.st) (Y.W o.st m) (Y.hp o.st o.pt) +
      o.eps * hPsi (Y.vars o.st) (Y.hp o.st o.pt) * Y.inc o.st m +
      o.eps * ∑ b, Y.S1 o.st (Y.hp o.st o.pt) (fun a => Y.G o.st m a (Y.hp o.st o.pt)) b *
        Y.Gb o.st m b (Y.hp o.st o.pt) +
    o.eps * Y.S0 o.st (Y.hp o.st o.pt) fun a => Y.G o.st m a (Y.hp o.st o.pt)
  vals := fun a => Y.G o.st m a (Y.hp o.st o.pt)

/-- All output claims hold at honOut. -/
theorem honOut_holds (o : Y.Out) (m : Y.J → E) : Y.OutHolds (honOut Y o m) m :=
  ⟨(add_sub_cancel_right _ _).symm, fun _ => rfl⟩

end Hon

end Cb.Pv.Lay.End

#print axioms Cb.Pv.Lay.End.honOut_holds
