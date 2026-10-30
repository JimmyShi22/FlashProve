-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/NumTiesK.lean: THE NUMBERING `numsK` (Johnson/Road/K4/Num4.lean) MEETS THE RECORD
`NumTies` (Johnson/Road/K4/SlotsOfLed.lean), at the ties that are made from it
(`TailM.ofIs`, OnBytes/Desc/First/P1/OwnMapsPlan.lean). One statement, by unfolding.

Limits. Numbers alone. LamM is a letter with the premise that it is the library's number of layers
with routed experts.
-/
import Johnson.Road.K4.Num4
import Johnson.Road.K4.SlotsOfLed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open OnBytes.Desc.First.P1 (TailM TailR TailLens)

variable [scl : Scl] {M X0 : Type} (V : FullPar Cb.Gl.E M X0)

/-- **The ten equations on the numberings.** -/
theorem numTies_K {x : OnBytes.Params.LayerRounds}
    (h : OnBytes.Tie.Pv.Lay.TailIs V.own.toOwn.tail x) {R : TailR} (hl : TailLens R x) {LamM : ℕ}
    (hLam : LamM = V.D.ne) :
    NumTies V (TailM.ofIs h hl (numsK V)) LamM where
  n1f := rfl
  n1t := rfl
  n2 := fun _ => rfl
  n3 := fun _ => rfl
  n4A := rfl
  n4B := by
    subst hLam
    show 2 + V.D.ne = 1 + (1 + V.D.ne)
    omega
  n5f := rfl
  n5t := rfl
  n6f := rfl
  n6t := rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.numTies_K
