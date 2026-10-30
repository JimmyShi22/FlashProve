-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/NumTiesKFirst.lean: THE NUMBERINGS OF THE SEVEN SUMCHECKS' END VALUES IN THE FIRST
GROUP, in the order in which K4's text hears them, and the ten equations `NumTiesF`
(Johnson/Road/K4/SlotsOfLedFirst.lean) at them. The twin of `numsK` (Johnson/Road/K4/Num4.lean) and
`numTies_K` (Johnson/Road/K4/NumTiesK.lean). A definition and one statement.

  `numsKF Pf`: the same seven numberings as `numsK`, at the first group's chain `tailW Pf`: its six
    first stages have the later groups' names of end values; the merge has one.
  `numTiesF_K`: `NumTiesF Pf (TailM.ofIs h hl (numsKF Pf)) LamM`, where LamM is the library's number
    of layers with routed experts.

Limits. Equations on numberings, nine of them by definition.
-/
import Johnson.Road.K4.Num4
import Johnson.Road.K4.SlotsOfLedFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open Inst.Model (Scl)
open OnBytes.Desc.First.P1 (TailM TailR TailLens TailNums)

variable [scl : Scl] {M X0 : Type} (Pf : FullFPar Cb.Gl.E M X0)

/-- **The numberings of all seven sumchecks' end values, in the first group.** -/
noncomputable def numsKF : TailNums (tailW Pf) where
  n1 := fun b : Bool => if b then 1 else 0
  n2 := fun q : Fin Pf.D.nNu × Fin 4 => (finProdFinEquiv q : ℕ)
  n3 := Cb.Pv.Lay.End.numA Pf.D
  n4 := num4K Pf.toFullPar
  n5 := fun b : Bool => if b then 1 else 0
  n6 := fun b : Bool => if b then 1 else 0
  n7 := fun _ => 0

/-- **The ten equations on the numberings.** -/
theorem numTiesF_K {x : OnBytes.Params.LayerRounds}
    (h : OnBytes.Tie.Pv.Lay.TailIs (tailW Pf) x) {R : TailR} (hl : TailLens R x) {LamM : ℕ}
    (hLam : LamM = Pf.D.ne) :
    NumTiesF Pf (TailM.ofIs h hl (numsKF Pf)) LamM where
  n1f := rfl
  n1t := rfl
  n2 := fun _ => rfl
  n3 := fun _ => rfl
  n4A := rfl
  n4B := by
    subst hLam
    show 2 + Pf.D.ne = 1 + (1 + Pf.D.ne)
    omega
  n5f := rfl
  n5t := rfl
  n6f := rfl
  n6t := rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.numTiesF_K
