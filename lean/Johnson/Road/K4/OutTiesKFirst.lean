-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OutTiesKFirst.lean: THE FIRST GROUP's TWIN OF Johnson/Road/K4/OutTiesK.lean: THE
RECORD OF PUBLIC TIES `OutTiesF` (Johnson/Road/K4/StageOutsAllFirst.lean), PAID FROM
`Plan4F.MeetsF` (Johnson/Road/K4/PlanMapsFirst.lean) AND THE RETURN OF THE BATCHED SUMCHECK's
HEARING, at the first group's value with its slots and orders laid (`Plan4LF.planF`,
Johnson/Road/K4/ValueSlotsFirst.lean). One theorem.

  `outTies_KF`: all twenty fields. OutTiesK.lean's proof at these letters; its small statements
    (`stack_wD`, `stack_rs_size`, `wide5`, `wide6`) speak of no group and are taken as they stand.

Where the fields come from: the head of OutTiesK.lean.

Limits. Equations and bounds between numbers. `MeetsF` and the hearing's return are premises.

-/
import Johnson.Road.K4.OutTiesK
import Johnson.Road.K4.StageOutsAllFirst
import Johnson.Road.K4.ValueSlotsFirst
import Johnson.Road.K4.PlanMapsFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model
open OnBytes.Model.Layer (Own)
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd lF lFe)
open Cb.Pv.Lay.At (kS kS_eq)
open OnBytes.Desc.First.K4 (Par hearStack engFl)

variable [scl : Scl] {M X : Type} {QF : Plan4LF Cb.Gl.E M X} {par : Par} {hS : Layer.Shape}
  {pcl : List (List String)}

/-- **The twenty public ties**, under `MeetsF` at the first group's value with its slots and orders
laid, where the batched sumcheck's hearing returns K4's record. -/
theorem outTies_KF (A : QF.planF.MeetsF par hS pcl) (tk : Array Nat) {o : Own} {NCLp : ℕ}
    {G2 G3 : Fork} {t u : Tape}
    (c4 : hearStack engFl { par.P with tokv := tk } o.v o.H par.hp.lamS NCLp G2 t =
      some (o.K, G3, u)) :
    OutTiesF QF.planF.fullF { par.P with tokv := tk } par.hp o := by
  have Xd := A.dimIs
  obtain ⟨m1, m2, m3⟩ := Fo.readsOf_mu A.hrd
  have xlt : QF.planF.D.lT = par.P.y.h.lt := Xd.lt
  have xlNI : QF.planF.D.lL + 1 = par.P.rd.lNI := Xd.lNI
  have xlPd : lDd QF.planF.D = par.P.y.lPd := Xd.lPd
  have xll : QF.planF.D.lL = par.P.y.h.ll := Xd.ll
  have xlPf : lF QF.planF.D = par.P.y.lPf := Xd.lPf
  have xlfe : lFe QF.planF.D = par.P.y.lfe := Xd.lfe
  have xk : kS QF.planF.D = par.hp.lamS := (kS_eq QF.planF.D).trans Xd.lamS
  exact
    { eS := rfl
      n5 := QF.h5
      e5 := rfl
      n6 := QF.h6
      e6 := rfl
      m1 := by
        show QF.planF.D.lL + 1 + (lDd QF.planF.D + QF.planF.D.lT) = par.P.rd.muV
        omega
      lt := xlt
      k4 := xk
      m5 := by
        show QF.planF.D.lL + lF QF.planF.D + QF.planF.D.lT = par.P.rd.muH
        omega
      m6 := by
        show QF.planF.D.lL - 1 + (lFe QF.planF.D + QF.planF.D.lT) = par.P.rd.muH2
        omega
      k7 := A.wk
      lI := xlNI
      lP := xlPd
      lfe := xlfe.symm
      ll := by
        show par.P.y.h.ll - 1 = QF.planF.D.lL - 1
        omega
      wD := by
        have e := stack_wD c4
        show o.K.fin.wD = QF.planF.D.lL + lF QF.planF.D
        rw [e]
        show par.P.y.h.ll + par.P.y.lPf = _
        omega
      le5 := wide5 QF.planF.D
      le6 := wide6 QF.planF.D QF.hfe
      rs := by
        show kS QF.planF.D ≤ o.K.rs.size
        rw [stack_rs_size c4, xk]
      half := eq_inv_of_mul_eq_one_left gl_half }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.outTies_KF
