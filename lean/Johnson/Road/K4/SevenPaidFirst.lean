-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/SevenPaidFirst.lean: THE FIRST GROUP's RECORD OF PUBLIC SIZES `SevenSizesF`
(Johnson/Road/K4/SevenOfLedFirst.lean), PAID FROM `Plan4F.MeetsF`
(Johnson/Road/K4/PlanMapsFirst.lean), at the first group's value with its slots and orders laid
(`Plan4LF.planF`, Johnson/Road/K4/ValueSlotsFirst.lean). One theorem: the twin of `sevenSizes_K`
and `sevenSizes_of_meets` (Johnson/Road/K4/SevenPaid.lean, MeetsCovers.lean), whose heads say where
each field comes from. Made of their text by turning the letters.

  `sevenSizesF_K`: all forty-one fields of `SevenSizesF QF.planF.fullF { par.P with tokv := tk }
    par.hp (lPd - ls) (hS.d / S2) ls`.

Limits. Equations and bounds between numbers alone. `MeetsF` is a premise; the three orders and the
two bounds "at least nine variables" are what `Plan4LF.planF` lays in and its fields h5, h6.

-/
import Johnson.Road.K4.SevenOfLedFirst
import Johnson.Road.K4.PlanClauses
import Johnson.Road.K4.MeetsCovers
import Johnson.Road.K4.PlanMapsFirst
import Johnson.Road.K4.ValueSlotsFirst
import OnBytes.Model.Fit.LayoutCaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (nEndT)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim lDd lF lFe)
open Cb.Pv.Lay.At (kS kS_eq)
open OnBytes.Desc.First.K4 (Par)

variable [scl : Scl] {M X : Type} {QF : Plan4LF Cb.Gl.E M X} {par : Par} {hS : Layer.Shape}
  {pcl : List (List String)}

/-- **The forty-one sizes**, under `MeetsF` at the first group's value with its slots and orders
laid. -/
theorem sevenSizesF_K (A : QF.planF.MeetsF par hS pcl) (tk : Array Nat) :
    SevenSizesF QF.planF.fullF { par.P with tokv := tk } par.hp (par.P.y.lPd - par.P.y.ls)
      (hS.d / par.P.y.S2) par.P.y.ls := by
  have Xd := A.dimIs
  have hp3 : hS.p3 = true := by
    rw [← (laySizes_of_layout A.hy).shape]
    exact (covers_shape A.hc).2.1
  have hxl : hS.xl = 5 := by
    rw [← (laySizes_of_layout A.hy).shape]
    exact (covers_shape A.hc).1
  have L := laySizes_of_layout A.hy
  have Mr := layMore_of_layout A.hy
  have La := Model.Fit.layout_caps A.hy
  obtain ⟨m1, m2, m3⟩ := Fo.readsOf_mu A.hrd
  obtain ⟨n1, n2, n3, n4, _⟩ := norms_sizes A.hy A.Z
  obtain ⟨g1, g2, g3, g4⟩ := gated_sizes A.hy hp3 A.Z
  have xlt : QF.planF.D.lT = par.P.y.h.lt := Xd.lt
  have xlNI : QF.planF.D.lL + 1 = par.P.rd.lNI := Xd.lNI
  have xlPd : lDd QF.planF.D = par.P.y.lPd := Xd.lPd
  have xll : QF.planF.D.lL = par.P.y.h.ll := Xd.ll
  have xlPf : lF QF.planF.D = par.P.y.lPf := Xd.lPf
  have xlfe : lFe QF.planF.D = par.P.y.lfe := Xd.lfe
  have hla : par.P.y.h.la = par.P.y.ls + QF.planF.D.lT := by
    have a := La.ls
    have b := La.laLt
    rw [L.shape, xlt, L.shape]
    omega
  have hNN : par.P.y.NN * par.P.y.Lam = QF.planF.D.nNu := by
    rw [L.NN, L.Lam, nNu_tie A.Z]
  have hLM : par.P.y.LamM = QF.planF.D.ne := L.LamM.trans (ne_tie A.Z).symm
  have hNE : par.P.y.h.NE = QF.planF.D.nx := by
    rw [L.shape]
    exact A.Z.nexp.symm
  exact
    { k1 := by
        show QF.planF.D.lL + 1 + (lDd QF.planF.D + QF.planF.D.lT) = par.P.rd.muV
        omega
      k2 := xlt
      k3 := xlt
      k4 := (kS_eq QF.planF.D).trans Xd.lamS
      k5 := by
        show QF.planF.D.lL + lF QF.planF.D + QF.planF.D.lT = par.P.rd.muH
        omega
      k6 := by
        show QF.planF.D.lL - 1 + (lFe QF.planF.D + QF.planF.D.lT) = par.P.rd.muH2
        omega
      e1 := rfl
      n5 := QF.h5
      e5 := rfl
      n6 := QF.h6
      e6 := rfl
      hls := rfl
      Z := front_sizes A.hy hp3 hxl A.Z
      hB := by
        show par.P.y.h.d / par.P.y.S2 = hS.d / par.P.y.S2
        rw [L.shape]
      h0 := by
        show 0 < QF.planF.D.nNu
        rw [nNu_tie A.Z]
        positivity
      nl := n1
      nd := n2
      nB := n3
      g1 := g1
      gs1 := g2
      gs2 := g3
      gfe := g4
      hNS := Xd.NS.symm
      hNP := Xd.NP.symm
      hNO := Xd.NO.symm
      hEnd := by
        show QF.planF.D.nNu + QF.planF.D.ne + QF.planF.D.ne * QF.planF.D.nx ≤ nEndT par.P.y
        unfold nEndT
        rw [hNN, hLM, hNE, L.shape, hp3, if_pos rfl]
        exact Nat.le_of_eq (by ring)
      hNN := hNN
      hLM := hLM
      hNE := hNE
      hla := hla
      s1 := by
        show par.P.rd.muV = QF.planF.D.lL + 1 + (par.P.y.lPd - par.P.y.ls) + par.P.y.h.la
        omega
      s5 := by
        show par.P.rd.muH = QF.planF.D.lL + lF QF.planF.D - par.P.y.ls + par.P.y.h.la
        omega
      s6 := by
        show par.P.rd.muH2 = QF.planF.D.lL - 1 + lFe QF.planF.D - par.P.y.ls + par.P.y.h.la
        omega
      s2 := xlt.symm
      w1 := by
        show par.P.rd.lNI + par.P.y.lPd - par.P.y.ls =
          QF.planF.D.lL + 1 + (par.P.y.lPd - par.P.y.ls)
        omega
      wP := by
        show par.P.y.Pd = 2 ^ (par.P.y.lPd - par.P.y.ls) * par.P.y.S2
        rw [Mr.Pd, Mr.S2, ← pow_add, Nat.sub_add_cancel n4]
      wS := by
        show 0 < par.P.y.S2
        rw [Mr.S2]
        positivity
      wn := by
        show QF.planF.D.nNu ≤ 2 ^ (QF.planF.D.lL + 1)
        unfold Inst.Model.FFSeg.Dim.nNu Inst.Model.FFSeg.Dim.nl
        rw [pow_succ, Nat.mul_comm]
      w5 := by
        show par.P.y.h.ll + par.P.y.lPf - par.P.y.ls = QF.planF.D.lL + lF QF.planF.D - par.P.y.ls
        omega
      w5s := by
        show par.P.y.Pf / par.P.y.S2 = 2 ^ (lF QF.planF.D - par.P.y.ls)
        rw [Mr.Pf, Mr.S2, xlPf, Nat.pow_div (by omega) (by norm_num)]
      w6 := by
        show par.P.y.h.ll - 1 + par.P.y.lfe - par.P.y.ls =
          QF.planF.D.lL - 1 + lFe QF.planF.D - par.P.y.ls
        omega }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sevenSizesF_K
