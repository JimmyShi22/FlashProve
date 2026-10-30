-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/SevenPaid.lean: THE RECORD OF PUBLIC SIZES `SevenSizes`
(Johnson/Road/K4/SevenSizes.lean), PAID FROM `Plan4.Meets` (Johnson/Road/K4/PlanMaps.lean), at the
value with its slots and orders laid (`Plan4L.plan`, Johnson/Road/K4/ValueSlots.lean), for a shape
with routed experts and five limbs. One theorem.

  `sevenSizes_K`: all forty-one fields of `SevenSizes QL.plan.full { par.P with tokv := tk } par.hp
    (lPd - ls) (hS.d / S2) ls`.

WHERE EACH FIELD COMES FROM. The stages' numbers of rounds, the sums', products' and shown values'
numbers: `DimIs` (`Plan4.Meets.dimIs`) and `Fo.readsOf_mu`. THE THREE ORDERS AND THE TWO
BOUNDS "at least nine variables" (e1 n5 e5 n6 e6) ARE NOT TAKEN FROM `Meets` HERE: they are what
`Plan4L.plan` lays in, and its fields h5 and h6: at a bare `Plan4` the orders are letters. The two
bounds are no open debt: by reading, `readsOf` refuses fewer than nine variables in a product
layer (its test "shape-product-layer", OnBytes/Model/LayerLayout.lean), so where `Meets` holds they
hold; no lemma says so yet. The seven front sizes, the norms' three and the gated layers' four
clauses: `front_sizes`, `norms_sizes`, `gated_sizes` (PlanClauses.lean). The bits of a feature in
its block: `layout_caps` (OnBytes/Model/Fit/LayoutCaps.lean). The rest: arithmetic on
`LaySizes` and `LayMore`.

Limits. Equations and bounds between numbers alone. That `Meets` holds at a run's place, and h5, h6,
are premises. That the shape has routed experts and five limbs is a premise here and follows from
`Meets` (Johnson/Road/K4/MeetsCovers.lean).
-/
import Johnson.Road.K4.SevenSizes
import Johnson.Road.K4.PlanClauses
import Johnson.Road.K4.ClaimsPaid
import Johnson.Road.K4.ValueSlots
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

variable [scl : Scl] {M X : Type} {QL : Plan4L Cb.Gl.E M X} {par : Par} {hS : Layer.Shape}
  {pcl : List (List String)}

/-- **The forty-one sizes**, under `Meets` at the value with its slots and orders laid, for a shape
with routed experts and five limbs. -/
theorem sevenSizes_K (A : QL.plan.Meets par hS pcl) (hp3 : hS.p3 = true) (hxl : hS.xl = 5)
    (tk : Array Nat) :
    SevenSizes QL.plan.full { par.P with tokv := tk } par.hp (par.P.y.lPd - par.P.y.ls)
      (hS.d / par.P.y.S2) par.P.y.ls := by
  have Xd := A.dimIs
  have L := laySizes_of_layout A.hy
  have Mr := layMore_of_layout A.hy
  have La := Model.Fit.layout_caps A.hy
  obtain ⟨m1, m2, m3⟩ := Fo.readsOf_mu A.hrd
  obtain ⟨n1, n2, n3, n4, _⟩ := norms_sizes A.hy A.Z
  obtain ⟨g1, g2, g3, g4⟩ := gated_sizes A.hy hp3 A.Z
  have xlt : QL.plan.D.lT = par.P.y.h.lt := Xd.lt
  have xlNI : QL.plan.D.lL + 1 = par.P.rd.lNI := Xd.lNI
  have xlPd : lDd QL.plan.D = par.P.y.lPd := Xd.lPd
  have xll : QL.plan.D.lL = par.P.y.h.ll := Xd.ll
  have xlPf : lF QL.plan.D = par.P.y.lPf := Xd.lPf
  have xlfe : lFe QL.plan.D = par.P.y.lfe := Xd.lfe
  have hla : par.P.y.h.la = par.P.y.ls + QL.plan.D.lT := by
    have a := La.ls
    have b := La.laLt
    rw [L.shape, xlt, L.shape]
    omega
  have hNN : par.P.y.NN * par.P.y.Lam = QL.plan.D.nNu := by
    rw [L.NN, L.Lam, nNu_tie A.Z]
  have hLM : par.P.y.LamM = QL.plan.D.ne := A.lamM tk
  have hNE : par.P.y.h.NE = QL.plan.D.nx := by
    rw [L.shape]
    exact A.Z.nexp.symm
  exact
    { k1 := by
        show QL.plan.D.lL + 1 + (lDd QL.plan.D + QL.plan.D.lT) = par.P.rd.muV
        omega
      k2 := xlt
      k3 := xlt
      k4 := (kS_eq QL.plan.D).trans Xd.lamS
      k5 := by
        show QL.plan.D.lL + lF QL.plan.D + QL.plan.D.lT = par.P.rd.muH
        omega
      k6 := by
        show QL.plan.D.lL - 1 + (lFe QL.plan.D + QL.plan.D.lT) = par.P.rd.muH2
        omega
      e1 := rfl
      n5 := QL.h5
      e5 := rfl
      n6 := QL.h6
      e6 := rfl
      hls := rfl
      Z := front_sizes A.hy hp3 hxl A.Z
      hB := by
        show par.P.y.h.d / par.P.y.S2 = hS.d / par.P.y.S2
        rw [L.shape]
      h0 := by
        show 0 < QL.plan.D.nNu
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
        show QL.plan.D.nNu + QL.plan.D.ne + QL.plan.D.ne * QL.plan.D.nx ≤ nEndT par.P.y
        unfold nEndT
        rw [hNN, hLM, hNE, L.shape, hp3, if_pos rfl]
        exact Nat.le_of_eq (by ring)
      hNN := hNN
      hLM := hLM
      hNE := hNE
      hla := hla
      s1 := by
        show par.P.rd.muV = QL.plan.D.lL + 1 + (par.P.y.lPd - par.P.y.ls) + par.P.y.h.la
        omega
      s5 := by
        show par.P.rd.muH = QL.plan.D.lL + lF QL.plan.D - par.P.y.ls + par.P.y.h.la
        omega
      s6 := by
        show par.P.rd.muH2 = QL.plan.D.lL - 1 + lFe QL.plan.D - par.P.y.ls + par.P.y.h.la
        omega
      s2 := xlt.symm
      w1 := by
        show par.P.rd.lNI + par.P.y.lPd - par.P.y.ls =
          QL.plan.D.lL + 1 + (par.P.y.lPd - par.P.y.ls)
        omega
      wP := by
        show par.P.y.Pd = 2 ^ (par.P.y.lPd - par.P.y.ls) * par.P.y.S2
        rw [Mr.Pd, Mr.S2, ← pow_add, Nat.sub_add_cancel n4]
      wS := by
        show 0 < par.P.y.S2
        rw [Mr.S2]
        positivity
      wn := by
        show QL.plan.D.nNu ≤ 2 ^ (QL.plan.D.lL + 1)
        unfold Inst.Model.FFSeg.Dim.nNu Inst.Model.FFSeg.Dim.nl
        rw [pow_succ, Nat.mul_comm]
      w5 := by
        show par.P.y.h.ll + par.P.y.lPf - par.P.y.ls = QL.plan.D.lL + lF QL.plan.D - par.P.y.ls
        omega
      w5s := by
        show par.P.y.Pf / par.P.y.S2 = 2 ^ (lF QL.plan.D - par.P.y.ls)
        rw [Mr.Pf, Mr.S2, xlPf, Nat.pow_div (by omega) (by norm_num)]
      w6 := by
        show par.P.y.h.ll - 1 + par.P.y.lfe - par.P.y.ls =
          QL.plan.D.lL - 1 + lFe QL.plan.D - par.P.y.ls
        omega }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sevenSizes_K
