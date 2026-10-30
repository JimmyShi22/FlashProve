-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttEnds58ProofsP.lean: a proof of ValueOnEndA (Johnson/Road/Rows/AttEnds58.lean):
the first end value of a pair in the value product's sumcheck on the diagonal tiles.

The way. The verifier reads two planes of the matrix as, the two limbs of the softmax weight, at a
point that it puts together from the sumcheck's point and a part of the lookup's. A plane on the
diagonal tiles, read through the table whose weights are the equality weights of the point's last
coordinates, is the extension of the plane's cells at the point (plane_on). The first map of the
library's step s12 is the extension of the softmax weights at such a point (aext12 in
Cb/Pv/Att/Mean/ReadsOn.lean).

Main theorems: pt_join, plane_on, valueOnEndA.


-/
import Johnson.Road.Rows.AttEnds58
import Johnson.Road.Rows.AttEnds14Tiles
import Cb.Pv.Att.Mean.ReadsOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open Finset
open OnBytes.Model (Reading World Aff Fork SubM HTailF2 eqTab)
open OnBytes.Attention (Shape Heard sc3A lastCoords lastN)
open OnBytes.Road.Hd (Ok)
open Inst.Model.AttSeg (wtV)

variable {K : Type} [Field K]

/-- A coordinate of two points, one after the other. -/
theorem pt_join (ρ : Reading K) (x y : Array E) (j : ℕ) :
    pt ρ (x ++ y) j = if j < x.size then pt ρ x j else pt ρ y (j - x.size) := by
  unfold pt
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split <;> rfl

section Forms

variable {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K} {h : Heard}
  {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-- **A plane on the diagonal tiles**, read at a point z of nD coordinates through the table whose
weights are the equality weights of the last lmS coordinates of z, is the extension of the plane's
cells. -/
theorem plane_on (A : AttAt ρ W tl K3 M h lid cf fs) {F : Fork} (hc : Cols F h K3) {t : ℕ}
    {z : Array E} (Tb : AsAt h t (lastN z h.S.cf.lmS)) (hz : z.size = h.S.nD) {x lam a : ℕ}
    (ha : a < h.S.HA) {q : Aff} {G : Fork} {C D : Ctx}
    (hq : Ok (Attention.plane h t x lam a z true) F C q G D) :
    q.value ρ W =
      Blocks.ext h.S.nD (fun y => cellsK h.S M (.c .D x (lam * h.S.HA + a) y)) (pt ρ z) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hb := pair_parts (lam := lam) ha
  have hle : h.S.cf.lmS ≤ h.S.nD := Z.lmS
  have hleM : h.S.cf.lmS ≤ h.S.nM := by
    have h1 := Z.lmS
    rw [N.nD] at h1
    rw [N.nM]
    omega
  have hsplit : h.S.nD = h.S.nD - h.S.cf.lmS + h.S.cf.lmS := by omega
  obtain ⟨-, -, e⟩ := plane_value A hc Tb hq
  have i0 : (if true = true then h.S.nD else h.S.nM) = h.S.nD := if_pos rfl
  rw [i0] at e
  have s1 : (z.extract 0 (h.S.nD - h.S.cf.lmS)).size = h.S.nD - h.S.cf.lmS := by
    rw [sizeCut _ (by omega)]
    omega
  have s2 : (lastCoords z h.S.cf.lmS).size = h.S.cf.lmS := by
    unfold Attention.lastCoords
    rw [sizeCut _ (Nat.le_refl _)]
    omega
  rw [e, eqTab_size, s1]
  conv_rhs => rw [hsplit, Blocks.ext_two]
  refine sum_congr rfl fun hi hhi => ?_
  rw [mul_sum]
  refine sum_congr rfl fun lo hlo => ?_
  have w1 : ρ.val ((eqTab (z.extract 0 (h.S.nD - h.S.cf.lmS))).getD hi zeroE) =
      Blocks.eqN (h.S.nD - h.S.cf.lmS) 0 (pt ρ z) hi :=
    eqTab_at ρ s1 (fun j hj => by
      rw [ptCut ρ z (by omega) (by omega), Nat.zero_add]) (mem_range.mp hhi)
  have w2 : ρ.val ((lastN z h.S.cf.lmS).getD lo zeroE) =
      Blocks.eqN h.S.cf.lmS (h.S.nD - h.S.cf.lmS) (pt ρ z) lo := by
    unfold Attention.lastN
    rw [eqTab_at ρ s2 (v := Inst.Model.AttSeg.sh (pt ρ z) (h.S.nD - h.S.cf.lmS)) (fun j hj => by
      unfold Attention.lastCoords
      rw [ptCut ρ z (Nat.le_refl _) (by omega), hz]
      rfl) (mem_range.mp hlo), eqN_sh]
  have c1 : (planeFirst h.S x lam a true >>> h.S.cf.lmS + hi) * 2 ^ h.S.cf.lmS + lo =
      5 * h.S.Lam * h.S.HA * 2 ^ h.S.nM + ((x * h.S.Lam + lam) * h.S.HA + a) * 2 ^ h.S.nD +
        (hi * 2 ^ h.S.cf.lmS + lo) := by
    have p1 : planeFirst h.S x lam a true =
        5 * h.S.Lam * h.S.HA * 2 ^ h.S.nM + ((x * h.S.Lam + lam) * h.S.HA + a) * 2 ^ h.S.nD := by
      unfold planeFirst
      rw [if_pos rfl, if_pos rfl, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    have p2 : 2 ^ h.S.nD = 2 ^ (h.S.nD - h.S.cf.lmS) * 2 ^ h.S.cf.lmS := by
      rw [← pow_add, ← hsplit]
    have p3 : 2 ^ h.S.nM = 2 ^ (h.S.nM - h.S.cf.lmS) * 2 ^ h.S.cf.lmS := by
      rw [← pow_add]
      congr 1
      omega
    rw [p1, Nat.shiftRight_eq_div_pow, p2, p3, ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.add_mul,
      Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    ring
  rw [w1, w2, c1]
  show _ = _ * mAt M (L5.asCell h.S (5 * h.S.Lam * h.S.HA * 2 ^ h.S.nM +
    ((x * h.S.Lam + (lam * h.S.HA + a) / h.S.HA) * h.S.HA + (lam * h.S.HA + a) % h.S.HA) *
      2 ^ h.S.nD + (hi * 2 ^ h.S.cf.lmS + lo)))
  rw [hb.1, hb.2]
  ring

end Forms

/-- **ValueOnEndA holds.** -/
theorem valueOnEndA : ValueOnEndA := by
  intro K _ ρ W tl K3 M h F lid cf fs C p b w p3 p4 G G' c c1 c' c1' A hc hr hzi ha _ hpt hyi TbS
    h3 h4 vA
  have N := norm_of_hid A.shape
  have P := L5.shaped_of_hid A.shape
  obtain ⟨S0, hS0⟩ := L5.shape_of_hid A.shape
  have ht := (L5.tested_of_shape hS0).1
  have hn : h.S.lnT - 1 + 1 = h.S.lnT := by
    have := P.lnT
    omega
  have hlt := N.lt
  have hr' : h.d.vpd.r.size = h.S.cf.lgk + h.S.lnT + h.S.cf.lB := hr
  have s1 : (sc3A h.d.vpd b).value ρ W = W.slot (h.d.vpd.sEnd + 2 * b) := Aff.value_slot ρ W _
  have q1 : (h.d.vpd.r.extract 0 (h.S.cf.lgk + h.S.lnT)).size = h.S.cf.lgk + h.S.lnT := by
    rw [sizeCut _ (by omega)]
    omega
  have q2 : (h.d.zilo h.S).size = h.S.cf.lB := by
    unfold Attention.Divide.zilo
    rw [sizeCut _ (by omega)]
    omega
  have q3 : (lastCoords h.d.vpd.r h.S.cf.lB).size = h.S.cf.lB := by
    unfold Attention.lastCoords
    rw [sizeCut _ (Nat.le_refl _)]
    omega
  have hsz : h.t.ptD.size = h.S.nD := by
    rw [hpt, N.nD]
    unfold Attention.pointD
    rw [Array.size_append, Array.size_append, q1, q2, q3]
    omega
  have e3 := plane_on A hc TbS hsz ha (ok_of_yields h3)
  have e4 := plane_on A hc TbS hsz ha (ok_of_yields h4)
  rw [Aff.value_sub, s1, Aff.value_add, Aff.value_add, Aff.value_ofConst, Aff.value_scale,
    A.num.ofNat, A.num.ofNat, e3, e4, sub_eq_zero] at vA
  have pd : ∀ j, pt ρ h.t.ptD j =
      if j < h.S.cf.lgk + h.S.lnT + h.S.cf.lB then
        (if j < h.S.cf.lgk + h.S.lnT then pt ρ (h.d.vpd.r.extract 0 (h.S.cf.lgk + h.S.lnT)) j
          else pt ρ (h.d.zilo h.S) (j - (h.S.cf.lgk + h.S.lnT)))
      else pt ρ (lastCoords h.d.vpd.r h.S.cf.lB) (j - (h.S.cf.lgk + h.S.lnT + h.S.cf.lB)) := by
    intro j
    rw [hpt]
    unfold Attention.pointD
    rw [pt_join, Array.size_append, q1, q2, pt_join, q1]
  rw [vA, aext12 (L5.dimOf h.S) C p (cellsK h.S M) (w.lam * h.S.HA + w.a) (pt ρ h.d.vpd.r)
    (pt ρ h.t.ptD)
    (fun k hk => by
      have hk' : k < h.S.cf.lgk + (h.S.lnT - 1 + 1) := hk
      rw [pd, if_pos (by omega), if_pos (by omega), ptCut ρ _ (by omega) (by omega),
        Nat.zero_add])
    (fun k hk => by
      have hk' : k < h.S.cf.lB := hk
      show pt ρ h.t.ptD (h.S.cf.lgk + (h.S.lnT - 1 + 1) + k) = _
      rw [pd, if_pos (by omega), if_neg (by omega), ← hyi k hk']
      exact congrArg _ (by omega))
    (fun k hk => by
      have hk' : k < h.S.cf.lB := hk
      show pt ρ h.t.ptD (h.S.cf.lgk + (h.S.lnT - 1 + 1) + h.S.cf.lB + k) =
        pt ρ h.d.vpd.r (h.S.cf.lgk + (h.S.lnT - 1 + 1) + k)
      rw [pd, if_neg (by omega)]
      unfold Attention.lastCoords
      rw [ptCut ρ _ (Nat.le_refl _) (by omega)]
      exact congrArg _ (by omega))]
  have hD : (L5.dimOf h.S).lD = h.S.nD := N.nD.symm
  rw [hD]
  have hw : wtV (cellsK h.S M) .D (w.lam * h.S.HA + w.a) = fun y =>
      (cellsK h.S M (.c .D 3 (w.lam * h.S.HA + w.a) y) + 128) +
        256 * cellsK h.S M (.c .D 4 (w.lam * h.S.HA + w.a) y) := rfl
  rw [hw, Blocks.ext_add, Blocks.ext_add, Blocks.ext_const, Blocks.ext_smul]
  push_cast
  ring

end OnBytes.Road.Rows
