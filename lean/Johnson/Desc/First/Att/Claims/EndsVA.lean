-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/EndsVA.lean: kind K5: the planes, and the value product's first end
values on the diagonal tiles: twins, for the written forms, of plane_value
(Johnson/Road/Rows/AttReadLong.lean), plane_on and ValueOnEndA
(Johnson/Road/Rows/AttEnds58ProofsP.lean, AttEnds58.lean), which speak of a run of a routine in a
context. The proofs' pure parts follow those proofs line for line.

Main names:
  `planeF_rd`: the written form of plane, as the double sum over the plane's columns and a column's
    rows, on the cells at the addresses of L5.asCell.
  `planeF_on`: a plane on the diagonal tiles, read at a point z of nD coordinates through the table
    whose weights are the equality weights of z's last lmS coordinates, is the extension of the
    plane's cells.
  `value_on_A`: W.slot (vpd.sEnd + 2 b) = Aext (L5.dimOf h.S) C p (cellsK h.S M) .s12 (w.lam HA +
    w.a) (pt ρ vpd.r): the softmax weight.
What these reach, and what not: as the head of Johnson/Desc/First/Att/Claims/EndsQ.lean says.
Premise beyond those of Johnson/Road/Rows: the indices read lie in the table.
Used: as Johnson/Desc/First/Att/Claims/EndsQ.lean, and AsAt, as_read, Rows.planeFirst, L5.asCell,
pt_join, sizeCut, ptCut, eqTab_at, eqN_sh, Blocks.ext_two, ext_add, ext_const, ext_smul, aext12,
Attention.lastN, lastCoords, pointD, Divide.zilo; the library's Aext, wtV, yi'.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttEnds58ProofsP
import Johnson.Desc.First.Att.Claims.EndsV

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Cb.Pv.Att
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Road.Hd (rdW)
open Inst.Model.AttSeg (Calls Pub wtV Aext)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K3 : ℕ} {M : Mats Kf}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-- **The written form of plane**: a sum over the columns hi of the plane and the rows lo of a column. -/
theorem planeF_rd (A : AttAt ρ W tl K3 M h lid cf fs) {t : ℕ} {phi : Array E} (Tb : AsAt h t phi)
    {x lam a : ℕ} {z : Array E} {isD : Bool}
    (hin : ∀ hi < (eqTab (z.extract 0 ((if isD then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
      Rows.planeFirst h.S x lam a isD >>> h.S.cf.lmS + hi < (h.t.tabLen.lookup t).getD 0) :
    (Fo.planeF h K3 t x lam a z isD).value ρ W =
      ∑ hi ∈ range
          (eqTab (z.extract 0 ((if isD then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
        ρ.val ((eqTab (z.extract 0 ((if isD then h.S.nD else h.S.nM) - h.S.cf.lmS))).getD hi
          zeroE) *
          ∑ lo ∈ range (2 ^ h.S.cf.lmS), ρ.val (phi.getD lo zeroE) *
            mAt M (L5.asCell h.S
              ((Rows.planeFirst h.S x lam a isD >>> h.S.cf.lmS + hi) * 2 ^ h.S.cf.lmS + lo)) := by
  rw [planeF_value, list_sum_range]
  refine sum_congr rfl fun hi hhi => ?_
  congr 1
  show rdW W h.iU3 K3 (t + (Rows.planeFirst h.S x lam a isD >>> h.S.cf.lmS + hi)) = _
  rw [as_read A Tb (hin hi (mem_range.mp hhi))]
  refine sum_congr rfl fun lo hlo => ?_
  have hP : 0 < 2 ^ h.S.cf.lmS := Nat.two_pow_pos _
  have d1 : ∀ n : ℕ, (n * 2 ^ h.S.cf.lmS + lo) / 2 ^ h.S.cf.lmS = n := fun n => by
    rw [Nat.mul_comm, Nat.mul_add_div hP, Nat.div_eq_of_lt (mem_range.mp hlo), Nat.add_zero]
  have d2 : ∀ n : ℕ, (n * 2 ^ h.S.cf.lmS + lo) % 2 ^ h.S.cf.lmS = lo := fun n => by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (mem_range.mp hlo)]
  show _ = _ * M _ _ _
  unfold L5.asCell
  simp only [d1, d2]

/-- **A plane on the diagonal tiles is the extension of the plane's cells.** -/
theorem planeF_on (A : AttAt ρ W tl K3 M h lid cf fs) {t : ℕ} {z : Array E}
    (Tb : AsAt h t (lastN z h.S.cf.lmS)) (hz : z.size = h.S.nD) {x lam a : ℕ} (ha : a < h.S.HA)
    (hin : ∀ hi < (eqTab (z.extract 0 ((if true then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
      Rows.planeFirst h.S x lam a true >>> h.S.cf.lmS + hi < (h.t.tabLen.lookup t).getD 0) :
    (Fo.planeF h K3 t x lam a z true).value ρ W =
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
  have e := planeF_rd A Tb hin
  have i0 : (if true = true then h.S.nD else h.S.nM) = h.S.nD := if_pos rfl
  rw [i0] at e
  have s1 : (z.extract 0 (h.S.nD - h.S.cf.lmS)).size = h.S.nD - h.S.cf.lmS := by
    rw [sizeCut _ (by omega)]
    omega
  have s2 : (lastCoords z h.S.cf.lmS).size = h.S.cf.lmS := by
    unfold Attention.lastCoords
    rw [sizeCut _ (Nat.le_refl _)]
    omega
  rw [e, OnBytes.Road.eqTab_size, s1]
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
  have c1 : (Rows.planeFirst h.S x lam a true >>> h.S.cf.lmS + hi) * 2 ^ h.S.cf.lmS + lo =
      5 * h.S.Lam * h.S.HA * 2 ^ h.S.nM + ((x * h.S.Lam + lam) * h.S.HA + a) * 2 ^ h.S.nD +
        (hi * 2 ^ h.S.cf.lmS + lo) := by
    have p1 : Rows.planeFirst h.S x lam a true =
        5 * h.S.Lam * h.S.HA * 2 ^ h.S.nM + ((x * h.S.Lam + lam) * h.S.HA + a) * 2 ^ h.S.nD := by
      unfold Rows.planeFirst
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

/-- **The twin of ValueOnEndA.** -/
theorem value_on_A (A : AttAt ρ W tl K3 M h lid cf fs) (C : Calls) (p : Pub Kf) {b : ℕ} {w : PW}
    (hr : h.d.vpd.r.size = h.S.nvVD) (hzi : h.d.ziW.size = h.S.cf.lt) (ha : w.a < h.S.HA)
    (hpt : h.t.ptD = pointD h.S h.d)
    (hyi : ∀ j < h.S.cf.lB, pt ρ (h.d.zilo h.S) j = Inst.Model.AttSeg.yi' (L5.dimOf h.S) C p.z j)
    (TbS : AsAt h h.t.tVD (lastN h.t.ptD h.S.cf.lmS))
    (hin : ∀ x, x = 3 ∨ x = 4 →
      ∀ hi < (eqTab (h.t.ptD.extract 0 ((if true then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
        Rows.planeFirst h.S x w.lam w.a true >>> h.S.cf.lmS + hi < (h.t.tabLen.lookup h.t.tVD).getD 0)
    (vA : W.slot (h.d.vpd.sEnd + 2 * b) = (Fo.planeF h K3 h.t.tVD 3 w.lam w.a h.t.ptD true +
      Aff.ofConst (ofNat 128) + Aff.scale (Fo.planeF h K3 h.t.tVD 4 w.lam w.a h.t.ptD true)
        (ofNat 256)).value ρ W) :
    W.slot (h.d.vpd.sEnd + 2 * b) =
      Aext (L5.dimOf h.S) C p (cellsK h.S M) .s12 (w.lam * h.S.HA + w.a) (pt ρ h.d.vpd.r) := by
  have N := norm_of_hid A.shape
  have P := L5.shaped_of_hid A.shape
  obtain ⟨S0, hS0⟩ := L5.shape_of_hid A.shape
  have ht := (L5.tested_of_shape hS0).1
  have hn : h.S.lnT - 1 + 1 = h.S.lnT := by
    have := P.lnT
    omega
  have hlt := N.lt
  have hr' : h.d.vpd.r.size = h.S.cf.lgk + h.S.lnT + h.S.cf.lB := hr
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
  have e3 := planeF_on A TbS hsz ha (hin 3 (.inl rfl))
  have e4 := planeF_on A TbS hsz ha (hin 4 (.inr rfl))
  rw [Aff.value_add, Aff.value_add, Aff.value_ofConst, Aff.value_scale,
    A.num.ofNat, A.num.ofNat, e3, e4] at vA
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

end K5Law
