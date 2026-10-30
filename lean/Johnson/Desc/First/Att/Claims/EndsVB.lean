-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/EndsVB.lean: kind K5: the value product below the diagonal: twins, for
the written forms, of plane_below and ValueBelowEnd (Johnson/Road/Rows/AttEnds14Below.lean,
AttEnds14.lean), which speak of a run of a routine in a context.

Main names:
  `planeF_below`: a plane below the diagonal, read at a point z of nM coordinates through the table
    whose weights are the equality weights of z's last lmS coordinates, is the extension of the
    plane's cells.
  `value_below`: W.slot (vpm.sEnd + 2 b) = Aext … .s11 (w.lam HA + w.a) (pt ρ vpm.r) ∧ W.slot
    (vpm.sEnd + (2 b + 1)) = Bext … .s11 ….
The two proofs' texts are those of Johnson/Road/Rows/AttEnds14Below.lean, turned in nine places: the
run's lemma to the written form's (plane_value → planeF_rd, plane_below → planeF_below,
readGroup_val → readGroupT_val), the claims "slot − form is worth 0" to the equations "slot = form's
worth" that Johnson/Desc/First/Att/Claims/Say58.lean gives, two short names to full ones, the
field's letter.
What these reach, and what not: as the head of Johnson/Desc/First/Att/Claims/EndsQ.lean says.
Premises beyond those of Johnson/Road/Rows: the indices read lie in the tables; the heads' features
are lawful (InLong).
Used: as Johnson/Desc/First/Att/Claims/EndsVA.lean and Johnson/Desc/First/Att/Claims/EndsE.lean, and
pt_append, eqN_shift', aext11, bext11, ptBelow, Blocks.ext_congr_point, tiles_col, tok_psi and what
else that proof's pure part names; Attention.pointM, tileSums.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttEnds14Below
import Johnson.Desc.First.Att.Claims.EndsVA
import Johnson.Desc.First.Att.Claims.EndsE

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Cb.Pv.Att
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Calls Pub rd3 sh valV wtV Aext Bext cat)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K3 : ℕ} {M : Mats Kf}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-- **A plane below the diagonal is the extension of the plane's cells.** -/
theorem planeF_below (A : AttAt ρ W tl K3 M h lid cf fs) {t : ℕ} {z : Array E}
    (Tb : AsAt h t (lastN z h.S.cf.lmS)) (hz : z.size = h.S.nM) {x lam a : ℕ} (ha : a < h.S.HA)
    (hin : ∀ hi < (eqTab (z.extract 0 ((if false then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
      Rows.planeFirst h.S x lam a false >>> h.S.cf.lmS + hi < (h.t.tabLen.lookup t).getD 0) :
    (Fo.planeF h K3 t x lam a z false).value ρ W =
      Blocks.ext h.S.nM (fun y => cellsK h.S M (.c .M x (lam * h.S.HA + a) y)) (pt ρ z) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hb := pair_parts (lam := lam) ha
  have hle : h.S.cf.lmS ≤ h.S.nM := by
    have h1 := Z.lmS
    rw [N.nD] at h1
    rw [N.nM]
    omega
  have hsplit : h.S.nM = h.S.nM - h.S.cf.lmS + h.S.cf.lmS := by omega
  have e := planeF_rd A Tb hin
  have i0 : (if false = true then h.S.nD else h.S.nM) = h.S.nM := if_neg (by decide)
  rw [i0] at e
  have s1 : (z.extract 0 (h.S.nM - h.S.cf.lmS)).size = h.S.nM - h.S.cf.lmS := by
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
  have w1 : ρ.val ((eqTab (z.extract 0 (h.S.nM - h.S.cf.lmS))).getD hi zeroE) =
      Blocks.eqN (h.S.nM - h.S.cf.lmS) 0 (pt ρ z) hi :=
    eqTab_at ρ s1 (fun j hj => by
      rw [ptCut ρ z (by omega) (by omega), Nat.zero_add]) (mem_range.mp hhi)
  have w2 : ρ.val ((lastN z h.S.cf.lmS).getD lo zeroE) =
      Blocks.eqN h.S.cf.lmS (h.S.nM - h.S.cf.lmS) (pt ρ z) lo := by
    unfold Attention.lastN
    rw [eqTab_at ρ s2 (v := fun j => pt ρ z (h.S.nM - h.S.cf.lmS + j)) (fun j hj => by
      unfold Attention.lastCoords
      rw [ptCut ρ z (Nat.le_refl _) (by omega), hz]) (mem_range.mp hlo), eqN_shift']
  have c1 : (Rows.planeFirst h.S x lam a false >>> h.S.cf.lmS + hi) * 2 ^ h.S.cf.lmS + lo =
      ((x * h.S.Lam + lam) * h.S.HA + a) * 2 ^ h.S.nM + (hi * 2 ^ h.S.cf.lmS + lo) := by
    have p1 : Rows.planeFirst h.S x lam a false = ((x * h.S.Lam + lam) * h.S.HA + a) * 2 ^ h.S.nM := by
      unfold Rows.planeFirst
      rw [if_neg (by decide), if_neg (by decide), Nat.zero_add, Nat.shiftLeft_eq]
    have p2 : 2 ^ h.S.nM = 2 ^ (h.S.nM - h.S.cf.lmS) * 2 ^ h.S.cf.lmS := by
      rw [← pow_add, ← hsplit]
    rw [p1, Nat.shiftRight_eq_div_pow, p2, ← Nat.mul_assoc,
      Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    ring
  rw [w1, w2, c1]
  show _ = _ * mAt M (L5.asCell h.S
    (((x * h.S.Lam + (lam * h.S.HA + a) / h.S.HA) * h.S.HA + (lam * h.S.HA + a) % h.S.HA) *
      2 ^ h.S.nM + (hi * 2 ^ h.S.cf.lmS + lo)))
  rw [hb.1, hb.2]
  ring

/-- **The twin of ValueBelowEnd.** -/
theorem value_below (A : AttAt ρ W tl K3 M h lid cf fs) (C : Calls) (p : Pub Kf) {b : ℕ} {w : PW}
    (hr : h.d.vpm.r.size = h.S.nvVM) (hzi : h.d.ziW.size = h.S.cf.lt) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (ha : w.a < h.S.HA) (hpt : h.t.ptM = pointM h.S h.d)
    (hwJ : h.d.wJv = (tileSums h.S
      (eqTab (h.d.vpm.r.extract h.S.cf.lgk (h.S.cf.lgk + (h.S.lnT - 1))))
      (eqTab (h.d.vpm.r.extract (h.S.cf.lgk + (h.S.lnT - 1))
        (h.S.cf.lgk + (h.S.lnT - 1) + h.S.lnT)))).2)
    (hyi : ∀ j < h.S.cf.lB, pt ρ (h.d.zilo h.S) j = Inst.Model.AttSeg.yi' (L5.dimOf h.S) C p.z j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = Inst.Model.AttSeg.yn (L5.dimOf h.S) C p.z j)
    (hgam : ρ.val h.d.gam = p.th)
    (TbS : AsAt h h.t.tVM (lastN h.t.ptM h.S.cf.lmS))
    (TbV : TabAt tl h h.t.qVM (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
      (blockRows (lowOf h.S h.d.zcW) (tok h.S h.d.wJv (lastCoords h.d.vpm.r h.S.cf.lB))))
    (hin : ∀ x, x = 3 ∨ x = 4 →
      ∀ hi < (eqTab (h.t.ptM.extract 0 ((if false then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
        Rows.planeFirst h.S x w.lam w.a false >>> h.S.cf.lmS + hi < (h.t.tabLen.lookup h.t.tVM).getD 0)
    (IV : InLong h h.t.qVM h.S.atV w.lam (fun g => g) h.d.zcW)
    (vA : W.slot (h.d.vpm.sEnd + 2 * b) = (Fo.planeF h K3 h.t.tVM 3 w.lam w.a h.t.ptM false +
      Aff.ofConst (ofNat 128) + Aff.scale (Fo.planeF h K3 h.t.tVM 4 w.lam w.a h.t.ptM false)
        (ofNat 256)).value ρ W)
    (vB : W.slot (h.d.vpm.sEnd + (2 * b + 1)) = (Aff.ofConst h.d.gam +
      Fo.readGroupT h K3 h.t.qVM h.S.atV h.d.vpm.r h.d.zcW w.lam).value ρ W) :
    W.slot (h.d.vpm.sEnd + 2 * b) =
        Aext (L5.dimOf h.S) C p (cellsK h.S M) .s11 (w.lam * h.S.HA + w.a) (pt ρ h.d.vpm.r) ∧
      W.slot (h.d.vpm.sEnd + (2 * b + 1)) =
        Bext (L5.dimOf h.S) C p (cellsK h.S M) .s11 (w.lam * h.S.HA + w.a) (pt ρ h.d.vpm.r) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hT := dim_T A
  have hl := Z.lnT
  have hlt := N.lt
  have hr' : h.d.vpm.r.size = h.S.cf.lgk + 2 * h.S.lnT - 1 + h.S.cf.lB := hr
  have hlam : (L5.dimOf h.S).lamOf (w.lam * h.S.HA + w.a) = w.lam := (pair_parts ha).1
  -- the lengths of the three parts of the point ptM
  have q1 : (h.d.vpm.r.extract 0 (h.S.cf.lgk + 2 * h.S.lnT - 1)).size =
      h.S.cf.lgk + 2 * h.S.lnT - 1 := by
    rw [sizeCut _ (by omega)]
    omega
  have q2 : (h.d.zilo h.S).size = h.S.cf.lB := by
    unfold Attention.Divide.zilo
    rw [sizeCut _ (by omega)]
    omega
  have q3 : (lastCoords h.d.vpm.r h.S.cf.lB).size = h.S.cf.lB := by
    unfold Attention.lastCoords
    rw [sizeCut _ (Nat.le_refl _)]
    omega
  have hsz : h.t.ptM.size = h.S.nM := by
    rw [hpt, N.nM]
    unfold Attention.pointM
    rw [Array.size_append, Array.size_append, q1, q2, q3]
    omega
  refine ⟨?_, ?_⟩
  · have e3 := planeF_below A TbS hsz ha (hin 3 (.inl rfl))
    have e4 := planeF_below A TbS hsz ha (hin 4 (.inr rfl))
    rw [Aff.value_add, Aff.value_add, Aff.value_ofConst, Aff.value_scale,
      A.num.ofNat, A.num.ofNat, e3, e4] at vA
    rw [vA, aext11]
    have hM : (L5.dimOf h.S).lM = h.S.nM := N.nM.symm
    rw [hM]
    have hw : wtV (cellsK h.S M) .M (w.lam * h.S.HA + w.a) = fun y =>
        (cellsK h.S M (.c .M 3 (w.lam * h.S.HA + w.a) y) + 128) +
          256 * cellsK h.S M (.c .M 4 (w.lam * h.S.HA + w.a) y) := rfl
    rw [hw, Blocks.ext_add, Blocks.ext_add, Blocks.ext_const, Blocks.ext_smul]
    have hp : ∀ f : ℕ → Kf, Blocks.ext h.S.nM f (pt ρ h.t.ptM) =
        Blocks.ext h.S.nM f (ptBelow (L5.dimOf h.S) C p (pt ρ h.d.vpm.r)) := by
      intro f
      have dlg : (L5.dimOf h.S).lg = h.S.cf.lgk := rfl
      have dlP : (L5.dimOf h.S).lP = h.S.lnT - 1 := rfl
      have dlB : (L5.dimOf h.S).lB = h.S.cf.lB := rfl
      refine Blocks.ext_congr_point (fun j hj => ?_) f
      rw [N.nM] at hj
      rw [hpt]
      unfold Attention.pointM ptBelow cat
      show _ = if j < h.S.cf.lgk + (h.S.lnT - 1) + (h.S.lnT - 1 + 1) then _ else
        if j - (h.S.cf.lgk + (h.S.lnT - 1) + (h.S.lnT - 1 + 1)) < h.S.cf.lB then _ else _
      rw [pt_append, Array.size_append, q1, q2, pt_append, q1]
      by_cases a1 : j < h.S.cf.lgk + 2 * h.S.lnT - 1
      · rw [if_pos (by omega), if_pos a1, if_pos (by omega), ptCut ρ _ (by omega) (by omega),
          Nat.zero_add]
      · by_cases a2 : j < h.S.cf.lgk + 2 * h.S.lnT - 1 + h.S.cf.lB
        · rw [if_pos a2, if_neg a1, if_neg (by omega), if_pos (by omega), hyi _ (by omega)]
          congr 1
          omega
        · rw [if_neg a2, if_neg (by omega), if_neg (by omega)]
          unfold Attention.lastCoords sh
          rw [ptCut ρ _ (Nat.le_refl _) (by omega)]
          congr 1
          omega
    rw [hp, hp]
    push_cast
    ring
  · have e5 := readGroupT_val A (zg := h.d.vpm.r) TbV (tok_size _ _ _) (by omega) hzc IV
    rw [Aff.value_add, Aff.value_ofConst, e5, hgam] at vB
    rw [vB, bext11, hlam]
    congr 1
    have sP : (h.d.vpm.r.extract h.S.cf.lgk (h.S.cf.lgk + (h.S.lnT - 1))).size =
        h.S.lnT - 1 := by
      rw [sizeCut _ (by omega)]
      omega
    have sS : (h.d.vpm.r.extract (h.S.cf.lgk + (h.S.lnT - 1))
        (h.S.cf.lgk + (h.S.lnT - 1) + h.S.lnT)).size = h.S.lnT := by
      rw [sizeCut _ (by omega)]
      omega
    have vP : ∀ j < h.S.lnT - 1,
        pt ρ (h.d.vpm.r.extract h.S.cf.lgk (h.S.cf.lgk + (h.S.lnT - 1))) j =
          sh (pt ρ h.d.vpm.r) (L5.dimOf h.S).lg j :=
      fun j hj => ptCut ρ _ (by omega) (by omega)
    have vS : ∀ j < h.S.lnT,
        pt ρ (h.d.vpm.r.extract (h.S.cf.lgk + (h.S.lnT - 1))
          (h.S.cf.lgk + (h.S.lnT - 1) + h.S.lnT)) j =
          sh (pt ρ h.d.vpm.r) ((L5.dimOf h.S).lg + (L5.dimOf h.S).lP) j :=
      fun j hj => ptCut ρ _ (by omega) (by omega)
    have vJ : ∀ j < h.S.cf.lB, pt ρ (lastCoords h.d.vpm.r h.S.cf.lB) j =
        sh (pt ρ h.d.vpm.r)
          ((L5.dimOf h.S).lg + (L5.dimOf h.S).lP + ((L5.dimOf h.S).lP + 1)) j := by
      intro j hj
      unfold Attention.lastCoords
      rw [ptCut ρ _ (Nat.le_refl _) (by omega)]
      show _ = pt ρ h.d.vpm.r (h.S.cf.lgk + (h.S.lnT - 1) + (h.S.lnT - 1 + 1) + j)
      congr 1
      omega
    rw [hwJ]
    exact rd3_congr _ (fun _ _ => rfl)
      (fun i hi => tok_psi ρ Z hT (fun I hI => tiles_col ρ Z sP sS vP vS hI) q3 vJ hi) hyn _

end K5Law
