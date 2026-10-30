-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttEnds14Below.lean: proof of the statement of Johnson/Road/Rows/AttEnds14.lean on
the value product below the diagonal.

Main theorems: getD_append, pt_append; plane_below (a plane of the matrix as below the diagonal,
read through its table, is the extension of its cells); valueBelowEnd.

Nothing is said about probabilities or about hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttEnds14Tiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open Finset
open OnBytes.Model (Reading World Aff Fork SubM HFun HTailF2 TenAt tenCell eqTab blockRows)
open OnBytes.Attention (Shape Heard Score sc3A sc3B lastCoords lastN)
open OnBytes.Road.Hd (Ok)
open Inst.Model.AttSeg (rd3 sh valV wtV Aext Bext cat)

variable {K : Type} [Field K]

/-- An entry of two arrays, one after the other. -/
theorem getD_append (x y : Array E) (j : ℕ) :
    (x ++ y).getD j zeroE = if j < x.size then x.getD j zeroE else y.getD (j - x.size) zeroE := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split <;> rfl

/-- A coordinate of two points, one after the other. -/
theorem pt_append (ρ : Reading K) (x y : Array E) (j : ℕ) :
    pt ρ (x ++ y) j = if j < x.size then pt ρ x j else pt ρ y (j - x.size) := by
  unfold pt
  rw [getD_append]
  split <;> rfl

section Forms

variable {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K} {h : Heard}
  {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-- A plane below the diagonal, read at a point z of nM coordinates through the table whose weights
are the equality weights of the last lmS coordinates of z, is the extension of the plane's cells. -/
theorem plane_below (A : AttAt ρ W tl K3 M h lid cf fs) {F : Fork} (hc : Cols F h K3) {t : ℕ}
    {z : Array E} (Tb : AsAt h t (lastN z h.S.cf.lmS)) (hz : z.size = h.S.nM) {x lam a : ℕ}
    (ha : a < h.S.HA) {q : Aff} {G : Fork} {C D : Ctx}
    (hq : Ok (Attention.plane h t x lam a z false) F C q G D) :
    q.value ρ W =
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
  obtain ⟨-, -, e⟩ := plane_value A hc Tb hq
  have i0 : (if false = true then h.S.nD else h.S.nM) = h.S.nM := if_neg (by decide)
  rw [i0] at e
  have s1 : (z.extract 0 (h.S.nM - h.S.cf.lmS)).size = h.S.nM - h.S.cf.lmS := by
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
  have c1 : (planeFirst h.S x lam a false >>> h.S.cf.lmS + hi) * 2 ^ h.S.cf.lmS + lo =
      ((x * h.S.Lam + lam) * h.S.HA + a) * 2 ^ h.S.nM + (hi * 2 ^ h.S.cf.lmS + lo) := by
    have p1 : planeFirst h.S x lam a false = ((x * h.S.Lam + lam) * h.S.HA + a) * 2 ^ h.S.nM := by
      unfold planeFirst
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

end Forms

/-! ## The value product below the diagonal -/

/-- The end values of the value product's sumcheck below the diagonal. -/
theorem valueBelowEnd : ValueBelowEnd := by
  intro K _ ρ W tl K3 M h lid cf fs C p b w p3 p4 v F F' F'' G G' G'' c c1 c' c1' c'' c1'' A hc
    hc' hc'' hr hzi hzc ha hpt hwJ hyi hyn hgam TbS TbV h3 h4 hv vA vB
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hT := dim_T A
  have hl := Z.lnT
  have hlt := N.lt
  have hr' : h.d.vpm.r.size = h.S.cf.lgk + 2 * h.S.lnT - 1 + h.S.cf.lB := hr
  have hlam : (L5.dimOf h.S).lamOf (w.lam * h.S.HA + w.a) = w.lam := (pair_parts ha).1
  have s1 : (sc3A h.d.vpm b).value ρ W = W.slot (h.d.vpm.sEnd + 2 * b) := Aff.value_slot ρ W _
  have s2 : (sc3B h.d.vpm b).value ρ W = W.slot (h.d.vpm.sEnd + (2 * b + 1)) :=
    Aff.value_slot ρ W _
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
  · have e3 := plane_below A hc TbS hsz ha (ok_of_yields h3)
    have e4 := plane_below A hc' TbS hsz ha (ok_of_yields h4)
    rw [Aff.value_sub, s1, Aff.value_add, Aff.value_add, Aff.value_ofConst, Aff.value_scale,
      A.num.ofNat, A.num.ofNat, e3, e4, sub_eq_zero] at vA
    rw [vA, aext11]
    have hM : (L5.dimOf h.S).lM = h.S.nM := N.nM.symm
    rw [hM]
    have hw : wtV (cellsK h.S M) .M (w.lam * h.S.HA + w.a) = fun y =>
        (cellsK h.S M (.c .M 3 (w.lam * h.S.HA + w.a) y) + 128) +
          256 * cellsK h.S M (.c .M 4 (w.lam * h.S.HA + w.a) y) := rfl
    rw [hw, Blocks.ext_add, Blocks.ext_add, Blocks.ext_const, Blocks.ext_smul]
    have hp : ∀ f : ℕ → K, Blocks.ext h.S.nM f (pt ρ h.t.ptM) =
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
  · have e5 := readGroup_val A hc'' TbV (tok_size _ _ _) (by omega) hzc (ok_of_yields hv)
    rw [Aff.value_sub, s2, Aff.value_add, Aff.value_ofConst, e5, sub_eq_zero, hgam] at vB
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

end OnBytes.Road.Rows
