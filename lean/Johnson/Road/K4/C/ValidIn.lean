-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ValidIn.lean: CONDITIONAL.

Not shown here. That the hypotheses hold anywhere: no example is known. The library's facts on a
layout (Laid2, the eleven switches, Sized), profile 4, MatsLaid, D.f = 2 D.fe: public. CellsAre at
each of the two lists of matrices. Nothing says that the cells are those of an inference.
No property is claimed.

THE LIBRARY's KEY VECTOR OF A CALL IS ONE ON ANY TWO LISTS OF MATRICES THAT BOTH READ THE HONEST
SIDE's CELLS. CellsAre (Cells.lean) ties a list of matrices to the small input's cells inside the
matrices' ranges and off the matrix of the lookup's planes, and nowhere else: two such lists may
differ outside. The library's keys read cells with valid names alone (keyVec_agree,
Johnson/Road/FormsKeysValid.lean); here: the feature of a valid name lies inside its matrix's parts
(valid_inMat), so both lists read the small input's cell there (cell_at, Feats.lean).

  cap_ad, cap_ar, cap_qa, cap_out   the parts of four more matrices hold their features in use.
  valid_inMat    the feature of a valid name lies inside the parts of its array's matrix.
  cells_two      at a valid name the two lists' cells are one.
  keyVec_two     the key vectors' extensions at any point are one.
-/
import Johnson.Road.K4.C.StreamsOf
import Johnson.Road.FormsKeysValid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW aC keyVec)

variable {y : Lay}

/-- The parts of the matrix ad hold its features in use. -/
theorem cap_ad (L2 : Laid2 y) : y.feat.getD 1 0 ≤ partsM y 1 * colsM y 1 * fcM y 1 := by
  have hu : 0 < 2 ^ y.h.lmad / 2 ^ y.h.lt :=
    Nat.div_pos (Nat.pow_le_pow_right (by decide) L2.lt_ad) (Nat.two_pow_pos _)
  have hw : 0 < y.h.NAd * (2 ^ y.h.lmad / 2 ^ y.h.lt) :=
    Nat.mul_pos (Nat.pos_of_ne_zero L2.NAd0) hu
  show y.feat.getD 1 0 ≤ y.parts.getD 1 0 * y.kcol.getD 1 0 * (y.mrow.getD 1 0 / y.T)
  rw [L2.feat1, L2.parts1, L2.kcol1, L2.mrow1, L2.T, roundUp_div _ hw]
  have h := ceil_cover ((offsOf y.h).getD 1 0) hw
  calc (offsOf y.h).getD 1 0
      ≤ ((offsOf y.h).getD 1 0 + y.h.NAd * (2 ^ y.h.lmad / 2 ^ y.h.lt) - 1) /
          (y.h.NAd * (2 ^ y.h.lmad / 2 ^ y.h.lt)) * (y.h.NAd * (2 ^ y.h.lmad / 2 ^ y.h.lt)) := h
    _ = y.h.NAd * (((offsOf y.h).getD 1 0 + y.h.NAd * (2 ^ y.h.lmad / 2 ^ y.h.lt) - 1) /
          (y.h.NAd * (2 ^ y.h.lmad / 2 ^ y.h.lt))) * (2 ^ y.h.lmad / 2 ^ y.h.lt) := by ring

/-- The matrix ar holds its features in use. -/
theorem cap_ar (L2 : Laid2 y) : y.feat.getD 2 0 ≤ partsM y 2 * colsM y 2 * fcM y 2 := by
  have hu : 0 < 2 ^ y.h.lmar / 2 ^ y.h.lt :=
    Nat.div_pos (Nat.pow_le_pow_right (by decide) L2.lt_ar) (Nat.two_pow_pos _)
  have hw : 0 < 1 * (2 ^ y.h.lmar / 2 ^ y.h.lt) := by
    rw [Nat.one_mul]
    exact hu
  show y.feat.getD 2 0 ≤ 1 * y.kcol.getD 2 0 * (y.mrow.getD 2 0 / y.T)
  rw [L2.feat2, L2.kcol2, L2.mrow2, L2.T, roundUp_div _ hw, Nat.one_mul, Nat.one_mul]
  exact ceil_cover _ hu

/-- The matrix qa holds its features in use. -/
theorem cap_qa (L2 : Laid2 y) : y.feat.getD 3 0 ≤ partsM y 3 * colsM y 3 * fcM y 3 := by
  have hu : 0 < 2 ^ y.h.lmq / 2 ^ y.h.lt :=
    Nat.div_pos (Nat.pow_le_pow_right (by decide) L2.lt_q) (Nat.two_pow_pos _)
  have hw : 0 < 1 * (2 ^ y.h.lmq / 2 ^ y.h.lt) := by
    rw [Nat.one_mul]
    exact hu
  show y.feat.getD 3 0 ≤ 1 * y.kcol.getD 3 0 * (y.mrow.getD 3 0 / y.T)
  rw [L2.feat3, L2.kcol3, L2.mrow3, L2.T, roundUp_div _ hw, Nat.one_mul, Nat.one_mul]
  exact ceil_cover _ hu

/-- The other matrix of the residual stream holds xl d features. -/
theorem cap_out (L2 : Laid2 y) : y.h.xl * y.h.d ≤ partsM y 5 * colsM y 5 * fcM y 5 :=
  cap_stream L2

/-- **The feature of a valid name lies inside the parts of its array's matrix.** -/
theorem valid_inMat (L2 : Laid2 y) (S : Switches y.h) {D : Dim} (Z : Sized y.h D)
    (hp4 : y.h.p4 = true) {q : Cell} (hv : q.Valid D) :
    InMat y (mxNo q.X.mx) (Inst.Model.FFSeg.feat D q.X q.k q.inst q.j) := by
  obtain ⟨hk, hi, hj, -⟩ := hv
  have h1 := Inst.Model.FFSeg.IndexFacts.feat_lt D hk hi hj
  obtain ⟨f0, f1, f2, f3, -, f4, f5⟩ := feat_total L2 S Z
  have hb := Inst.Model.FFSeg.IndexFacts.mx_ne_b q.X
  generalize Inst.Model.FFSeg.feat D q.X q.k q.inst q.j = φ at h1 ⊢
  generalize q.X.mx = μ at h1 hb ⊢
  cases μ with
  | af => exact ⟨by decide, Nat.lt_of_lt_of_le (f0 ▸ h1) (cap_af L2)⟩
  | ad => exact ⟨by decide, Nat.lt_of_lt_of_le (f1 ▸ h1) (cap_ad L2)⟩
  | ar => exact ⟨by decide, Nat.lt_of_lt_of_le (f2 ▸ h1) (cap_ar L2)⟩
  | qa => exact ⟨by decide, Nat.lt_of_lt_of_le (f3 hp4 ▸ h1) (cap_qa L2)⟩
  | xin => exact ⟨by decide, Nat.lt_of_lt_of_le (f4 ▸ h1) (cap_stream L2)⟩
  | xout => exact ⟨by decide, Nat.lt_of_lt_of_le (f5 ▸ h1) (cap_out L2)⟩
  | b => exact absurd rfl hb

/-- **At a valid name the cells of two lists of matrices that both read the small input's cells are
one.** -/
theorem cells_two {Q : K4Pub} {w : K4In} {M M' : Mats Cb.Gl.E} (C : CellsAre Q w M)
    (C' : CellsAre Q w M') (L : MatsLaid Q) (L2 : Laid2 Q.P.y) (S : Switches Q.P.y.h) {D : Dim}
    (Z : Sized Q.P.y.h D) (hp4 : Q.P.y.h.p4 = true) (q : Cell) (hv : q.Valid D) :
    cellsOf D (cellsAt Q.P.y M) q = cellsOf D (cellsAt Q.P.y M') q := by
  have hf := valid_inMat L2 S Z hp4 hv
  have ht : q.i < Q.P.y.T := by
    rw [T_eq L2 Z]
    exact hv.2.2.2
  show cellsAt Q.P.y M _ _ q.i = cellsAt Q.P.y M' _ _ q.i
  rw [← cell_at C L hf ht, ← cell_at C' L hf ht]

/-- **The key vectors on the two lists: their extensions at any point are one.** -/
theorem keyVec_two [scl : Scl] {Q : K4Pub} {w : K4In} {M M' : Mats Cb.Gl.E}
    (C : CellsAre Q w M) (C' : CellsAre Q w M') (L : MatsLaid Q) (L2 : Laid2 Q.P.y)
    (S : Switches Q.P.y.h) {D : Dim} (Z : Sized Q.P.y.h D) (hp4 : Q.P.y.h.p4 = true)
    (hf : D.f = 2 * D.fe) (tb : Tables) (L0 : ℕ) (lw : ℕ → LW Cb.Gl.E) (cc : Fin 8)
    (ζ : ℕ → Cb.Gl.E) :
    Blocks.ext (aC D cc) (keyVec D (cellsOf D (cellsAt Q.P.y M)) tb L0 lw cc) ζ =
      Blocks.ext (aC D cc) (keyVec D (cellsOf D (cellsAt Q.P.y M')) tb L0 lw cc) ζ :=
  ext_keyVec_agree (cells_two C C' L L2 S Z hp4) hf tb L0 lw cc ζ

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.cap_ad
#print axioms OnBytes.Road.K4.C.cap_ar
#print axioms OnBytes.Road.K4.C.cap_qa
#print axioms OnBytes.Road.K4.C.cap_out
#print axioms OnBytes.Road.K4.C.valid_inMat
#print axioms OnBytes.Road.K4.C.cells_two
#print axioms OnBytes.Road.K4.C.keyVec_two
