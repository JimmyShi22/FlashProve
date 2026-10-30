-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttEnds58ProofsV.lean: a proof of ValueOnEndB (Johnson/Road/Rows/AttEnds58.lean):
the second end value of a pair in the value product's sumcheck on the diagonal tiles.

The way. As for the other claims on the matrix qa (Johnson/Road/Rows/AttEnds58ProofsQ.lean), with
two things more. The second map of the library's step s12 is th plus the read of the values (bext12
in Cb/Pv/Att/Mean/ReadsOn.lean). The table's weights on the positions are made of the equality
weights of a tile and of a place in the tile; tile and place are a position, so they are the
library's equality vector over the positions (tok_eqT).

Main theorems: tok_eqT, valueOnEndB.


-/
import Johnson.Road.Rows.AttEnds58ProofsQ
import Johnson.Road.Rows.AttTiles
import Cb.Pv.Att.Mean.ReadsOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open Finset
open OnBytes.Model (Reading World Aff Fork SubM HTailF2 TenAt tenCell eqTab)
open OnBytes.Attention (Shape Heard sc3A sc3B)
open Inst.Model.AttSeg (Dim rd3 eqT sh valV)

variable {K : Type} [Field K]

section
variable {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K} {h : Heard}
  {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-- The token weights of the value product on the diagonal tiles are the library's equality vector
over the positions, at the part of the sumcheck's point behind the head: tile and place in the tile
are a position. -/
theorem tok_eqT (A : AttAt ρ W tl K3 M h lid cf fs) {r : Array E}
    (hr : r.size = h.S.cf.lgk + h.S.lnT + h.S.cf.lB) {i : ℕ} (h' : i < (L5.dimOf h.S).T) :
    ρ.val ((Attention.tok h.S (eqTab (r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.lnT)))
      (Attention.lastCoords r h.S.cf.lB)).getD i zeroE) =
      eqT (L5.dimOf h.S) (sh (pt ρ r) (L5.dimOf h.S).lg) i := by
  have Z := sizes_of_hid A.shape
  have N := norm_of_hid A.shape
  have P := L5.shaped_of_hid A.shape
  obtain ⟨S0, hS0⟩ := L5.shape_of_hid A.shape
  have ht := (L5.tested_of_shape hS0).1
  have hn : h.S.lnT - 1 + 1 = h.S.lnT := by
    have := P.lnT
    omega
  have hiT : i < h.S.T := by
    rw [← dim_T A]
    exact h'
  have s1 : (r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.lnT)).size = h.S.lnT := by
    rw [size_cut _ (by omega)]
    omega
  have s2 : (Attention.lastCoords r h.S.cf.lB).size = h.S.cf.lB := by
    show (r.extract (r.size - h.S.cf.lB) r.size).size = _
    rw [size_cut _ (Nat.le_refl _)]
    omega
  have hq : i / 2 ^ h.S.cf.lB < 2 ^ h.S.lnT := by
    have e : h.S.cf.lB + h.S.lnT = h.S.cf.lt := by
      rw [N.lt]
      omega
    have h2 : i < 2 ^ (h.S.cf.lB + h.S.lnT) := by
      rw [e, ← Z.T]
      exact hiT
    rw [pow_add] at h2
    exact Nat.div_lt_of_lt_mul h2
  have ap := Blocks.eqN_append' (h.S.lnT - 1 + 1) h.S.cf.lB 0 (sh (pt ρ r) h.S.cf.lgk)
    (i / 2 ^ h.S.cf.lB) (Nat.mod_lt i (Nat.two_pow_pos h.S.cf.lB))
  rw [Nat.div_add_mod'] at ap
  show _ = Blocks.eqN (h.S.lnT - 1 + 1 + h.S.cf.lB) 0 (sh (pt ρ r) h.S.cf.lgk) i
  rw [ap, tok_value (ρ := ρ) h.S _ _ hiT, Z.B, eqTab_value ρ _ _ (by rw [s1]; exact hq),
    eqTab_value ρ _ _ (by rw [s2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)), s1, s2, hn]
  refine congrArg₂ (· * ·) (eqN_agree (fun k hk => ?_) _) (eqN_agree (fun k hk => ?_) _)
  · show pt ρ (r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.lnT)) (0 + k) =
      pt ρ r (h.S.cf.lgk + (0 + k))
    rw [Nat.zero_add]
    exact pt_extract ρ r (by omega) (by omega)
  · show pt ρ (r.extract (r.size - h.S.cf.lB) r.size) (0 + k) =
      pt ρ r (h.S.cf.lgk + (0 + h.S.lnT + k))
    rw [Nat.zero_add, Nat.zero_add, pt_extract ρ r (Nat.le_refl _) (by omega)]
    exact congrArg (pt ρ r) (by omega)

end

/-! ## The value product on the diagonal tiles: the values -/

/-- **ValueOnEndB holds.** -/
theorem valueOnEndB : ValueOnEndB := by
  intro K _ ρ W tl K3 M h F lid cf fs C p b w v G c c1 A hc hr hzc ha hyn hgam Tb hrun hval
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hr' : h.d.vpd.r.size = h.S.cf.lgk + h.S.lnT + h.S.cf.lB := hr
  have e := head_rd3 A hc (fun g => g) Tb (by rw [A.mats.nm]; omega)
    A.mats.qaM Z.wcQ (tok_size h.S _ _) (by omega) hzc
    (fun g l => tensor_dvd
      (by
        rw [N.atV]
        exact Nat.dvd_add (Dvd.dvd.mul_left (Dvd.dvd.mul_left (ls_dvd A) _) _)
          (Dvd.dvd.mul_left (Dvd.dvd.mul_left (ls_dvd A) _) _))
      (by rw [N.atV]; exact Dvd.dvd.mul_left (ls_dvd A) _) l _ (head_dvd A _))
    (valV (cellsK h.S M) w.lam)
    (fun g i n => by
      have e2 : h.S.atV.nl = 2 := by rw [N.atV]
      rw [e2]
      rfl)
    (ok_of_yields hrun)
  have e0 : (sc3B h.d.vpd b).value ρ W = W.slot (h.d.vpd.sEnd + (2 * b + 1)) :=
    Aff.value_slot ρ W _
  rw [Aff.value_sub, e0, Aff.value_add, Aff.value_ofConst, e, sub_eq_zero] at hval
  have hl : (L5.dimOf h.S).lamOf (w.lam * h.S.HA + w.a) = w.lam := (pair_parts ha).1
  rw [hval, bext12, hl, hgam]
  congr 1
  exact rd3_congr _ (fun _ _ => rfl) (fun i hi => tok_eqT A hr' hi) (fun j hj => hyn j hj) _

end OnBytes.Road.Rows
