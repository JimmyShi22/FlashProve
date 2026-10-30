-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/EndsV.lean: kind K5: the value product on the diagonal tiles, the
second end values: the twin, for the written form, of ValueOnEndB (Johnson/Road/Rows/AttEnds58.lean;
proved in Johnson/Road/Rows/AttEnds58ProofsV.lean of a run in a context). The proof follows that
proof line for line, with headF_rd3 where head_rd3 stood.

Main names:
  `value_on_B`: W.slot (vpd.sEnd + (2 b + 1)) = Bext (L5.dimOf h.S) C p (cellsK h.S M) .s12 (w.lam
    HA + w.a) (pt ρ vpd.r): gam plus the value.
The first end values are in Johnson/Desc/First/Att/Claims/EndsVA.lean; the product below the
diagonal in Johnson/Desc/First/Att/Claims/EndsVB.lean.
What these reach, and what not: as the head of Johnson/Desc/First/Att/Claims/EndsQ.lean says.
Premises beyond those of Johnson/Road/Rows: headFeat … = .ok; the indices read lie in the table.
Used: as Johnson/Desc/First/Att/Claims/EndsQ.lean, and tok_eqT, tok_size, bext12, pair_parts,
Attention.tok, lastCoords; the library's Bext, valV, yn.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttEnds58ProofsV
import Johnson.Desc.First.Att.Claims.EndsQ

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Cb.Pv.Att
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Dim Calls Pub rd3 eqT sh valV Bext)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K3 : ℕ} {M : Mats Kf}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-- **The twin of ValueOnEndB.** -/
theorem value_on_B (A : AttAt ρ W tl K3 M h lid cf fs) (C : Calls) (p : Pub Kf) {b : ℕ} {w : PW}
    (hr : h.d.vpd.r.size = h.S.nvVD) (hzc : h.d.zcW.size = h.S.cf.ldh) (ha : w.a < h.S.HA)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = Inst.Model.AttSeg.yn (L5.dimOf h.S) C p.z j)
    (hgam : ρ.val h.d.gam = p.th)
    (Tb : QaAt tl h h.t.qVD h.d.zcW
      (tok h.S (eqTab (h.d.vpd.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.lnT)))
        (lastCoords h.d.vpd.r h.S.cf.lB)))
    (hfeat : ∀ g < 2 ^ h.S.cf.lgk, headFeat h.S.atV g h.S.dh = .ok (g * h.S.dh))
    (hin : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < (hiOf h.S h.d.zcW).size, ∀ l < h.S.atV.nl,
      tenCell h.S.atV l w.lam (g * h.S.dh) / 2 ^ h.S.ls + ch < (h.t.tabLen.lookup h.t.qVD).getD 0)
    (hval : W.slot (h.d.vpd.sEnd + (2 * b + 1)) = (Aff.ofConst h.d.gam +
      Fo.readGroupT h K3 h.t.qVD h.S.atV h.d.vpd.r h.d.zcW w.lam).value ρ W) :
    W.slot (h.d.vpd.sEnd + (2 * b + 1)) =
      Bext (L5.dimOf h.S) C p (cellsK h.S M) .s12 (w.lam * h.S.HA + w.a) (pt ρ h.d.vpd.r) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hr' : h.d.vpd.r.size = h.S.cf.lgk + h.S.lnT + h.S.cf.lB := hr
  have hzg : h.S.cf.lgk ≤ h.d.vpd.r.size := by omega
  have e := headF_rd3 A (zg := h.d.vpd.r) (fun g => g) Tb (by rw [A.mats.nm]; omega)
    A.mats.qaM Z.wcQ (tok_size h.S _ _) hzg hzc
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
    hfeat hin
  unfold Fo.readGroupT at hval
  rw [Aff.value_add, Aff.value_ofConst, e] at hval
  have hl : (L5.dimOf h.S).lamOf (w.lam * h.S.HA + w.a) = w.lam := (pair_parts ha).1
  rw [hval, bext12, hl, hgam]
  congr 1
  exact rd3_congr _ (fun _ _ => rfl) (fun i hi => tok_eqT A hr' hi) (fun j hj => hyn j hj) _

end K5Law
