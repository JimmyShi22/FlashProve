-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttPortClFirst.lean: if the verifier's claims 4, 5 and 6 on the end values of the
first four sumchecks of an attention sub-proof have the value 0, the library-side claims hold, at
any values of the late entries; and the line of claim 6.

As Johnson/Road/Rows/AttPortCl.lean, for the scores of the two units, the denominator times the
output and the value product below the diagonal, with the reading forms of Cb/Pv/Att/End/First.lean.

Main theorems. x is Sum.elim m u.
 - unitM_cl, unitD_cl: the claims on both end values of every pair of a unit of the scores, below
   the diagonal and on it.
 - product_cl: those of the denominator times the output. below_cl: those of the value product below
   the diagonal.
 - line_cl: the first claim of claim 6, on four slots: the two hidden sums add up to the hidden ACC
   plus the drawn element times the hidden ZC.

What the theorems take as given, and what is not claimed: as in Johnson/Road/Rows/AttPortCl.lean,
with ScoreGiven, ProductGiven and BelowGiven of Johnson/Road/Rows/AttBetween.lean.


-/
import Johnson.Road.Rows.AttPortCl
import Johnson.Road.Rows.AttPortFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset Cb
open OnBytes.Model (Reading World Aff Fork)
open OnBytes.Attention (Heard Score ScoreTables PW)
open Inst.Model.AttSeg (Raw Calls Pub Step yn)
open Cb.Pv.Att (stepSc3 ptBelow)
open Cb.Pv.Att.End (LateLay AttTab endF ptN pick rA6b rB6b rA6d rB6d rA8 rB8 rA11 rB11 hidF aAdd
  aSub aSmul Good6b Good6d Good8 Good11 val_aSub val_aAdd val_aConst val_aSmul val_aEnt)

variable {K : Type} [Field K] [Fintype K]

variable {ρ : Reading K} {W : World K} {K3 : ℕ} {h : Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {u : J₂ → K} {m : J₁ → K}
  {rd : (J₁ → K) → Raw → K} {inc : Pub K → J₁ → K}

/-- Piece number b of a list that has a piece for each pair. -/
theorem piece_of {pw : Array PW} (P : PiecesAll h.S pw) {b : ℕ} (hb : b < h.S.NP) :
    ∃ w, pw[b]? = some w ∧ w.lam = b / h.S.HA ∧ w.a < h.S.HA ∧ w.lam * h.S.HA + w.a = b := by
  obtain ⟨hsz, hpw⟩ := P
  have hb' : b < pw.size := by rw [hsz]; exact hb
  have hw : pw[b]? = some pw[b] := Array.getElem?_eq_getElem hb'
  obtain ⟨e1, e2⟩ := hpw b hb _ hw
  refine ⟨_, hw, e1, ?_, ?_⟩
  · rw [e2]
    exact Nat.mod_lt b (heads_pos hb)
  · rw [e1, e2]
    exact Nat.div_add_mod' b h.S.HA

/-- The scores of the unit below the diagonal. -/
theorem unitM_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    {k : Score} {tb : ScoreTables} (hQ : tabOf .tQm = tb.tQ) (hK : tabOf .tKm = tb.tK) (Cc : Calls)
    {cAt : Fin (L5.dimOf h.S).nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt K (Step.s6b.g (L5.dimOf h.S)) (fun _ => 3) ++ [pDummy K 2]) → J₁}
    (o : (stepSc3 (L5.dimOf h.S) Cc rd .s6b inc wAt cAt).plain.our.par.Out)
    (g : ScoreGiven ρ W K3 h k tb) (P : PiecesAll h.S k.pw) (hq2 : h.S.atQ.nl = 2)
    (hk2 : h.S.atK.nl = 2)
    (hr : k.sc.r.size = (L5.dimOf h.S).lg + (L5.dimOf h.S).lP + ((L5.dimOf h.S).lP + 1) +
      h.S.cf.ldh)
    (hξ : ∀ j < (L5.dimOf h.S).lg + (L5.dimOf h.S).lP + ((L5.dimOf h.S).lP + 1) + h.S.cf.ldh,
      ptN _ o j = pt ρ k.sc.r j)
    (hG : Good6b (L5.dimOf h.S) h.S.ls Y)
    (hs : ∀ b : Fin (L5.dimOf h.S).nb,
      SlotAt W (stepSc3 (L5.dimOf h.S) Cc rd .s6b inc wAt cAt).plain o (Sum.elim m u)
          (k.sc.sEnd + 2 * b.val) (b, false) ∧
        SlotAt W (stepSc3 (L5.dimOf h.S) Cc rd .s6b inc wAt cAt).plain o (Sum.elim m u)
          (k.sc.sEnd + (2 * b.val + 1)) (b, true))
    (a : Fin (L5.dimOf h.S).nb × Bool) :
    (endF (stepSc3 (L5.dimOf h.S) Cc rd .s6b inc wAt cAt).plain o a
      (pick (rA6b (L5.dimOf h.S) h.S.ls Y (ptN _ o)) (rB6b (L5.dimOf h.S) h.S.ls Y (ptN _ o))
        a)).Holds (Sum.elim m u) := by
  obtain ⟨b, s⟩ := a
  obtain ⟨w, hw, e1, ha, eb⟩ := piece_of P (b := b.val) b.isLt
  obtain ⟨q, kx, F, F', G, G', c, c1, c', c1', k1, k2, r1, r2, v1, v2⟩ := g b.val w hw
  obtain ⟨x1, x2⟩ := unit_port m A k1 L .tQm .tKm hQ hK rfl rfl hq2 hk2
    (n := (L5.dimOf h.S).lg + (L5.dimOf h.S).lP + ((L5.dimOf h.S).lP + 1))
    (by show h.S.cf.lgk ≤ h.S.cf.lgk + _ + _; omega) hr hξ ha
    (by rw [eb]; exact hG.tQ b.val b.isLt)
    (by rw [e1]; exact hG.tK b.val b.isLt) k2 (ok_of_yields r1) (ok_of_yields r2)
  rw [eb] at x1
  rw [e1] at x2
  cases s with
  | false => exact (end_port _ o (b, false) _ (Sum.elim m u) _ _ (hs b).1 x1).mp v1
  | true => exact (end_port _ o (b, true) _ (Sum.elim m u) _ _ (hs b).2 x2).mp v2

/-- The scores of the unit on the diagonal. -/
theorem unitD_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    {k : Score} {tb : ScoreTables} (hQ : tabOf .tQd = tb.tQ) (hK : tabOf .tKd = tb.tK) (Cc : Calls)
    {cAt : Fin (L5.dimOf h.S).nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt K (Step.s6d.g (L5.dimOf h.S)) (fun _ => 3) ++ [pDummy K 2]) → J₁}
    (o : (stepSc3 (L5.dimOf h.S) Cc rd .s6d inc wAt cAt).plain.our.par.Out)
    (g : ScoreGiven ρ W K3 h k tb) (P : PiecesAll h.S k.pw) (hq2 : h.S.atQ.nl = 2)
    (hk2 : h.S.atK.nl = 2)
    (hr : k.sc.r.size = (L5.dimOf h.S).lg + ((L5.dimOf h.S).lP + 1) + h.S.cf.ldh)
    (hξ : ∀ j < (L5.dimOf h.S).lg + ((L5.dimOf h.S).lP + 1) + h.S.cf.ldh,
      ptN _ o j = pt ρ k.sc.r j)
    (hG : Good6d (L5.dimOf h.S) h.S.ls Y)
    (hs : ∀ b : Fin (L5.dimOf h.S).nb,
      SlotAt W (stepSc3 (L5.dimOf h.S) Cc rd .s6d inc wAt cAt).plain o (Sum.elim m u)
          (k.sc.sEnd + 2 * b.val) (b, false) ∧
        SlotAt W (stepSc3 (L5.dimOf h.S) Cc rd .s6d inc wAt cAt).plain o (Sum.elim m u)
          (k.sc.sEnd + (2 * b.val + 1)) (b, true))
    (a : Fin (L5.dimOf h.S).nb × Bool) :
    (endF (stepSc3 (L5.dimOf h.S) Cc rd .s6d inc wAt cAt).plain o a
      (pick (rA6d (L5.dimOf h.S) h.S.ls Y (ptN _ o)) (rB6d (L5.dimOf h.S) h.S.ls Y (ptN _ o))
        a)).Holds (Sum.elim m u) := by
  obtain ⟨b, s⟩ := a
  obtain ⟨w, hw, e1, ha, eb⟩ := piece_of P (b := b.val) b.isLt
  obtain ⟨q, kx, F, F', G, G', c, c1, c', c1', k1, k2, r1, r2, v1, v2⟩ := g b.val w hw
  obtain ⟨x1, x2⟩ := unit_port m A k1 L .tQd .tKd hQ hK rfl rfl hq2 hk2
    (n := (L5.dimOf h.S).lg + ((L5.dimOf h.S).lP + 1))
    (by show h.S.cf.lgk ≤ h.S.cf.lgk + _; omega) hr hξ ha
    (by rw [eb]; exact hG.tQ b.val b.isLt)
    (by rw [e1]; exact hG.tK b.val b.isLt) k2 (ok_of_yields r1) (ok_of_yields r2)
  rw [eb] at x1
  rw [e1] at x2
  cases s with
  | false => exact (end_port _ o (b, false) _ (Sum.elim m u) _ _ (hs b).1 x1).mp v1
  | true => exact (end_port _ o (b, true) _ (Sum.elim m u) _ _ (hs b).2 x2).mp v2

/-- The denominator times the output. -/
theorem product_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (hE : tabOf .hE = h.t.hE) (hO : tabOf .qO = h.t.qO) (Cc : Calls)
    {cAt : Fin (L5.dimOf h.S).nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt K (Step.s8.g (L5.dimOf h.S)) (fun _ => 3) ++ [pDummy K 2]) → J₁}
    (o : (stepSc3 (L5.dimOf h.S) Cc rd .s8 inc wAt cAt).plain.our.par.Out)
    (g : ProductGiven ρ W K3 h) (P : PiecesAll h.S h.d.pwW) (hnl : h.S.atO.nl = 2)
    (hr : h.S.cf.lgk ≤ h.d.scE.r.size) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lgk, ptN _ o j = pt ρ h.d.scE.r j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn (L5.dimOf h.S) Cc (Pub.z o.st) j)
    (hG : Good8 (L5.dimOf h.S) h.S.ls Y)
    (hs : ∀ b : Fin (L5.dimOf h.S).nb,
      SlotAt W (stepSc3 (L5.dimOf h.S) Cc rd .s8 inc wAt cAt).plain o (Sum.elim m u)
          (h.d.scE.sEnd + 2 * b.val) (b, false) ∧
        SlotAt W (stepSc3 (L5.dimOf h.S) Cc rd .s8 inc wAt cAt).plain o (Sum.elim m u)
          (h.d.scE.sEnd + (2 * b.val + 1)) (b, true))
    (a : Fin (L5.dimOf h.S).nb × Bool) :
    (endF (stepSc3 (L5.dimOf h.S) Cc rd .s8 inc wAt cAt).plain o a
      (pick (rA8 (L5.dimOf h.S) Y (ptN _ o)) (rB8 (L5.dimOf h.S) Cc h.S.ls Y o.st (ptN _ o))
        a)).Holds (Sum.elim m u) := by
  obtain ⟨b, s⟩ := a
  obtain ⟨w, hw, e1, ha, eb⟩ := piece_of P (b := b.val) b.isLt
  obtain ⟨z, q, F, F', G, G', c, c1, c', c1', k1, k2, r1, r2, v1, v2⟩ := g b.val w hw
  cases s with
  | false =>
    have x1 := den_port m A k1 L hE (ξ := ptN _ o) ha hr hξ
      (by rw [eb]; exact hG.hE b.val b.isLt) (ok_of_yields r1)
    rw [eb] at x1
    exact (end_port _ o (b, false) _ (Sum.elim m u) _ _ (hs b).1 x1).mp v1
  | true =>
    have x2 := out_port m A k2 L hO (Cc := Cc) (p := o.st) (ξ := ptN _ o) ha hnl hr hzc hξ hyn
      (by rw [eb]; exact hG.qO b.val b.isLt) (ok_of_yields r2)
    rw [eb] at x2
    exact (end_port _ o (b, true) _ (Sum.elim m u) _ _ (hs b).2 x2).mp v2

/-- The value product below the diagonal. -/
theorem below_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (hS : tabOf .tVM = h.t.tVM) (hV : tabOf .qVM = h.t.qVM) (Cc : Calls)
    {cAt : Fin (L5.dimOf h.S).nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt K (Step.s11.g (L5.dimOf h.S)) (fun _ => 3) ++ [pDummy K 2]) → J₁}
    (o : (stepSc3 (L5.dimOf h.S) Cc rd .s11 inc wAt cAt).plain.our.par.Out)
    (g : BelowGiven ρ W K3 h) (P : PiecesAll h.S h.d.pwW) (hnl : h.S.atV.nl = 2)
    (hnM : (L5.dimOf h.S).lM = h.S.nM) (hz : h.t.ptM.size = h.S.nM)
    (hr : h.S.cf.lgk ≤ h.d.vpm.r.size) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lgk, ptN _ o j = pt ρ h.d.vpm.r j)
    (hpt : ∀ j < h.S.nM - h.S.cf.lmS,
      pt ρ h.t.ptM j = ptBelow (L5.dimOf h.S) Cc o.st (ptN _ o) j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn (L5.dimOf h.S) Cc (Pub.z o.st) j)
    (hgam : ρ.val h.d.gam = Pub.th o.st) (hG : Good11 (L5.dimOf h.S) h.S.ls h.S.cf.lmS Y)
    (hs : ∀ b : Fin (L5.dimOf h.S).nb,
      SlotAt W (stepSc3 (L5.dimOf h.S) Cc rd .s11 inc wAt cAt).plain o (Sum.elim m u)
          (h.d.vpm.sEnd + 2 * b.val) (b, false) ∧
        SlotAt W (stepSc3 (L5.dimOf h.S) Cc rd .s11 inc wAt cAt).plain o (Sum.elim m u)
          (h.d.vpm.sEnd + (2 * b.val + 1)) (b, true))
    (a : Fin (L5.dimOf h.S).nb × Bool) :
    (endF (stepSc3 (L5.dimOf h.S) Cc rd .s11 inc wAt cAt).plain o a
      (pick (rA11 (L5.dimOf h.S) Cc h.S.cf.lmS Y o.st (ptN _ o))
        (rB11 (L5.dimOf h.S) Cc h.S.ls Y o.st (ptN _ o)) a)).Holds (Sum.elim m u) := by
  obtain ⟨b, s⟩ := a
  obtain ⟨w, hw, e1, ha, eb⟩ := piece_of P (b := b.val) b.isLt
  obtain ⟨p3, p4, v, F, F', F'', G, G', G'', c, c1, c', c1', c'', c1'', k1, k2, k3, r1, r2, r3, v1,
    v2⟩ := g b.val w hw
  cases s with
  | false =>
    have e := weightM_port m A.num k1 L hS (Cc := Cc) (p := o.st) (ξ := ptN _ o) ha hnM hz hpt
      (by rw [eb, ← hnM]; exact hG.tVM b.val b.isLt) k2 (ok_of_yields r1) (ok_of_yields r2)
    rw [eb] at e
    exact (end_port _ o (b, false) _ (Sum.elim m u) _ _ (hs b).1 e).mp v1
  | true =>
    exact (end_port _ o (b, true) _ (Sum.elim m u) _ _ (hs b).2
      (valueM_port m A k3 L hV (Cc := Cc) (p := o.st) (ξ := ptN _ o) (b := b.val) e1.symm hnl hr
        hzc hξ hyn hgam (by rw [e1]; exact hG.qVM b.val b.isLt) (ok_of_yields r3))).mp v2

omit [Fintype K] in
/-- The line of claim 6. r0, r1, ra, rz: what was sent for the two sums, ACC and ZC; k0, k1, ka, kz:
the places of their mask entries; th: the drawn element. -/
theorem line_cl (r0 r1 ra rz th : K) (k0 k1 ka kz : J₁)
    (h0 : W.slot h.d.sCl = r0 - m k0) (h1 : W.slot (h.d.sCl + 1) = r1 - m k1)
    (ha : W.slot h.d.sACC = ra - m ka) (hz : W.slot h.d.sZC = rz - m kz)
    (hth : ρ.val h.d.gam = th)
    (v : (Aff.slot h.d.sCl + Aff.slot (h.d.sCl + 1) - Aff.slot h.d.sACC -
      Aff.scale (Aff.slot h.d.sZC) h.d.gam).value ρ W = 0) :
    ((aSub (aAdd (hidF r0 k0) (hidF r1 k1))
      (aAdd (hidF ra ka) (aSmul th (hidF rz kz)))).claim :
        TWhole.Form K (J₁ ⊕ J₂)).Holds (Sum.elim m u) := by
  rw [Aff.value_sub, Aff.value_sub, Aff.value_add, Aff.value_scale, Aff.value_slot, Aff.value_slot,
    Aff.value_slot, Aff.value_slot, h0, h1, ha, hz, hth] at v
  unfold Cb.Pv.Att.End.hidF
  rw [TWhole.Aff.claim_holds, val_aSub, val_aAdd, val_aAdd, val_aSmul, val_aSub, val_aSub,
    val_aSub, val_aSub, val_aConst, val_aConst, val_aConst, val_aConst, val_aEnt, val_aEnt,
    val_aEnt, val_aEnt]
  show r0 - m k0 + (r1 - m k1) - (ra - m ka + th * (rz - m kz)) = 0
  linear_combination v

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.unitM_cl
#print axioms OnBytes.Road.Rows.unitD_cl
#print axioms OnBytes.Road.Rows.product_cl
#print axioms OnBytes.Road.Rows.below_cl
#print axioms OnBytes.Road.Rows.line_cl
