-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PortClFirst.lean: kind K5: what claims 4, 5 and 6 say on the end
values of the first four sumchecks (Johnson/Desc/First/Att/Claims/Say.lean: UnitAt;
Johnson/Desc/First/Att/Claims/Say58.lean: Say5, Say6.below, Say6.acc) gives the library-side claims,
at any values of the late entries. Twins of unitM_cl, unitD_cl, product_cl, below_cl and line_cl
(Johnson/Road/Rows/AttPortClFirst.lean), whose "…Given" records hold runs of routines in a context.
No table is taken to be true. The proofs follow those proofs line for line, with the twin of
Johnson/Desc/First/Att/Claims/PortFirst.lean where the port stood.

Main names: `unit_two`, `unitMF_cl`, `unitDF_cl`, `productF_cl`, `belowF_cl`, `lineF_cl`.
Taken as given: as the head of Johnson/Desc/First/Att/Claims/PortCl.lean says; InUnit and InTail for
the lawful heads.
Limit: the claims on the sumchecks' rows are not treated.
Used: as Johnson/Desc/First/Att/Claims/PortCl.lean, and piece_of; the library's rA6b … rB11, hidF,
aAdd, aSub, aSmul, Good6b, Good6d, Good8, Good11.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttPortClFirst
import Johnson.Desc.First.Att.Claims.PortCl
import Johnson.Desc.First.Att.Claims.PortFirst

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset Cb
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Raw Calls Pub Step yn)
open Cb.Pv.Att (stepSc3 ptBelow)
open Cb.Pv.Att.End (LateLay AttTab endF ptN pick rA6b rB6b rA6d rB6d rA8 rB8 rA11 rB11 hidF aAdd
  aSub aSmul Good6b Good6d Good8 Good11 val_aSub val_aAdd val_aConst val_aSmul val_aEnt)

variable {Kf : Type} [Field Kf] [Fintype Kf]

variable {ρ : Reading Kf} {W : World Kf} {K3 : ℕ} {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {u : J₂ → Kf} {m : J₁ → Kf}
  {rd : (J₁ → Kf) → Raw → Kf} {inc : Pub Kf → J₁ → Kf}

omit [Fintype Kf] in
/-- The two equations of a unit at piece b. -/
theorem unit_two {k : Score} {tb : ScoreTables} {pc : PlaneClaim} (U : UnitAt ρ W h K3 k tb pc)
    (P : PiecesAll h.S k.pw) {b : ℕ} (hb : b < h.S.NP) {w : PW} (hw : k.pw[b]? = some w) :
    W.slot (k.sc.sEnd + 2 * b) = (Fo.readHeadT h K3 tb.tQ h.S.atQ k.sc.r
        (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size) w.lam w.a).value ρ W ∧
    W.slot (k.sc.sEnd + (2 * b + 1)) = (Fo.readGroupT h K3 tb.tK h.S.atK k.sc.r
        (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size) w.lam).value ρ W := by
  have hg := getD_of hw
  have hs : k.pw.size = h.S.NP := P.1
  have a := U.ends (2 * b) (by omega)
  have c := U.ends (2 * b + 1) (by omega)
  unfold endsU at a c
  rw [if_pos (by omega), show 2 * b / 2 = b by omega, hg] at a
  rw [if_neg (by omega), show (2 * b + 1) / 2 = b by omega, hg] at c
  exact ⟨a, c⟩

/-- The scores of the unit below the diagonal. -/
theorem unitMF_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    {k : Score} {tb : ScoreTables} {pc : PlaneClaim} (hQ : tabOf .tQm = tb.tQ) (hK : tabOf .tKm = tb.tK)
    (Cc : Calls) {cAt : Fin (L5.dimOf h.S).nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s6b.g (L5.dimOf h.S)) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 (L5.dimOf h.S) Cc rd .s6b inc wAt cAt).plain.our.par.Out)
    (U : UnitAt ρ W h K3 k tb pc) (I : InUnit h k tb) (P : PiecesAll h.S k.pw) (hq2 : h.S.atQ.nl = 2)
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
  obtain ⟨v1, v2⟩ := unit_two U P b.isLt hw
  obtain ⟨x1, x2⟩ := unitF_port (K3 := K3) (k := k) (tb := tb) m A L .tQm .tKm hQ hK rfl rfl hq2 hk2
    (n := (L5.dimOf h.S).lg + (L5.dimOf h.S).lP + ((L5.dimOf h.S).lP + 1))
    (by show h.S.cf.lgk ≤ h.S.cf.lgk + _ + _; omega) hr hξ ha
    (by rw [eb]; exact hG.tQ b.val b.isLt)
    (by rw [e1]; exact hG.tK b.val b.isLt) (I.tQ b.val w hw).feat (I.tK b.val w hw).feat
  rw [eb] at x1
  rw [e1] at x2
  rw [e1] at v2
  cases s with
  | false => exact end_of _ o (b, false) _ (Sum.elim m u) _ _ (hs b).1 x1 v1
  | true => exact end_of _ o (b, true) _ (Sum.elim m u) _ _ (hs b).2 x2 v2

/-- The scores of the unit on the diagonal. -/
theorem unitDF_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    {k : Score} {tb : ScoreTables} {pc : PlaneClaim} (hQ : tabOf .tQd = tb.tQ) (hK : tabOf .tKd = tb.tK)
    (Cc : Calls) {cAt : Fin (L5.dimOf h.S).nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s6d.g (L5.dimOf h.S)) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 (L5.dimOf h.S) Cc rd .s6d inc wAt cAt).plain.our.par.Out)
    (U : UnitAt ρ W h K3 k tb pc) (I : InUnit h k tb) (P : PiecesAll h.S k.pw) (hq2 : h.S.atQ.nl = 2)
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
  obtain ⟨v1, v2⟩ := unit_two U P b.isLt hw
  obtain ⟨x1, x2⟩ := unitF_port (K3 := K3) (k := k) (tb := tb) m A L .tQd .tKd hQ hK rfl rfl hq2 hk2
    (n := (L5.dimOf h.S).lg + ((L5.dimOf h.S).lP + 1))
    (by show h.S.cf.lgk ≤ h.S.cf.lgk + _; omega) hr hξ ha
    (by rw [eb]; exact hG.tQ b.val b.isLt)
    (by rw [e1]; exact hG.tK b.val b.isLt) (I.tQ b.val w hw).feat (I.tK b.val w hw).feat
  rw [eb] at x1
  rw [e1] at x2
  rw [e1] at v2
  cases s with
  | false => exact end_of _ o (b, false) _ (Sum.elim m u) _ _ (hs b).1 x1 v1
  | true => exact end_of _ o (b, true) _ (Sum.elim m u) _ _ (hs b).2 x2 v2

/-- The denominator times the output. -/
theorem productF_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (hE : tabOf .hE = h.t.hE) (hO : tabOf .qO = h.t.qO) (Cc : Calls)
    {cAt : Fin (L5.dimOf h.S).nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s8.g (L5.dimOf h.S)) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 (L5.dimOf h.S) Cc rd .s8 inc wAt cAt).plain.our.par.Out)
    (s5 : Say5 ρ W h K3) (I : InTail h) (P : PiecesAll h.S h.d.pwW) (hnl : h.S.atO.nl = 2)
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
  have hb : b.val < h.S.NP := b.isLt
  obtain ⟨w, hw, e1, ha, eb⟩ := piece_of P (b := b.val) b.isLt
  have hgd := getD_of hw
  have v1 := s5.ends (2 * b.val) (by omega)
  have v2 := s5.ends (2 * b.val + 1) (by omega)
  unfold endsE at v1 v2
  rw [if_pos (by omega), show 2 * b.val / 2 = b.val by omega, hgd] at v1
  rw [if_neg (by omega), show (2 * b.val + 1) / 2 = b.val by omega, hgd] at v2
  cases s with
  | false =>
    have x1 := denF_port (K3 := K3) m A L hE (ξ := ptN _ o) ha hr hξ
      (by rw [eb]; exact hG.hE b.val b.isLt)
    rw [eb] at x1
    exact end_of _ o (b, false) _ (Sum.elim m u) _ _ (hs b).1 x1 v1
  | true =>
    have x2 := outF_port (K3 := K3) m A L hO (Cc := Cc) (p := o.st) (ξ := ptN _ o) ha hnl hr hzc hξ hyn
      (by rw [eb]; exact hG.qO b.val b.isLt) (I.qO b.val hb w hw).feat
    rw [eb] at x2
    exact end_of _ o (b, true) _ (Sum.elim m u) _ _ (hs b).2 x2 v2

/-- The value product below the diagonal. -/
theorem belowF_cl (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (hS : tabOf .tVM = h.t.tVM) (hV : tabOf .qVM = h.t.qVM) (Cc : Calls)
    {cAt : Fin (L5.dimOf h.S).nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s11.g (L5.dimOf h.S)) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 (L5.dimOf h.S) Cc rd .s11 inc wAt cAt).plain.our.par.Out)
    (s6 : Say6 ρ W h K3) (I : InTail h) (P : PiecesAll h.S h.d.pwW) (hnl : h.S.atV.nl = 2)
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
  have hb : b.val < h.S.NP := b.isLt
  obtain ⟨w, hw, e1, ha, eb⟩ := piece_of P (b := b.val) b.isLt
  have hgd := getD_of hw
  have v1 := s6.below.ends (2 * b.val) (by omega)
  have v2 := s6.below.ends (2 * b.val + 1) (by omega)
  unfold endsV at v1 v2
  rw [if_pos (by omega), show 2 * b.val / 2 = b.val by omega, hgd] at v1
  rw [if_neg (by omega), show (2 * b.val + 1) / 2 = b.val by omega, hgd] at v2
  cases s with
  | false =>
    have e := weightMF_port (K3 := K3) m A.num L hS (Cc := Cc) (p := o.st) (ξ := ptN _ o) ha hnM hz hpt
      (by rw [eb, ← hnM]; exact hG.tVM b.val b.isLt)
    rw [eb] at e
    exact end_of _ o (b, false) _ (Sum.elim m u) _ _ (hs b).1 e v1
  | true =>
    exact end_of _ o (b, true) _ (Sum.elim m u) _ _ (hs b).2
      (valueMF_port m A L hV (Cc := Cc) (p := o.st) (ξ := ptN _ o) (b := b.val) e1.symm hnl hr
        hzc hξ hyn hgam (by rw [e1]; exact hG.qVM b.val b.isLt) (I.qVM b.val hb w hw).feat) v2

omit [Fintype Kf] in
/-- The line of claim 6. r0, r1, ra, rz: what was sent for the two sums, ACC and ZC; k0, k1, ka, kz: the places of their mask entries; th: the drawn element. -/
theorem lineF_cl (s6 : Say6 ρ W h K3) (r0 r1 ra rz th : Kf) (k0 k1 ka kz : J₁)
    (h0 : W.slot h.d.sCl = r0 - m k0) (h1 : W.slot (h.d.sCl + 1) = r1 - m k1)
    (ha : W.slot h.d.sACC = ra - m ka) (hz : W.slot h.d.sZC = rz - m kz)
    (hth : ρ.val h.d.gam = th) :
    ((aSub (aAdd (hidF r0 k0) (hidF r1 k1))
      (aAdd (hidF ra ka) (aSmul th (hidF rz kz)))).claim :
        TWhole.Form Kf (J₁ ⊕ J₂)).Holds (Sum.elim m u) := by
  have v := s6.acc
  rw [h0, h1, ha, hz, hth] at v
  unfold Cb.Pv.Att.End.hidF
  rw [TWhole.Aff.claim_holds, val_aSub, val_aAdd, val_aAdd, val_aSmul, val_aSub, val_aSub,
    val_aSub, val_aSub, val_aConst, val_aConst, val_aConst, val_aConst, val_aEnt, val_aEnt,
    val_aEnt, val_aEnt]
  show r0 - m k0 + (r1 - m k1) - (ra - m ka + th * (rz - m kz)) = 0
  linear_combination v

end K5Law
