-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/BackParts.lean: kind K5: the parts of Claims/PortParts.lean the other
way round: where a claim of the library's ledger
holds, at the early entries m and the late entries u read off the world, the written form is worth
0.

The equalities of worths (the lemmas …F_port of Claims/PortFirst.lean, PortLate.lean, PortLin.lean)
are read from right to left. The premises are
those of the lemmas …F_at: the same public facts and the same dictionary of slots.

Main names:
  `end_back`: from the claim on an end value to "the slot's worth is the written reader's form's
    worth" (end_port, Johnson/Road/Rows/AttPortLate.lean,
    is an iff). `lin_back`: the converse of lin_holds (Johnson/Road/Rows/AttPortClLin.lean).
  `unitMF_bk`, `unitDF_bk`, `productF_bk`, `belowF_bk`, `onF_bk`, `scoreF_bk`, `keyF_bk`,
    `bitsF_bk`, `m6F_bk`, `lineF_bk`: the end values' claims,
    each for all its places at once, in the form of the fields of UnitAt and Say5 … Say8
      (Claims/Say.lean, Claims/Say58.lean).
  `zcF_bk`, `ibF_bk`, `msMF_bk`, `msDF_bk`, `highF_bk`, `cellF_bk`: the named scalars' claims.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PortParts

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset Cb
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Raw Calls Pub Step yn Dim)
open Cb.Pv.Att (OwnPar ptBelow)
open Cb.Pv.Att.End (LateLay AttTab EndLay endF endF_at ptN rowF plainCl ptOn Good6b Good6d Good8 Good11 Good12 GoodM
  Good16 Good18 GoodH clM clD clE clVM clVD clM6 clF clK clH lineF hidF aAdd aSub aSmul val_aSub val_aAdd val_aConst
  val_aSmul val_aEnt)

variable {Kf : Type} [Field Kf] [Fintype Kf] {M X : Type}
variable {ρ : Reading Kf} {W : World Kf} {K3 : ℕ} {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {tabOf : AttTab → ℕ}

/-- From the library-side claim on the end value to "slot = the written form's worth". -/
theorem end_back (T : Cb.Pv.Att.PlainSc Kf) [DecidableEq T.J] (o : T.our.par.Out) (a : T.A)
    (r : TWhole.Aff Kf (T.J ⊕ J₂)) (x : T.J ⊕ J₂ → Kf) (j : ℕ) (q : Aff)
    (hs : SlotAt W T o x j a) (hq : q.value ρ W = r.val x) (H : (endF T o a r).Holds x) :
    W.slot j = q.value ρ W := by
  have e := (end_port T o a r x j q hs hq).mpr H
  rwa [Aff.value_sub, Aff.value_slot, sub_eq_zero] at e

omit [Fintype Kf] in
/-- lin_holds' converse. -/
theorem lin_back {J₁ : Type} [Fintype J₁] [DecidableEq J₁] {u : J₂ → Kf} {m : J₁ → Kf} {q : Aff} {s : ℕ} {r : Kf} {k : J₁}
    {R : TWhole.Aff Kf (J₁ ⊕ J₂)} (hq : q.value ρ W = W.slot s - R.val (Sum.elim m u))
    (H : (Cb.Pv.Att.End.linF r k R).Holds (Sum.elim m u)) (hs : W.slot s = r - m k) : q.value ρ W = 0 := by
  unfold Cb.Pv.Att.End.linF Cb.Pv.Att.End.hidF at H
  rw [TWhole.Aff.claim_holds, val_aSub, val_aSub, val_aConst, val_aEnt] at H
  rw [hq, hs]
  exact H

section At
open Cb.Pv.Att (PlainSc stepSc3 step18 size18 bitsSc3)
open Cb.Pv.Att.End (pick keyR bitsR slotF rA12 rB12 rM6 rA16 rA21 linF rA6b rB6b rA6d rB6d rA8 rB8 rA11 rB11)
variable {J₁ : Type} [Fintype J₁] [DecidableEq J₁] {Y : LateLay AttTab J₂} {u : J₂ → Kf} {m : J₁ → Kf}
  {rd : (J₁ → Kf) → Raw → Kf} {inc : Pub Kf → J₁ → Kf}

theorem unitMF_bk {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    {k : Score} {tb : ScoreTables} (hQ : tabOf .tQm = tb.tQ) (hK : tabOf .tKm = tb.tK)
    (Cc : Calls) {cAt : Fin D.nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s6b.g D) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 D Cc rd .s6b inc wAt cAt).plain.our.par.Out)
    (I : InUnit h k tb) (P : PiecesAll h.S k.pw) (hq2 : h.S.atQ.nl = 2)
    (hk2 : h.S.atK.nl = 2)
    (hr : k.sc.r.size = D.lg + D.lP + (D.lP + 1) +
      h.S.cf.ldh)
    (hξ : ∀ j < D.lg + D.lP + (D.lP + 1) + h.S.cf.ldh,
      ptN _ o j = pt ρ k.sc.r j)
    (hG : Good6b D ls Y)
    (hs : ∀ b : Fin D.nb,
      SlotAt W (stepSc3 D Cc rd .s6b inc wAt cAt).plain o (Sum.elim m u)
          (k.sc.sEnd + 2 * b.val) (b, false) ∧
        SlotAt W (stepSc3 D Cc rd .s6b inc wAt cAt).plain o (Sum.elim m u)
          (k.sc.sEnd + (2 * b.val + 1)) (b, true))
    (H : ∀ a : Fin D.nb × Bool,
      (endF (stepSc3 D Cc rd .s6b inc wAt cAt).plain o a
        (pick (rA6b D ls Y (ptN _ o)) (rB6b D ls Y (ptN _ o))
          a)).Holds (Sum.elim m u)) :
    ∀ j < 2 * k.pw.size, W.slot (k.sc.sEnd + j) = (endsU h K3 k tb j).value ρ W := by
  subst hD hls
  refine (forall_pairs k.pw.size (fun j => W.slot (k.sc.sEnd + j) = (endsU h K3 k tb j).value ρ W)).1 fun b hb => ?_
  rw [P.1] at hb
  obtain ⟨w, hw, e1, ha, eb⟩ := piece_of P (b := b) hb
  have hg := getD_of hw
  obtain ⟨x1, x2⟩ := unitF_port (K3 := K3) (k := k) (tb := tb) m A L .tQm .tKm hQ hK rfl rfl hq2 hk2
    (n := (L5.dimOf h.S).lg + (L5.dimOf h.S).lP + ((L5.dimOf h.S).lP + 1))
    (by show h.S.cf.lgk ≤ h.S.cf.lgk + _ + _; omega) hr hξ ha
    (by rw [eb]; exact hG.tQ b hb)
    (by rw [e1]; exact hG.tK b hb) (I.tQ b w hw).feat (I.tK b w hw).feat
  rw [eb] at x1
  constructor
  · show W.slot (k.sc.sEnd + 2 * b) = (endsU h K3 k tb (2 * b)).value ρ W
    unfold endsU
    rw [if_pos (by omega), show 2 * b / 2 = b by omega, hg]
    exact end_back _ o (⟨b, hb⟩, false) _ (Sum.elim m u) _ _ (hs ⟨b, hb⟩).1 x1 (H (⟨b, hb⟩, false))
  · show W.slot (k.sc.sEnd + (2 * b + 1)) = (endsU h K3 k tb (2 * b + 1)).value ρ W
    unfold endsU
    rw [if_neg (by omega), show (2 * b + 1) / 2 = b by omega, hg]
    rw [e1] at x2 ⊢
    exact end_back _ o (⟨b, hb⟩, true) _ (Sum.elim m u) _ _ (hs ⟨b, hb⟩).2 x2 (H (⟨b, hb⟩, true))

theorem unitDF_bk {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    {k : Score} {tb : ScoreTables} (hQ : tabOf .tQd = tb.tQ) (hK : tabOf .tKd = tb.tK)
    (Cc : Calls) {cAt : Fin D.nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s6d.g D) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 D Cc rd .s6d inc wAt cAt).plain.our.par.Out)
    (I : InUnit h k tb) (P : PiecesAll h.S k.pw) (hq2 : h.S.atQ.nl = 2)
    (hk2 : h.S.atK.nl = 2)
    (hr : k.sc.r.size = D.lg + (D.lP + 1) + h.S.cf.ldh)
    (hξ : ∀ j < D.lg + (D.lP + 1) + h.S.cf.ldh,
      ptN _ o j = pt ρ k.sc.r j)
    (hG : Good6d D ls Y)
    (hs : ∀ b : Fin D.nb,
      SlotAt W (stepSc3 D Cc rd .s6d inc wAt cAt).plain o (Sum.elim m u)
          (k.sc.sEnd + 2 * b.val) (b, false) ∧
        SlotAt W (stepSc3 D Cc rd .s6d inc wAt cAt).plain o (Sum.elim m u)
          (k.sc.sEnd + (2 * b.val + 1)) (b, true))
    (H : ∀ a : Fin D.nb × Bool,
      (endF (stepSc3 D Cc rd .s6d inc wAt cAt).plain o a
        (pick (rA6d D ls Y (ptN _ o)) (rB6d D ls Y (ptN _ o))
          a)).Holds (Sum.elim m u)) :
    ∀ j < 2 * k.pw.size, W.slot (k.sc.sEnd + j) = (endsU h K3 k tb j).value ρ W := by
  subst hD hls
  refine (forall_pairs k.pw.size (fun j => W.slot (k.sc.sEnd + j) = (endsU h K3 k tb j).value ρ W)).1 fun b hb => ?_
  rw [P.1] at hb
  obtain ⟨w, hw, e1, ha, eb⟩ := piece_of P (b := b) hb
  have hg := getD_of hw
  obtain ⟨x1, x2⟩ := unitF_port (K3 := K3) (k := k) (tb := tb) m A L .tQd .tKd hQ hK rfl rfl hq2 hk2
    (n := (L5.dimOf h.S).lg + ((L5.dimOf h.S).lP + 1))
    (by show h.S.cf.lgk ≤ h.S.cf.lgk + _; omega) hr hξ ha
    (by rw [eb]; exact hG.tQ b hb)
    (by rw [e1]; exact hG.tK b hb) (I.tQ b w hw).feat (I.tK b w hw).feat
  rw [eb] at x1
  constructor
  · show W.slot (k.sc.sEnd + 2 * b) = (endsU h K3 k tb (2 * b)).value ρ W
    unfold endsU
    rw [if_pos (by omega), show 2 * b / 2 = b by omega, hg]
    exact end_back _ o (⟨b, hb⟩, false) _ (Sum.elim m u) _ _ (hs ⟨b, hb⟩).1 x1 (H (⟨b, hb⟩, false))
  · show W.slot (k.sc.sEnd + (2 * b + 1)) = (endsU h K3 k tb (2 * b + 1)).value ρ W
    unfold endsU
    rw [if_neg (by omega), show (2 * b + 1) / 2 = b by omega, hg]
    rw [e1] at x2 ⊢
    exact end_back _ o (⟨b, hb⟩, true) _ (Sum.elim m u) _ _ (hs ⟨b, hb⟩).2 x2 (H (⟨b, hb⟩, true))

theorem productF_bk {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (hE : tabOf .hE = h.t.hE) (hO : tabOf .qO = h.t.qO) (Cc : Calls)
    {cAt : Fin D.nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s8.g D) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 D Cc rd .s8 inc wAt cAt).plain.our.par.Out)
    (I : InTail h) (P : PiecesAll h.S h.d.pwW) (hnl : h.S.atO.nl = 2)
    (hr : h.S.cf.lgk ≤ h.d.scE.r.size) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lgk, ptN _ o j = pt ρ h.d.scE.r j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn D Cc (Pub.z o.st) j)
    (hG : Good8 D ls Y)
    (hs : ∀ b : Fin D.nb,
      SlotAt W (stepSc3 D Cc rd .s8 inc wAt cAt).plain o (Sum.elim m u)
          (h.d.scE.sEnd + 2 * b.val) (b, false) ∧
        SlotAt W (stepSc3 D Cc rd .s8 inc wAt cAt).plain o (Sum.elim m u)
          (h.d.scE.sEnd + (2 * b.val + 1)) (b, true))
    (H : ∀ a : Fin D.nb × Bool,
      (endF (stepSc3 D Cc rd .s8 inc wAt cAt).plain o a
        (pick (rA8 D Y (ptN _ o)) (rB8 D Cc ls Y o.st (ptN _ o))
          a)).Holds (Sum.elim m u)) :
    ∀ j < 2 * h.S.NP, W.slot (h.d.scE.sEnd + j) = (endsE h K3 j).value ρ W := by
  subst hD hls
  refine (forall_pairs h.S.NP (fun j => W.slot (h.d.scE.sEnd + j) = (endsE h K3 j).value ρ W)).1 fun b hb => ?_
  obtain ⟨w, hw, e1, ha, eb⟩ := piece_of P (b := b) hb
  have hgd := getD_of hw
  constructor
  · show W.slot (h.d.scE.sEnd + 2 * b) = (endsE h K3 (2 * b)).value ρ W
    unfold endsE
    rw [if_pos (by omega), show 2 * b / 2 = b by omega, hgd]
    have x1 := denF_port (K3 := K3) m A L hE (ξ := ptN _ o) ha hr hξ
      (by rw [eb]; exact hG.hE b hb)
    rw [eb] at x1
    exact end_back _ o (⟨b, hb⟩, false) _ (Sum.elim m u) _ _ (hs ⟨b, hb⟩).1 x1 (H (⟨b, hb⟩, false))
  · show W.slot (h.d.scE.sEnd + (2 * b + 1)) = (endsE h K3 (2 * b + 1)).value ρ W
    unfold endsE
    rw [if_neg (by omega), show (2 * b + 1) / 2 = b by omega, hgd]
    have x2 := outF_port (K3 := K3) m A L hO (Cc := Cc) (p := o.st) (ξ := ptN _ o) ha hnl hr hzc hξ hyn
      (by rw [eb]; exact hG.qO b hb) (I.qO b hb w hw).feat
    rw [eb] at x2
    exact end_back _ o (⟨b, hb⟩, true) _ (Sum.elim m u) _ _ (hs ⟨b, hb⟩).2 x2 (H (⟨b, hb⟩, true))

theorem belowF_bk {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls) {lmS : ℕ} (hlmS : lmS = h.S.cf.lmS)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (hS : tabOf .tVM = h.t.tVM) (hV : tabOf .qVM = h.t.qVM) (Cc : Calls)
    {cAt : Fin D.nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s11.g D) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 D Cc rd .s11 inc wAt cAt).plain.our.par.Out)
    (I : InTail h) (P : PiecesAll h.S h.d.pwW) (hnl : h.S.atV.nl = 2)
    (hnM : D.lM = h.S.nM) (hz : h.t.ptM.size = h.S.nM)
    (hr : h.S.cf.lgk ≤ h.d.vpm.r.size) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lgk, ptN _ o j = pt ρ h.d.vpm.r j)
    (hpt : ∀ j < h.S.nM - h.S.cf.lmS,
      pt ρ h.t.ptM j = ptBelow D Cc o.st (ptN _ o) j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn D Cc (Pub.z o.st) j)
    (hgam : ρ.val h.d.gam = Pub.th o.st) (hG : Good11 D ls lmS Y)
    (hs : ∀ b : Fin D.nb,
      SlotAt W (stepSc3 D Cc rd .s11 inc wAt cAt).plain o (Sum.elim m u)
          (h.d.vpm.sEnd + 2 * b.val) (b, false) ∧
        SlotAt W (stepSc3 D Cc rd .s11 inc wAt cAt).plain o (Sum.elim m u)
          (h.d.vpm.sEnd + (2 * b.val + 1)) (b, true))
    (H : ∀ a : Fin D.nb × Bool,
      (endF (stepSc3 D Cc rd .s11 inc wAt cAt).plain o a
        (pick (rA11 D Cc lmS Y o.st (ptN _ o))
          (rB11 D Cc ls Y o.st (ptN _ o)) a)).Holds (Sum.elim m u)) :
    ∀ j < 2 * h.S.NP, W.slot (h.d.vpm.sEnd + j) = (endsV h K3 h.d.vpm h.t.tVM h.t.ptM false h.t.qVM j).value ρ W := by
  subst hD hls hlmS
  refine (forall_pairs h.S.NP (fun j => W.slot (h.d.vpm.sEnd + j) = (endsV h K3 h.d.vpm h.t.tVM h.t.ptM false h.t.qVM j).value ρ W)).1 fun b hb => ?_
  obtain ⟨w, hw, e1, ha, eb⟩ := piece_of P (b := b) hb
  have hgd := getD_of hw
  constructor
  · show W.slot (h.d.vpm.sEnd + 2 * b) = (endsV h K3 h.d.vpm h.t.tVM h.t.ptM false h.t.qVM (2 * b)).value ρ W
    unfold endsV
    rw [if_pos (by omega), show 2 * b / 2 = b by omega, hgd]
    have e := weightMF_port (K3 := K3) m A.num L hS (Cc := Cc) (p := o.st) (ξ := ptN _ o) ha hnM hz hpt
      (by rw [eb, ← hnM]; exact hG.tVM b hb)
    rw [eb] at e
    exact end_back _ o (⟨b, hb⟩, false) _ (Sum.elim m u) _ _ (hs ⟨b, hb⟩).1 e (H (⟨b, hb⟩, false))
  · show W.slot (h.d.vpm.sEnd + (2 * b + 1)) = (endsV h K3 h.d.vpm h.t.tVM h.t.ptM false h.t.qVM (2 * b + 1)).value ρ W
    unfold endsV
    rw [if_neg (by omega), show (2 * b + 1) / 2 = b by omega, hgd]
    exact end_back _ o (⟨b, hb⟩, true) _ (Sum.elim m u) _ _ (hs ⟨b, hb⟩).2
      (valueMF_port m A L hV (Cc := Cc) (p := o.st) (ξ := ptN _ o) (b := b) e1.symm hnl hr
        hzc hξ hyn hgam (by rw [e1]; exact hG.qVM b hb) (I.qVM b hb w hw).feat) (H (⟨b, hb⟩, true))

theorem onF_bk {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls) {lmS : ℕ} (hlmS : lmS = h.S.cf.lmS)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) (Cc : Calls) {cAt : Fin D.nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s12.g D) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 D Cc rd .s12 inc wAt cAt).plain.our.par.Out)
    (I : InTail h) (P : PiecesAll h.S h.d.pwW) (hnl : h.S.atV.nl = 2)
    (hnD : D.lD = h.S.nD) (hz : h.t.ptD.size = h.S.nD)
    (hr : h.S.cf.lgk ≤ h.d.vpd.r.size) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lgk, ptN _ o j = pt ρ h.d.vpd.r j)
    (hpt : ∀ j < h.S.nD - h.S.cf.lmS,
      pt ρ h.t.ptD j = ptOn D Cc o.st (ptN _ o) j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn D Cc (Pub.z o.st) j)
    (hgam : ρ.val h.d.gam = Pub.th o.st) (hG : Good12 D ls lmS Y)
    (hs : ∀ b : Fin D.nb,
      SlotAt W (stepSc3 D Cc rd .s12 inc wAt cAt).plain o (Sum.elim m u)
          (h.d.vpd.sEnd + 2 * b.val) (b, false) ∧
        SlotAt W (stepSc3 D Cc rd .s12 inc wAt cAt).plain o (Sum.elim m u)
          (h.d.vpd.sEnd + (2 * b.val + 1)) (b, true))
    (H : ∀ a : Fin D.nb × Bool,
      (endF (stepSc3 D Cc rd .s12 inc wAt cAt).plain o a
        (pick (rA12 D Cc lmS Y o.st (ptN _ o))
          (rB12 D Cc ls Y o.st (ptN _ o)) a)).Holds (Sum.elim m u)) :
    ∀ j < 2 * h.S.NP, W.slot (h.d.vpd.sEnd + j) = (endsV h K3 h.d.vpd h.t.tVD h.t.ptD true h.t.qVD j).value ρ W := by
  subst hD hls hlmS
  refine (forall_pairs h.S.NP (fun j => W.slot (h.d.vpd.sEnd + j) = (endsV h K3 h.d.vpd h.t.tVD h.t.ptD true h.t.qVD j).value ρ W)).1 fun b hb => ?_
  obtain ⟨w, hw, e1, ha, eb⟩ := piece_of P (b := b) hb
  have hgd := getD_of hw
  constructor
  · show W.slot (h.d.vpd.sEnd + 2 * b) = (endsV h K3 h.d.vpd h.t.tVD h.t.ptD true h.t.qVD (2 * b)).value ρ W
    unfold endsV
    rw [if_pos (by omega), show 2 * b / 2 = b by omega, hgd]
    have e := weightF_port (K3 := K3) m A.num L Tb (Cc := Cc) (p := o.st) (ξ := ptN _ o) ha hnD hz hpt
      (by rw [eb, ← hnD]; exact hG.tVD b hb)
    rw [eb] at e
    exact end_back _ o (⟨b, hb⟩, false) _ (Sum.elim m u) _ _ (hs ⟨b, hb⟩).1 e (H (⟨b, hb⟩, false))
  · show W.slot (h.d.vpd.sEnd + (2 * b + 1)) = (endsV h K3 h.d.vpd h.t.tVD h.t.ptD true h.t.qVD (2 * b + 1)).value ρ W
    unfold endsV
    rw [if_neg (by omega), show (2 * b + 1) / 2 = b by omega, hgd]
    exact end_back _ o (⟨b, hb⟩, true) _ (Sum.elim m u) _ _ (hs ⟨b, hb⟩).2
      (valueF_port m A L Tb (Cc := Cc) (p := o.st) (ξ := ptN _ o) (b := b) e1.symm hnl hr
        hzc hξ hyn hgam (by rw [e1]; exact hG.qVD b hb) (I.qVD b hb w hw).feat) (H (⟨b, hb⟩, true))

theorem scoreF_bk {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) (Cc : Calls) {cAt : Fin D.nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s16.g D) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 D Cc rd .s16 inc wAt cAt).plain.our.par.Out)
    (I : InTail h) (hnl : h.S.atQ.nl = 2)
    (hr : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh, ptN _ o j = pt ρ h.x.scF.r j)
    (hG : Good16 D ls Y)
    (hs : ∀ b : Fin D.nb,
      SlotAt W (stepSc3 D Cc rd .s16 inc wAt cAt).plain o (Sum.elim m u)
        (h.x.scF.sEnd + 2 * b.val) (b, false))
    (H : ∀ b : Fin D.nb,
      (endF (stepSc3 D Cc rd .s16 inc wAt cAt).plain o (b, false)
        (rA16 D ls Y (ptN _ o) b.val)).Holds (Sum.elim m u)) :
    ∀ b < h.S.NP, W.slot (h.x.scF.sEnd + 2 * b) =
      (Fo.readHeadT h K3 h.t.qF h.S.atQ (h.x.rg h.S) (h.x.rc h.S) (b / h.S.HA) (b % h.S.HA)).value ρ W := by
  subst hD hls
  intro b hb
  exact end_back _ o (⟨b, hb⟩, false) _ (Sum.elim m u) (h.x.scF.sEnd + 2 * b) _ (hs ⟨b, hb⟩)
    (queryF_port m A L Tb hnl hr hξ (hG.qF b hb) (I.qF b hb).feat) (H ⟨b, hb⟩)

theorem keyF_bk {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) {St' : Type} (f : St' → Pub Kf) (inc' : St' → J₁ → Kf)
    {wAt : PIdx (ldPartFmt Kf (size18 D).k (size18 D).deg ++
      [pDummy Kf ((size18 D).lt + 1)]) → J₁}
    {cAt : (size18 D).A → J₁}
    (o : ((step18 D rd inc wAt cAt).plain.pull f inc').our.par.Out)
    (I : InTail h) (hnl : h.S.atK.nl = 2)
    (hrF : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh)
    (hr : h.x.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk)
    (hξ : ∀ j < 2 * h.S.cf.lt + h.S.cf.lgk, ptN _ o j = pt ρ h.x.scd.r j)
    (hfn : ∀ j < h.S.cf.ldh, pt ρ (h.x.rc h.S) j = (f o.st).fn j)
    (hG : Good18 D ls Y)
    (hsK : ∀ l : Fin (size18 D).Lam,
      SlotAt W ((step18 D rd inc wAt cAt).plain.pull f inc') o (Sum.elim m u)
        (h.x.sKC + l.val) (.inl l))
    (hsB : ∀ (b : Fin (size18 D).pairs) (t : Fin (size18 D).lt),
      SlotAt W ((step18 D rd inc wAt cAt).plain.pull f inc') o (Sum.elim m u)
        (h.x.sIb h.S b.val t.val) (.inr (b, t)))
    (H : ∀ a : (size18 D).A,
      (endF ((step18 D rd inc wAt cAt).plain.pull f inc') o a
        (keyR D ls Y (f o.st) (ptN _ o) a)).Holds (Sum.elim m u)) :
    ∀ j < h.S.Lam + h.S.NP * h.S.cf.lt, W.slot (h.x.scd.sEnd + j) = (endsK h K3 j).value ρ W := by
  subst hD hls
  have hlT := pub_lT A
  refine (forall_block h.S.Lam h.S.NP h.S.cf.lt
    (fun j => W.slot (h.x.scd.sEnd + j) = (endsK h K3 j).value ρ W)).1 ⟨fun l hl => ?_, fun b hb t ht => ?_⟩
  · show W.slot (h.x.scd.sEnd + l) = (endsK h K3 l).value ρ W
    rw [endsK_lam h K3 hl]
    exact end_back _ o (.inl ⟨l, hl⟩) _ (Sum.elim m u) (h.x.sKC + l) _ (hsK ⟨l, hl⟩)
      (keyF_port m A L Tb hnl hrF hr hξ hfn (hG.qKx l hl) (I.qKx l hl).feat) (H (.inl ⟨l, hl⟩))
  · show W.slot (h.x.scd.sEnd + (h.S.Lam + b * h.S.cf.lt + t)) = (endsK h K3 (h.S.Lam + b * h.S.cf.lt + t)).value ρ W
    have ht' : t < (size18 (L5.dimOf h.S)).lt := by
      have e : (size18 (L5.dimOf h.S)).lt = (L5.dimOf h.S).lT := rfl
      omega
    rw [endsK_bit h K3 b ht]
    exact end_back _ o (.inr (⟨b, hb⟩, ⟨t, ht'⟩)) _ (Sum.elim m u) (h.x.sIb h.S b t) _ (hsB ⟨b, hb⟩ ⟨t, ht'⟩)
      (ibitF_port m A L Tb hb hr hξ (hG.hPi b hb t ht')) (H (.inr (⟨b, hb⟩, ⟨t, ht'⟩)))

theorem bitsF_bk {D : Dim} (hD : D = L5.dimOf h.S) {kap : ℕ} (hkap : kap = 4)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) {cAt : Fin D.nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (D.lT + D.lg + kap) (fun _ => 3) ++
      [pDummy Kf 2]) → J₁}
    (o : (bitsSc3 kap D rd inc wAt cAt).plain.our.par.Out)
    (hr : h.x.scH.r.size = h.S.cf.lt + h.S.cf.lgk + 4)
    (hξ : ∀ j < h.S.cf.lt + h.S.cf.lgk + 4, ptN _ o j = pt ρ h.x.scH.r j)
    (hG : GoodH D Y)
    (hs : ∀ b : Fin D.nb,
      SlotAt W (bitsSc3 kap D rd inc wAt cAt).plain o (Sum.elim m u)
          (h.x.scH.sEnd + 2 * b.val) (b, false) ∧
        SlotAt W (bitsSc3 kap D rd inc wAt cAt).plain o (Sum.elim m u)
          (h.x.scH.sEnd + (2 * b.val + 1)) (b, true))
    (H : ∀ a : Fin D.nb × Bool,
      (endF (bitsSc3 kap D rd inc wAt cAt).plain o a
        (bitsR D Y rd inc kap cAt wAt o a)).Holds (Sum.elim m u)) :
    ∀ j < 2 * h.S.NP, W.slot (h.x.scH.sEnd + j) = (endsH h K3 j).value ρ W := by
  subst hD hkap
  have hlT := pub_lT A
  refine (forall_pairs h.S.NP (fun j => W.slot (h.x.scH.sEnd + j) = (endsH h K3 j).value ρ W)).1 fun b hb => ?_
  have e := bitsF_port (K3 := K3) m A L Tb hb hr hξ
    (fun k hk => hG.hR2 b hb k (by rw [hlT]; exact hk))
  have ev : W.slot (h.x.scH.sEnd + 2 * b) = (bitsF h K3 b).value ρ W :=
    end_back _ o (⟨b, hb⟩, false) _ (Sum.elim m u) _ _ (hs ⟨b, hb⟩).1 e (H (⟨b, hb⟩, false))
  constructor
  · show W.slot (h.x.scH.sEnd + 2 * b) = (endsH h K3 (2 * b)).value ρ W
    unfold endsH
    rw [if_pos (by omega), show 2 * b / 2 = b by omega]
    exact ev
  · show W.slot (h.x.scH.sEnd + (2 * b + 1)) = (endsH h K3 (2 * b + 1)).value ρ W
    unfold endsH
    rw [if_neg (by omega), show (2 * b + 1) / 2 = b by omega, Aff.value_sub, Aff.value_ofConst, ρ.one, ← ev]
    have sA : (slotF (J₂ := J₂) (bitsSc3 4 (L5.dimOf h.S) rd inc wAt cAt).plain o (⟨b, hb⟩, false)).val
        (Sum.elim m u) = W.slot (h.x.scH.sEnd + 2 * b) := by
      unfold Cb.Pv.Att.End.slotF
      rw [val_aSub, val_aConst, val_aSmul, val_aEnt]
      exact (hs ⟨b, hb⟩).1.symm
    have Ht := H (⟨b, hb⟩, true)
    rw [endF_at] at Ht
    have Ht' : _ = (Cb.Pv.Att.End.aSub
      (slotF (bitsSc3 4 (L5.dimOf h.S) rd inc wAt cAt).plain o (⟨b, hb⟩, false))
      (Cb.Pv.Att.End.aConst 1)).val (Sum.elim m u) := Ht
    rw [val_aSub, val_aConst, sA] at Ht'
    rw [← Ht']
    exact (hs ⟨b, hb⟩).2

omit [Fintype Kf] in
theorem m6F_bk {D : Dim} (hD : D = L5.dimOf h.S)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) (p : Pub Kf)
    (htg : h.x.tg.size = h.S.cf.lgk) (hp : ∀ j < h.S.cf.lgk, pt ρ h.x.tg j = p.tg j)
    (hG : GoodM D Y) (s : ℕ → Kf) (k : ℕ → J₁)
    (hs : ∀ b < h.S.NP, W.slot (h.x.sM6 + b) = s b - m (k b))
    (H : ∀ b < h.S.NP, (linF (s b) (k b) (rM6 D Y p b)).Holds (Sum.elim m u)) :
    ∀ b < h.S.NP, W.slot (h.x.sM6 + b) =
      (Fo.readMaximumF h K3 h.t.hT h.x.tg (b / h.S.HA) (b % h.S.HA)).value ρ W := by
  subst hD
  intro b hb
  have e := maxF_port (K3 := K3) m A L Tb hb htg hp (hG.hT b hb)
  have Hb := H b hb
  unfold Cb.Pv.Att.End.linF Cb.Pv.Att.End.hidF at Hb
  rw [TWhole.Aff.claim_holds, val_aSub, val_aSub, val_aConst, val_aEnt] at Hb
  rw [hs b hb, e]
  exact sub_eq_zero.mp Hb

omit [Fintype Kf] in
/-- The line of claim 6. -/
theorem lineF_bk (r0 r1 ra rz th : Kf) (k0 k1 ka kz : J₁)
    (h0 : W.slot h.d.sCl = r0 - m k0) (h1 : W.slot (h.d.sCl + 1) = r1 - m k1)
    (ha : W.slot h.d.sACC = ra - m ka) (hz : W.slot h.d.sZC = rz - m kz)
    (hth : ρ.val h.d.gam = th)
    (H : ((aSub (aAdd (hidF r0 k0) (hidF r1 k1))
      (aAdd (hidF ra ka) (aSmul th (hidF rz kz)))).claim :
        TWhole.Form Kf (J₁ ⊕ J₂)).Holds (Sum.elim m u)) :
    W.slot h.d.sCl + W.slot (h.d.sCl + 1) - W.slot h.d.sACC - ρ.val h.d.gam * W.slot h.d.sZC = 0 := by
  unfold Cb.Pv.Att.End.hidF at H
  rw [TWhole.Aff.claim_holds, val_aSub, val_aAdd, val_aAdd, val_aSmul, val_aSub, val_aSub,
    val_aSub, val_aSub, val_aConst, val_aConst, val_aConst, val_aConst, val_aEnt, val_aEnt,
    val_aEnt, val_aEnt] at H
  have H' : r0 - m k0 + (r1 - m k1) - (ra - m ka + th * (rz - m kz)) = 0 := H
  rw [h0, h1, ha, hz, hth]
  linear_combination H'

omit [Fintype Kf]
open Inst.Model.AttSeg (Reg Fam KSc wp inn zg zgD yg xg)
open Cb.Pv.Att.End (rvF LinGood IsPlane)

theorem zcF_bk {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls) {lmS : ℕ} (hlmS : lmS = h.S.cf.lmS)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Cc : Calls) (z : ℕ → Kf)
    (hG : LinGood D ls lmS Y) (r : Kf) (k : J₁) (hT : tabOf .hW = h.t.hW) (P : PiecesAll h.S h.d.pwW)
    (hz : h.S.cf.lgk ≤ h.d.zgW.size)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgW j = yg D Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwW.getD b default).wp = wp D Cc z .w3 b)
    (hs : W.slot h.d.sZC = r - m k)
    (H : (linF r k (rvF D Cc ls lmS Y z .zc)).Holds (Sum.elim m u)) :
    (Fo.lessF (Aff.slot h.d.sZC) h.d.pwW fun w =>
      Fo.readDenominatorF h K3 h.t.hW h.d.zgW w.lam w.a).value ρ W = 0 := by
  subst hD hls hlmS
  exact lin_back (zcF_port m A L hT P Cc z hz hvg hw (fun b hb g hg l hl => hG.hW b hb g hg l hl)) H hs

theorem ibF_bk {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls) {lmS : ℕ} (hlmS : lmS = h.S.cf.lmS)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Cc : Calls) (z : ℕ → Kf)
    (hG : LinGood D ls lmS Y) (r : Kf) (k : J₁) (i : ℕ) (hi : i < D.lT) (hT : tabOf .hX = h.t.hX)
    (P : PiecesAll h.S h.d.pwX) (hz : h.S.cf.lgk ≤ h.d.zgX.size)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgX j = xg D Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwX.getD b default).wp = wp D Cc z .x3 b)
    (hs : W.slot (h.d.sIB + i) = r - m k)
    (H : (linF r k (rvF D Cc ls lmS Y z (.ib i))).Holds (Sum.elim m u)) :
    (Fo.lessF (Aff.slot (h.d.sIB + i)) h.d.pwX fun w =>
      Fo.readIndexBitF h K3 h.t.hX h.d.zgX w.lam w.a i).value ρ W = 0 := by
  subst hD hls hlmS
  exact lin_back (ibF_port m A L hT P Cc z i hz hvg hw (fun b hb g hg => hG.hX i hi b hb g hg)) H hs

theorem msMF_bk {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls) {lmS : ℕ} (hlmS : lmS = h.S.cf.lmS)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Cc : Calls) (z : ℕ → Kf)
    (hG : LinGood D ls lmS Y) (r : Kf) (k : J₁) {t s : ℕ} (hT : tabOf .tMm = t) {pw : Array PW} (P : PiecesAll h.S pw)
    {zz : Array E} (hz : h.S.cf.lgk ≤ zz.size)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ zz j = zg D Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp D Cc z .m2 b)
    (hs : W.slot s = r - m k)
    (H : (linF r k (rvF D Cc ls lmS Y z (.ms .M))).Holds (Sum.elim m u)) :
    (Fo.lessF (Aff.slot s) pw fun w => Fo.readMaximumF h K3 t zz w.lam w.a).value ρ W = 0 := by
  subst hD hls hlmS
  exact lin_back (msF_port m A L .tMm hT rfl s P Cc z .m2 hz hvg hw
    (fun b hb g hg l hl => hG.tMm b hb g hg l hl)) H hs

theorem msDF_bk {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls) {lmS : ℕ} (hlmS : lmS = h.S.cf.lmS)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Cc : Calls) (z : ℕ → Kf)
    (hG : LinGood D ls lmS Y) (r : Kf) (k : J₁) {t s : ℕ} (hT : tabOf .tMd = t) {pw : Array PW} (P : PiecesAll h.S pw)
    {zz : Array E} (hz : h.S.cf.lgk ≤ zz.size)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ zz j = zgD D Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp D Cc z .d2 b)
    (hs : W.slot s = r - m k)
    (H : (linF r k (rvF D Cc ls lmS Y z (.ms .D))).Holds (Sum.elim m u)) :
    (Fo.lessF (Aff.slot s) pw fun w => Fo.readMaximumF h K3 t zz w.lam w.a).value ρ W = 0 := by
  subst hD hls hlmS
  exact lin_back (msF_port m A L .tMd hT rfl s P Cc z .d2 hz hvg hw
    (fun b hb g hg l hl => hG.tMd b hb g hg l hl)) H hs

theorem highF_bk {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls) {lmS : ℕ} (hlmS : lmS = h.S.cf.lmS)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Cc : Calls) (z : ℕ → Kf)
    (hG : LinGood D ls lmS Y) (r : Kf) (k : J₁) (first : Bool) (fam : Fam) {s : ℕ} (hT : tabOf .tO = h.t.tO) {pw : Array PW}
    (P : PiecesAll h.S pw) {zz zc : Array E} (hzg : h.S.cf.lgk ≤ zz.size)
    (hzc : zc.size = h.S.cf.ldh)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ zz j = yg D Cc z j)
    (hvn : ∀ j < h.S.cf.ldh, pt ρ zc j = yn D Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp D Cc z fam b)
    (hfe : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk,
      headFeat (if first then Attention.atRh h.S else Attention.atRhp h.S)
        (g * h.S.HA + (pw.getD b default).a) h.S.dh = .ok ((g * h.S.HA + (pw.getD b default).a) * h.S.dh))
    (hs : W.slot s = r - m k)
    (H : (linF r k (Cb.Pv.Att.End.overPairs D Cc z fam fun b =>
        Cb.Pv.Att.End.rdLong D ls Y .tO (yg D Cc z)
          (yn D Cc z) 1
          fun _ g => if first then Raw.qh b g 0 0 else Raw.qh' b g 0 0)).Holds (Sum.elim m u)) :
    (Fo.lessF (Aff.slot s) pw fun w => Fo.readHeadT h K3 h.t.tO
      (if first then Attention.atRh h.S else Attention.atRhp h.S) zz zc w.lam w.a).value ρ W = 0 := by
  subst hD hls hlmS
  cases first with
  | true =>
    exact lin_back (highF_port m A L hT (X := Attention.atRh h.S) rfl
      (fun b g n => .qh b g 0 n) (fun _ _ _ => rfl) (fun _ _ _ => rfl) s P Cc z fam hzg hzc hvg
      hvn hw (fun b hb g hg ch hch => (hG.tO b hb g hg ch hch).1) hfe) H hs
  | false =>
    exact lin_back (highF_port m A L hT (X := Attention.atRhp h.S) rfl
      (fun b g n => .qh' b g 0 n) (fun _ _ _ => rfl) (fun _ _ _ => rfl) s P Cc z fam hzg hzc hvg
      hvn hw (fun b hb g hg ch hch => (hG.tO b hb g hg ch hch).2) hfe) H hs

theorem cellF_bk {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls) {lmS : ℕ} (hlmS : lmS = h.S.cf.lmS)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Cc : Calls) (z : ℕ → Kf)
    (hG : LinGood D ls lmS Y) (r : Kf) (k : J₁) (fam : Fam) (hf : IsPlane fam) (x : ℕ) (hx : x < 5) {s : ℕ}
    (hT : tabOf .tA = h.t.tA) {pw : Array PW} (P : PiecesAll h.S pw) {zz : Array E} {isD : Bool}
    (hreg : fam.reg = if isD then Reg.D else Reg.M)
    (hnb : (if isD then h.S.nD else h.S.nM) = fam.l D)
    (hz : zz.size = fam.l D)
    (hvz : ∀ j < fam.l D - h.S.cf.lmS,
      pt ρ zz j = inn D Cc z fam j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp D Cc z fam b)
    (hs : W.slot s = r - m k)
    (H : (linF r k (rvF D Cc ls lmS Y z (.cell fam x))).Holds
        (Sum.elim m u)) :
    (Fo.lessF (Aff.slot s) pw fun w => Fo.planeF h K3 h.t.tA x w.lam w.a zz isD).value ρ W = 0 := by
  subst hD hls hlmS
  exact lin_back (cellF_port m L hT s x P Cc z fam fam.reg hreg hnb hz hvz hw
    (fun b hb hi hh => hG.tA fam x b hf hx hb hi hh)) H hs

end At

end K5Law

#print axioms K5Law.unitMF_bk
#print axioms K5Law.keyF_bk
#print axioms K5Law.bitsF_bk
#print axioms K5Law.highF_bk
