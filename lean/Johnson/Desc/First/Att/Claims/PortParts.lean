-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PortParts.lean: kind K5: the library's ledger of the own rounds'
claims (Cb/Pv/Att/End/Cl.lean: ownCl L Q u: fourteen parts, in the order in which the verifier adds
the claims), part by part, from what the kind's claims say: at any parameters P : OwnPar, letters L
: EndLay P J₂ and run u : P.Run whose sizes are the shape's, at x := Sum.elim (P.msg m) ul, ul any
values of the late entries that meet the dictionary LateAt.

Main names:
  `SizesAre P L h`: P.D = L5.dimOf h.S; P.kap = 4; L.ls = h.S.ls; L.lmS = h.S.cf.lmS.
  `…_at`: the twins of Johnson/Desc/First/Att/Claims/PortCl.lean,
    Johnson/Desc/First/Att/Claims/PortClFirst.lean and Johnson/Desc/First/Att/Claims/PortClLin.lean
    at sizes D, ls, lmS, kap that are the shape's: the statement with these four names in the
    shape's place; the proof: subst, then the twin.
  `plainCl_holds`, `linCl_holds`, `PlanePts`, `MaxIs`, `DivIs`, `slotEh`, `plane_holds`, `unit_lin`.
  Thirteen parts: `clM0_holds`, `clM_holds`, `clD0_holds`, `clD_holds`, `clE0_holds`, `clE_holds`,
    `lineF_holds`, `clVM_holds`, `clVD_holds`, `clM6_holds`, `clF_holds`, `clK_holds`, `clH_holds`.
  `ownCl_of_parts`: the fourteen give ∀ f ∈ ownCl L Q u, f.Holds x. `ownCl_pull`: at ul := the late
    entries' meant values that is ∀ f ∈ ownCl L Q u, (pullF (attA L u) f).Holds (P.msg m).
Taken as given by the parts: AttPub; LateAt; where the tables begin (tabOf); what the claims say
(Say5 … Say8, UnitAt, PlanesSay); InTail and InUnit; PiecesAll and the library's weights; the
lengths; that the output statements' points and challenges are the verifier's; the premises on names
(Good…); SlotAt and "W.slot s = sent − mask"; and hrow: the claim on the sumcheck's row (rowF),
which is not treated here.
Limits: the fourteenth part, joinF, is a premise of ownCl_of_parts. At ul := the meant values
(ownCl_pull) LateAt says that the world's entries of the vector of tables are the meant values: that
the tables are true: it is what the smallness test is meant to give; not shown in this file or in
what it imports. "No table is taken to be true" holds of the parts while ul is free, not of their
use in ownCl_pull. DivIs.fe (the lawful heads of the four readers on tO) is paid in
Johnson/Desc/First/Att/Claims/InHigh.lean.
Used: as Johnson/Desc/First/Att/Claims/PortClFirst.lean and
Johnson/Desc/First/Att/Claims/PortClLin.lean; the library's OwnPar, Run, EndLay, JoinLay, ownCl and
its parts, attA, Cb.Sub.pullF, pullF_holds.

Nothing is claimed on soundness, completeness or hiding.

-/
import Cb.Pv.Att.End.Cl
import Johnson.Desc.First.Att.Claims.PortClFirst
import Johnson.Desc.First.Att.Claims.PortClLin

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset Cb
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Raw Calls Pub Step yn Dim)
open Cb.Pv.Att (OwnPar ptBelow)
open Cb.Pv.Att.End (LateLay AttTab EndLay endF ptN rowF plainCl ptOn Good6b Good6d Good8 Good11 Good12 GoodM
  Good16 Good18 GoodH clM clD clE clVM clVD clM6 clF clK clH lineF)

variable {Kf : Type} [Field Kf] [Fintype Kf] {M X : Type}
variable {ρ : Reading Kf} {W : World Kf} {K3 : ℕ} {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {tabOf : AttTab → ℕ}

/-- The row and the listed end values. -/
theorem plainCl_holds {T : Cb.Pv.Att.PlainSc Kf} [DecidableEq T.J] (o : T.our.par.Out) (l : List T.A)
    (r : T.A → TWhole.Aff Kf (T.J ⊕ J₂)) (x : T.J ⊕ J₂ → Kf) (hrow : (rowF T o).Holds x)
    (he : ∀ a, (endF T o a (r a)).Holds x) : ∀ f ∈ plainCl T o l r, f.Holds x := by
  intro f hf
  unfold plainCl at hf
  rcases List.mem_cons.1 hf with rfl | hf'
  · exact hrow
  · obtain ⟨a, _, rfl⟩ := List.mem_map.1 hf'
    exact he a

/-! ### the twins at sizes that are the shape's: their statements with D, ls, lmS, kap in the shape's place -/

section At
open Cb.Pv.Att (PlainSc stepSc3 step18 size18 bitsSc3)
open Cb.Pv.Att.End (pick keyR bitsR slotF rA12 rB12 rM6 rA16 rA21 linF rA6b rB6b rA6d rB6d rA8 rB8 rA11 rB11)
variable {J₁ : Type} [Fintype J₁] [DecidableEq J₁] {Y : LateLay AttTab J₂} {u : J₂ → Kf} {m : J₁ → Kf}
  {rd : (J₁ → Kf) → Raw → Kf} {inc : Pub Kf → J₁ → Kf}

theorem unitMF_at {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    {k : Score} {tb : ScoreTables} {pc : PlaneClaim} (hQ : tabOf .tQm = tb.tQ) (hK : tabOf .tKm = tb.tK)
    (Cc : Calls) {cAt : Fin D.nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s6b.g D) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 D Cc rd .s6b inc wAt cAt).plain.our.par.Out)
    (U : UnitAt ρ W h K3 k tb pc) (I : InUnit h k tb) (P : PiecesAll h.S k.pw) (hq2 : h.S.atQ.nl = 2)
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
    (a : Fin D.nb × Bool) :
    (endF (stepSc3 D Cc rd .s6b inc wAt cAt).plain o a
      (pick (rA6b D ls Y (ptN _ o)) (rB6b D ls Y (ptN _ o))
        a)).Holds (Sum.elim m u) := by
  subst hD hls
  exact unitMF_cl A L hQ hK Cc o U I P hq2 hk2 hr hξ hG hs a

theorem unitDF_at {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    {k : Score} {tb : ScoreTables} {pc : PlaneClaim} (hQ : tabOf .tQd = tb.tQ) (hK : tabOf .tKd = tb.tK)
    (Cc : Calls) {cAt : Fin D.nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s6d.g D) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 D Cc rd .s6d inc wAt cAt).plain.our.par.Out)
    (U : UnitAt ρ W h K3 k tb pc) (I : InUnit h k tb) (P : PiecesAll h.S k.pw) (hq2 : h.S.atQ.nl = 2)
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
    (a : Fin D.nb × Bool) :
    (endF (stepSc3 D Cc rd .s6d inc wAt cAt).plain o a
      (pick (rA6d D ls Y (ptN _ o)) (rB6d D ls Y (ptN _ o))
        a)).Holds (Sum.elim m u) := by
  subst hD hls
  exact unitDF_cl A L hQ hK Cc o U I P hq2 hk2 hr hξ hG hs a

theorem productF_at {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (hE : tabOf .hE = h.t.hE) (hO : tabOf .qO = h.t.qO) (Cc : Calls)
    {cAt : Fin D.nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s8.g D) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 D Cc rd .s8 inc wAt cAt).plain.our.par.Out)
    (s5 : Say5 ρ W h K3) (I : InTail h) (P : PiecesAll h.S h.d.pwW) (hnl : h.S.atO.nl = 2)
    (hr : h.S.cf.lgk ≤ h.d.scE.r.size) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lgk, ptN _ o j = pt ρ h.d.scE.r j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn D Cc (Pub.z o.st) j)
    (hG : Good8 D ls Y)
    (hs : ∀ b : Fin D.nb,
      SlotAt W (stepSc3 D Cc rd .s8 inc wAt cAt).plain o (Sum.elim m u)
          (h.d.scE.sEnd + 2 * b.val) (b, false) ∧
        SlotAt W (stepSc3 D Cc rd .s8 inc wAt cAt).plain o (Sum.elim m u)
          (h.d.scE.sEnd + (2 * b.val + 1)) (b, true))
    (a : Fin D.nb × Bool) :
    (endF (stepSc3 D Cc rd .s8 inc wAt cAt).plain o a
      (pick (rA8 D Y (ptN _ o)) (rB8 D Cc ls Y o.st (ptN _ o))
        a)).Holds (Sum.elim m u) := by
  subst hD hls
  exact productF_cl A L hE hO Cc o s5 I P hnl hr hzc hξ hyn hG hs a

theorem belowF_at {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls) {lmS : ℕ} (hlmS : lmS = h.S.cf.lmS)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (hS : tabOf .tVM = h.t.tVM) (hV : tabOf .qVM = h.t.qVM) (Cc : Calls)
    {cAt : Fin D.nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s11.g D) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 D Cc rd .s11 inc wAt cAt).plain.our.par.Out)
    (s6 : Say6 ρ W h K3) (I : InTail h) (P : PiecesAll h.S h.d.pwW) (hnl : h.S.atV.nl = 2)
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
    (a : Fin D.nb × Bool) :
    (endF (stepSc3 D Cc rd .s11 inc wAt cAt).plain o a
      (pick (rA11 D Cc lmS Y o.st (ptN _ o))
        (rB11 D Cc ls Y o.st (ptN _ o)) a)).Holds (Sum.elim m u) := by
  subst hD hls hlmS
  exact belowF_cl A L hS hV Cc o s6 I P hnl hnM hz hr hzc hξ hpt hyn hgam hG hs a

theorem onF_at {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls) {lmS : ℕ} (hlmS : lmS = h.S.cf.lmS)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) (Cc : Calls) {cAt : Fin D.nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s12.g D) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 D Cc rd .s12 inc wAt cAt).plain.our.par.Out)
    (s6 : Say6 ρ W h K3) (I : InTail h) (P : PiecesAll h.S h.d.pwW) (hnl : h.S.atV.nl = 2)
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
    (a : Fin D.nb × Bool) :
    (endF (stepSc3 D Cc rd .s12 inc wAt cAt).plain o a
      (pick (rA12 D Cc lmS Y o.st (ptN _ o))
        (rB12 D Cc ls Y o.st (ptN _ o)) a)).Holds (Sum.elim m u) := by
  subst hD hls hlmS
  exact onF_cl A L Tb Cc o s6 I P hnl hnD hz hr hzc hξ hpt hyn hgam hG hs a

theorem scoreF_at {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) (Cc : Calls) {cAt : Fin D.nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (Step.s16.g D) (fun _ => 3) ++ [pDummy Kf 2]) → J₁}
    (o : (stepSc3 D Cc rd .s16 inc wAt cAt).plain.our.par.Out)
    (s7 : Say7 ρ W h K3) (I : InTail h) (hnl : h.S.atQ.nl = 2)
    (hr : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh, ptN _ o j = pt ρ h.x.scF.r j)
    (hG : Good16 D ls Y)
    (hs : ∀ b : Fin D.nb,
      SlotAt W (stepSc3 D Cc rd .s16 inc wAt cAt).plain o (Sum.elim m u)
        (h.x.scF.sEnd + 2 * b.val) (b, false))
    (b : Fin D.nb) :
    (endF (stepSc3 D Cc rd .s16 inc wAt cAt).plain o (b, false)
      (rA16 D ls Y (ptN _ o) b.val)).Holds (Sum.elim m u) := by
  subst hD hls
  exact scoreF_cl A L Tb Cc o s7 I hnl hr hξ hG hs b

theorem keyF_at {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) {St' : Type} (f : St' → Pub Kf) (inc' : St' → J₁ → Kf)
    {wAt : PIdx (ldPartFmt Kf (size18 D).k (size18 D).deg ++
      [pDummy Kf ((size18 D).lt + 1)]) → J₁}
    {cAt : (size18 D).A → J₁}
    (o : ((step18 D rd inc wAt cAt).plain.pull f inc').our.par.Out)
    (s7 : Say7 ρ W h K3) (I : InTail h) (hnl : h.S.atK.nl = 2)
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
    (a : (size18 D).A) :
    (endF ((step18 D rd inc wAt cAt).plain.pull f inc') o a
      (keyR D ls Y (f o.st) (ptN _ o) a)).Holds (Sum.elim m u) := by
  subst hD hls
  exact keyF_cl A L Tb f inc' o s7 I hnl hrF hr hξ hfn hG hsK hsB a

theorem bitsF_at {D : Dim} (hD : D = L5.dimOf h.S) {kap : ℕ} (hkap : kap = 4)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) {cAt : Fin D.nb × Bool → J₁}
    {wAt : PIdx (ldPartFmt Kf (D.lT + D.lg + kap) (fun _ => 3) ++
      [pDummy Kf 2]) → J₁}
    (o : (bitsSc3 kap D rd inc wAt cAt).plain.our.par.Out)
    (s8 : Say8 ρ W h K3) (hr : h.x.scH.r.size = h.S.cf.lt + h.S.cf.lgk + 4)
    (hξ : ∀ j < h.S.cf.lt + h.S.cf.lgk + 4, ptN _ o j = pt ρ h.x.scH.r j)
    (hG : GoodH D Y)
    (hs : ∀ b : Fin D.nb,
      SlotAt W (bitsSc3 kap D rd inc wAt cAt).plain o (Sum.elim m u)
          (h.x.scH.sEnd + 2 * b.val) (b, false) ∧
        SlotAt W (bitsSc3 kap D rd inc wAt cAt).plain o (Sum.elim m u)
          (h.x.scH.sEnd + (2 * b.val + 1)) (b, true))
    (a : Fin D.nb × Bool) :
    (endF (bitsSc3 kap D rd inc wAt cAt).plain o a
      (bitsR D Y rd inc kap cAt wAt o a)).Holds (Sum.elim m u) := by
  subst hD hkap
  exact bitsF_cl A L Tb o s8 hr hξ hG hs a

omit [Fintype Kf] in
theorem m6F_at {D : Dim} (hD : D = L5.dimOf h.S)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u)
    (Tb : LateTabs h tabOf) (p : Pub Kf) (s7 : Say7 ρ W h K3)
    (htg : h.x.tg.size = h.S.cf.lgk) (hp : ∀ j < h.S.cf.lgk, pt ρ h.x.tg j = p.tg j)
    (hG : GoodM D Y) (s : ℕ → Kf) (k : ℕ → J₁)
    (hs : ∀ b < h.S.NP, W.slot (h.x.sM6 + b) = s b - m (k b)) (b : ℕ) (hb : b < h.S.NP) :
    (linF (s b) (k b) (rM6 D Y p b)).Holds (Sum.elim m u) := by
  subst hD
  exact m6F_cl A L Tb p s7 htg hp hG s k hs b hb

omit [Fintype Kf]
open Inst.Model.AttSeg (Reg Fam KSc wp inn zg zgD yg xg)
open Cb.Pv.Att.End (rvF LinGood IsPlane)

theorem zcF_at {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls) {lmS : ℕ} (hlmS : lmS = h.S.cf.lmS)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Cc : Calls) (z : ℕ → Kf)
    (hG : LinGood D ls lmS Y) (r : Kf) (k : J₁) (hT : tabOf .hW = h.t.hW) (P : PiecesAll h.S h.d.pwW)
    (hz : h.S.cf.lgk ≤ h.d.zgW.size)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgW j = yg D Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwW.getD b default).wp = wp D Cc z .w3 b)
    (v : (Fo.lessF (Aff.slot h.d.sZC) h.d.pwW fun w =>
      Fo.readDenominatorF h K3 h.t.hW h.d.zgW w.lam w.a).value ρ W = 0)
    (hs : W.slot h.d.sZC = r - m k) :
    (linF r k (rvF D Cc ls lmS Y z .zc)).Holds (Sum.elim m u) := by
  subst hD hls hlmS
  exact zcF_cl A L Cc z hG r k hT P hz hvg hw v hs

theorem ibF_at {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls) {lmS : ℕ} (hlmS : lmS = h.S.cf.lmS)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Cc : Calls) (z : ℕ → Kf)
    (hG : LinGood D ls lmS Y) (r : Kf) (k : J₁) (i : ℕ) (hi : i < D.lT) (hT : tabOf .hX = h.t.hX)
    (P : PiecesAll h.S h.d.pwX) (hz : h.S.cf.lgk ≤ h.d.zgX.size)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgX j = xg D Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwX.getD b default).wp = wp D Cc z .x3 b)
    (v : (Fo.lessF (Aff.slot (h.d.sIB + i)) h.d.pwX fun w =>
      Fo.readIndexBitF h K3 h.t.hX h.d.zgX w.lam w.a i).value ρ W = 0)
    (hs : W.slot (h.d.sIB + i) = r - m k) :
    (linF r k (rvF D Cc ls lmS Y z (.ib i))).Holds (Sum.elim m u) := by
  subst hD hls hlmS
  exact ibF_cl A L Cc z hG r k i hi hT P hz hvg hw v hs

theorem msMF_at {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls) {lmS : ℕ} (hlmS : lmS = h.S.cf.lmS)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Cc : Calls) (z : ℕ → Kf)
    (hG : LinGood D ls lmS Y) (r : Kf) (k : J₁) {t s : ℕ} (hT : tabOf .tMm = t) {pw : Array PW} (P : PiecesAll h.S pw)
    {zz : Array E} (hz : h.S.cf.lgk ≤ zz.size)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ zz j = zg D Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp D Cc z .m2 b)
    (v : (Fo.lessF (Aff.slot s) pw fun w => Fo.readMaximumF h K3 t zz w.lam w.a).value ρ W = 0)
    (hs : W.slot s = r - m k) :
    (linF r k (rvF D Cc ls lmS Y z (.ms .M))).Holds (Sum.elim m u) := by
  subst hD hls hlmS
  exact msMF_cl A L Cc z hG r k hT P hz hvg hw v hs

theorem msDF_at {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls) {lmS : ℕ} (hlmS : lmS = h.S.cf.lmS)
    (A : AttPub ρ h lid cf fs) (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Cc : Calls) (z : ℕ → Kf)
    (hG : LinGood D ls lmS Y) (r : Kf) (k : J₁) {t s : ℕ} (hT : tabOf .tMd = t) {pw : Array PW} (P : PiecesAll h.S pw)
    {zz : Array E} (hz : h.S.cf.lgk ≤ zz.size)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ zz j = zgD D Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp D Cc z .d2 b)
    (v : (Fo.lessF (Aff.slot s) pw fun w => Fo.readMaximumF h K3 t zz w.lam w.a).value ρ W = 0)
    (hs : W.slot s = r - m k) :
    (linF r k (rvF D Cc ls lmS Y z (.ms .D))).Holds (Sum.elim m u) := by
  subst hD hls hlmS
  exact msDF_cl A L Cc z hG r k hT P hz hvg hw v hs

theorem highF_at {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls) {lmS : ℕ} (hlmS : lmS = h.S.cf.lmS)
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
    (v : (Fo.lessF (Aff.slot s) pw fun w => Fo.readHeadT h K3 h.t.tO
      (if first then Attention.atRh h.S else Attention.atRhp h.S) zz zc w.lam w.a).value ρ W = 0)
    (hs : W.slot s = r - m k) :
    (linF r k (Cb.Pv.Att.End.overPairs D Cc z fam fun b =>
      Cb.Pv.Att.End.rdLong D ls Y .tO (yg D Cc z)
        (yn D Cc z) 1
        fun _ g => if first then Raw.qh b g 0 0 else Raw.qh' b g 0 0)).Holds (Sum.elim m u) := by
  subst hD hls hlmS
  exact highF_cl A L Cc z hG r k first fam hT P hzg hzc hvg hvn hw hfe v hs

theorem cellF_at {D : Dim} (hD : D = L5.dimOf h.S) {ls : ℕ} (hls : ls = h.S.ls) {lmS : ℕ} (hlmS : lmS = h.S.cf.lmS)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Cc : Calls) (z : ℕ → Kf)
    (hG : LinGood D ls lmS Y) (r : Kf) (k : J₁) (fam : Fam) (hf : IsPlane fam) (x : ℕ) (hx : x < 5) {s : ℕ}
    (hT : tabOf .tA = h.t.tA) {pw : Array PW} (P : PiecesAll h.S pw) {zz : Array E} {isD : Bool}
    (hreg : fam.reg = if isD then Reg.D else Reg.M)
    (hnb : (if isD then h.S.nD else h.S.nM) = fam.l D)
    (hz : zz.size = fam.l D)
    (hvz : ∀ j < fam.l D - h.S.cf.lmS,
      pt ρ zz j = inn D Cc z fam j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp D Cc z fam b)
    (v : (Fo.lessF (Aff.slot s) pw fun w => Fo.planeF h K3 h.t.tA x w.lam w.a zz isD).value ρ W = 0)
    (hs : W.slot s = r - m k) :
    (linF r k (rvF D Cc ls lmS Y z (.cell fam x))).Holds
      (Sum.elim m u) := by
  subst hD hls hlmS
  exact cellF_cl L Cc z hG r k fam hf x hx hT P hreg hnb hz hvz hw v hs

end At

/-- The parameters' sizes are the shape's. -/
structure SizesAre (P : OwnPar Kf M X) (L : EndLay P J₂) (h : Attention.Heard) : Prop where
  D : P.D = L5.dimOf h.S
  kap : P.kap = 4
  ls : L.ls = h.S.ls
  lmS : L.lmS = h.S.cf.lmS

/-! ### the ledger's parts -/

variable {P : OwnPar Kf M X} {L : EndLay P J₂} {u : P.Run} {ul : J₂ → Kf} {m : M}

local notation "XX" => Sum.elim (P.msg m) ul

/-- The unit below the diagonal. -/
theorem clM_holds (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs)
    (LA : LateAt W h K3 L.Y tabOf (placeAtt h.S) ul) {k : Score} {tb : ScoreTables} {pc : PlaneClaim}
    (hQ : tabOf .tQm = tb.tQ) (hK : tabOf .tKm = tb.tK) (U : UnitAt ρ W h K3 k tb pc) (I : InUnit h k tb)
    (Pc : PiecesAll h.S k.pw) (hq2 : h.S.atQ.nl = 2) (hk2 : h.S.atK.nl = 2)
    (hr : k.sc.r.size = P.D.lg + P.D.lP + (P.D.lP + 1) + h.S.cf.ldh)
    (hξ : ∀ j < P.D.lg + P.D.lP + (P.D.lP + 1) + h.S.cf.ldh, ptN P.uM.T u.oM j = pt ρ k.sc.r j)
    (hG : Good6b P.D L.ls L.Y)
    (hs : ∀ b : Fin P.D.nb, SlotAt W P.uM.T u.oM XX (k.sc.sEnd + 2 * b.val) (b, false) ∧
      SlotAt W P.uM.T u.oM XX (k.sc.sEnd + (2 * b.val + 1)) (b, true))
    (hrow : (rowF (J₂ := J₂) P.uM.T u.oM).Holds XX) : ∀ f ∈ clM L u, f.Holds XX :=
  plainCl_holds _ _ _ _ hrow fun a =>
    unitMF_at Z.D Z.ls A LA hQ hK P.C u.oM U I Pc hq2 hk2 hr hξ hG hs a

/-- The unit on the diagonal. -/
theorem clD_holds (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs)
    (LA : LateAt W h K3 L.Y tabOf (placeAtt h.S) ul) {k : Score} {tb : ScoreTables} {pc : PlaneClaim}
    (hQ : tabOf .tQd = tb.tQ) (hK : tabOf .tKd = tb.tK) (U : UnitAt ρ W h K3 k tb pc) (I : InUnit h k tb)
    (Pc : PiecesAll h.S k.pw) (hq2 : h.S.atQ.nl = 2) (hk2 : h.S.atK.nl = 2)
    (hr : k.sc.r.size = P.D.lg + (P.D.lP + 1) + h.S.cf.ldh)
    (hξ : ∀ j < P.D.lg + (P.D.lP + 1) + h.S.cf.ldh, ptN P.uD.T u.oD j = pt ρ k.sc.r j)
    (hG : Good6d P.D L.ls L.Y)
    (hs : ∀ b : Fin P.D.nb, SlotAt W P.uD.T u.oD XX (k.sc.sEnd + 2 * b.val) (b, false) ∧
      SlotAt W P.uD.T u.oD XX (k.sc.sEnd + (2 * b.val + 1)) (b, true))
    (hrow : (rowF (J₂ := J₂) P.uD.T u.oD).Holds XX) : ∀ f ∈ clD L u, f.Holds XX :=
  plainCl_holds _ _ _ _ hrow fun a =>
    unitDF_at Z.D Z.ls A LA hQ hK P.C u.oD U I Pc hq2 hk2 hr hξ hG hs a

/-- The denominator times the output. -/
theorem clE_holds (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs)
    (LA : LateAt W h K3 L.Y tabOf (placeAtt h.S) ul) (hE : tabOf .hE = h.t.hE) (hO : tabOf .qO = h.t.qO)
    (s5 : Say5 ρ W h K3) (I : InTail h) (Pc : PiecesAll h.S h.d.pwW) (hnl : h.S.atO.nl = 2)
    (hr : h.S.cf.lgk ≤ h.d.scE.r.size) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lgk, ptN P.sE.T u.oE j = pt ρ h.d.scE.r j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn P.D P.C (Pub.z u.oE.st) j)
    (hG : Good8 P.D L.ls L.Y)
    (hs : ∀ b : Fin P.D.nb, SlotAt W P.sE.T u.oE XX (h.d.scE.sEnd + 2 * b.val) (b, false) ∧
      SlotAt W P.sE.T u.oE XX (h.d.scE.sEnd + (2 * b.val + 1)) (b, true))
    (hrow : (rowF (J₂ := J₂) P.sE.T u.oE).Holds XX) : ∀ f ∈ clE L u, f.Holds XX :=
  plainCl_holds _ _ _ _ hrow fun a =>
    productF_at Z.D Z.ls A LA hE hO P.C u.oE s5 I Pc hnl hr hzc hξ hyn hG hs a

/-- The value product below the diagonal. -/
theorem clVM_holds (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs)
    (LA : LateAt W h K3 L.Y tabOf (placeAtt h.S) ul) (hS : tabOf .tVM = h.t.tVM)
    (hV : tabOf .qVM = h.t.qVM) (s6 : Say6 ρ W h K3) (I : InTail h) (Pc : PiecesAll h.S h.d.pwW)
    (hnl : h.S.atV.nl = 2) (hnM : P.D.lM = h.S.nM) (hz : h.t.ptM.size = h.S.nM)
    (hr : h.S.cf.lgk ≤ h.d.vpm.r.size) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lgk, ptN P.sVM.T u.oVM j = pt ρ h.d.vpm.r j)
    (hpt : ∀ j < h.S.nM - h.S.cf.lmS,
      pt ρ h.t.ptM j = ptBelow P.D P.C u.oVM.st (ptN P.sVM.T u.oVM) j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn P.D P.C (Pub.z u.oVM.st) j)
    (hgam : ρ.val h.d.gam = Pub.th u.oVM.st) (hG : Good11 P.D L.ls L.lmS L.Y)
    (hs : ∀ b : Fin P.D.nb, SlotAt W P.sVM.T u.oVM XX (h.d.vpm.sEnd + 2 * b.val) (b, false) ∧
      SlotAt W P.sVM.T u.oVM XX (h.d.vpm.sEnd + (2 * b.val + 1)) (b, true))
    (hrow : (rowF (J₂ := J₂) P.sVM.T u.oVM).Holds XX) : ∀ f ∈ clVM L u, f.Holds XX :=
  plainCl_holds _ _ _ _ hrow fun a =>
    belowF_at Z.D Z.ls Z.lmS A LA hS hV P.C u.oVM s6 I Pc hnl hnM hz hr hzc hξ hpt hyn hgam hG hs a

/-- The value product on the diagonal. -/
theorem clVD_holds (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs)
    (LA : LateAt W h K3 L.Y tabOf (placeAtt h.S) ul) (Tb : LateTabs h tabOf) (s6 : Say6 ρ W h K3)
    (I : InTail h) (Pc : PiecesAll h.S h.d.pwW) (hnl : h.S.atV.nl = 2) (hnD : P.D.lD = h.S.nD)
    (hz : h.t.ptD.size = h.S.nD) (hr : h.S.cf.lgk ≤ h.d.vpd.r.size) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lgk, ptN P.sVD.T u.oVD j = pt ρ h.d.vpd.r j)
    (hpt : ∀ j < h.S.nD - h.S.cf.lmS, pt ρ h.t.ptD j = ptOn P.D P.C u.oVD.st (ptN P.sVD.T u.oVD) j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn P.D P.C (Pub.z u.oVD.st) j)
    (hgam : ρ.val h.d.gam = Pub.th u.oVD.st) (hG : Good12 P.D L.ls L.lmS L.Y)
    (hs : ∀ b : Fin P.D.nb, SlotAt W P.sVD.T u.oVD XX (h.d.vpd.sEnd + 2 * b.val) (b, false) ∧
      SlotAt W P.sVD.T u.oVD XX (h.d.vpd.sEnd + (2 * b.val + 1)) (b, true))
    (hrow : (rowF (J₂ := J₂) P.sVD.T u.oVD).Holds XX) : ∀ f ∈ clVD L u, f.Holds XX :=
  plainCl_holds _ _ _ _ hrow fun a =>
    onF_at Z.D Z.ls Z.lmS A LA Tb P.C u.oVD s6 I Pc hnl hnD hz hr hzc hξ hpt hyn hgam hG hs a

/-- The score at the index: its row and its first end values. -/
theorem clF_holds (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs)
    (LA : LateAt W h K3 L.Y tabOf (placeAtt h.S) ul) (Tb : LateTabs h tabOf) (s7 : Say7 ρ W h K3)
    (I : InTail h) (hnl : h.S.atQ.nl = 2)
    (hr : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh, ptN P.sF.T u.oF j = pt ρ h.x.scF.r j)
    (hG : Good16 P.D L.ls L.Y)
    (hs : ∀ b : Fin P.D.nb, SlotAt W P.sF.T u.oF XX (h.x.scF.sEnd + 2 * b.val) (b, false))
    (hrow : (rowF (J₂ := J₂) P.sF.T u.oF).Holds XX) : ∀ f ∈ clF L u, f.Holds XX := by
  intro f hf
  unfold clF plainCl at hf
  rcases List.mem_cons.1 hf with rfl | hf'
  · exact hrow
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hf'
    unfold Cb.Pv.Att.End.firsts at ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.1 ha
    exact scoreF_at Z.D Z.ls A LA Tb P.C u.oF s7 I hnl hr hξ hG hs b

/-- The key at the index. -/
theorem clK_holds (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs)
    (LA : LateAt W h K3 L.Y tabOf (placeAtt h.S) ul) (Tb : LateTabs h tabOf) (s7 : Say7 ρ W h K3)
    (I : InTail h) (hnl : h.S.atK.nl = 2)
    (hrF : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh)
    (hr : h.x.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk)
    (hξ : ∀ j < 2 * h.S.cf.lt + h.S.cf.lgk, ptN P.sD.T u.oK j = pt ρ h.x.scd.r j)
    (hfn : ∀ j < h.S.cf.ldh, pt ρ (h.x.rc h.S) j = (Prod.fst u.oK.st).fn j)
    (hG : Good18 P.D L.ls L.Y)
    (hsK : ∀ l : Fin (Cb.Pv.Att.size18 P.D).Lam, SlotAt W P.sD.T u.oK XX (h.x.sKC + l.val) (.inl l))
    (hsB : ∀ (b : Fin (Cb.Pv.Att.size18 P.D).pairs) (t : Fin (Cb.Pv.Att.size18 P.D).lt),
      SlotAt W P.sD.T u.oK XX (h.x.sIb h.S b.val t.val) (.inr (b, t)))
    (hrow : (rowF (J₂ := J₂) P.sD.T u.oK).Holds XX) : ∀ f ∈ clK L u, f.Holds XX :=
  plainCl_holds _ _ _ _ hrow fun a =>
    keyF_at Z.D Z.ls A LA Tb Prod.fst Prod.snd u.oK s7 I hnl hrF hr hξ hfn hG hsK hsB a

/-- The bits. -/
theorem clH_holds (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs)
    (LA : LateAt W h K3 L.Y tabOf (placeAtt h.S) ul) (Tb : LateTabs h tabOf) (s8 : Say8 ρ W h K3)
    (hr : h.x.scH.r.size = h.S.cf.lt + h.S.cf.lgk + 4)
    (hξ : ∀ j < h.S.cf.lt + h.S.cf.lgk + 4, ptN P.sH.T u.oH j = pt ρ h.x.scH.r j)
    (hG : GoodH P.D L.Y)
    (hs : ∀ b : Fin P.D.nb, SlotAt W P.sH.T u.oH XX (h.x.scH.sEnd + 2 * b.val) (b, false) ∧
      SlotAt W P.sH.T u.oH XX (h.x.scH.sEnd + (2 * b.val + 1)) (b, true))
    (hrow : (rowF (J₂ := J₂) P.sH.T u.oH).Holds XX) : ∀ f ∈ clH L u, f.Holds XX :=
  plainCl_holds _ _ _ _ hrow fun a => bitsF_at Z.D Z.kap A LA Tb u.oH s8 hr hξ hG hs a

/-- The pairs' scalars. -/
theorem clM6_holds (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs)
    (LA : LateAt W h K3 L.Y tabOf (placeAtt h.S) ul) (Tb : LateTabs h tabOf) (s7 : Say7 ρ W h K3)
    (htg : h.x.tg.size = h.S.cf.lgk) (hp : ∀ j < h.S.cf.lgk, pt ρ h.x.tg j = (P.pubZ u.z).tg j)
    (hG : GoodM P.D L.Y)
    (hs : ∀ b : Fin P.D.nb, W.slot (h.x.sM6 + b.val) = u.s b - P.msg m (P.kF b)) :
    ∀ f ∈ clM6 L u, f.Holds XX := by
  intro f hf
  unfold clM6 at hf
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hf
  have hnb : P.D.nb = h.S.NP := by rw [Z.D]; rfl
  have e := m6F_at (m := P.msg m) (u := ul) Z.D A LA Tb (P.pubZ u.z) s7 htg hp hG
    (fun b => if hb : b < P.D.nb then u.s ⟨b, hb⟩ else 0)
    (fun b => if hb : b < P.D.nb then P.kF ⟨b, hb⟩ else P.kF i)
    (fun b hb => by
      have hb' : b < P.D.nb := by rw [hnb]; exact hb
      beta_reduce
      rw [dif_pos hb', dif_pos hb']
      exact hs ⟨b, hb'⟩) i.val (by rw [← hnb]; exact i.isLt)
  beta_reduce at e
  rw [dif_pos i.isLt, dif_pos i.isLt] at e
  exact e

/-- The line on the two sums of the value product. -/
theorem lineF_holds (s6 : Say6 ρ W h K3)
    (h0 : W.slot h.d.sCl = u.rV 0 - P.msg m (P.kV 0)) (h1 : W.slot (h.d.sCl + 1) = u.rV 1 - P.msg m (P.kV 1))
    (ha : W.slot h.d.sACC = u.rE P.iACC - P.msg m (P.kE P.iACC))
    (hz : W.slot h.d.sZC = u.rE P.iZC - P.msg m (P.kE P.iZC)) (hth : ρ.val h.d.gam = u.th) :
    (lineF (J₂ := J₂) u).Holds XX :=
  lineF_cl s6 _ _ _ _ _ _ _ _ _ h0 h1 ha hz hth

/-! ### the named scalars -/

open Inst.Model.AttSeg (Reg Fam KSc wp inn zg zgD yg xg)
open Cb.Pv.Att.End (rvF LinGood IsPlane linF linCl nameM nameD nameE nameU clM0 clD0 clE0 zT)

omit [Fintype Kf] in
theorem linCl_holds {J₁ : Type} [Fintype J₁] [DecidableEq J₁] {D : Dim} {C : Calls} {ls lmS : ℕ} {Y : LateLay AttTab J₂}
    {name : ℕ → Option KSc} {n : ℕ} {r : Fin n → Kf} {kk : Fin n → J₁} {z : ℕ → Kf} {x : J₁ ⊕ J₂ → Kf}
    (hh : ∀ (j : Fin n) k, name j.val = some k → (linF (r j) (kk j) (rvF D C ls lmS Y z k)).Holds x) :
    ∀ f ∈ linCl D C ls lmS Y name r kk z, f.Holds x := by
  intro f hf
  unfold linCl at hf
  obtain ⟨j, _, hj⟩ := List.mem_filterMap.1 hf
  cases hn : name j.val with
  | none => rw [hn] at hj; cases hj
  | some k =>
    rw [hn] at hj
    rw [← Option.some.inj hj]
    exact hh j k hn

/-- What is asked of a plane claim of family fam: public facts. -/
structure PlanePts (ρ : Reading Kf) (h : Attention.Heard) (D : Dim) (C : Calls) (z : ℕ → Kf) (fam : Fam)
    (pc : PlaneClaim) : Prop where
  plane : IsPlane fam
  pairs : PiecesAll h.S pc.pw
  reg : fam.reg = if pc.isD then Reg.D else Reg.M
  nb : (if pc.isD then h.S.nD else h.S.nM) = fam.l D
  size : pc.z.size = fam.l D
  vz : ∀ j < fam.l D - h.S.cf.lmS, pt ρ pc.z j = inn D C z fam j
  w : ∀ b < h.S.NP, ρ.val (pc.pw.getD b default).wp = wp D C z fam b

/-- A plane value of a plane claim. -/
theorem plane_holds (Z : SizesAre P L h) (LA : LateAt W h K3 L.Y tabOf (placeAtt h.S) ul)
    (hG : LinGood P.D L.ls L.lmS L.Y) (hT : tabOf .tA = h.t.tA) {z : ℕ → Kf} {fam : Fam} {pc : PlaneClaim}
    (Q : PlanePts ρ h P.D P.C z fam pc) (S : PlanesSay ρ W h K3 pc) {x : ℕ} (hx : x < pc.np) (hx5 : x < 5)
    {r : Kf} {k : P.J} (hs : W.slot (pc.s0 + x) = r - P.msg m k) :
    (linF r k (rvF P.D P.C L.ls L.lmS L.Y z (.cell fam x))).Holds XX :=
  cellF_at Z.D Z.ls Z.lmS LA P.C z hG r k fam Q.plane x hx5 hT Q.pairs Q.reg Q.nb Q.size
    Q.vz Q.w (S x hx) hs

/-- What is asked of a unit's row maxima: public facts. vg: the library's point on the heads. -/
structure MaxIs (ρ : Reading Kf) (h : Attention.Heard) (D : Dim) (C : Calls) (z : ℕ → Kf) (fam : Fam)
    (vg : ℕ → Kf) (k : Score) : Prop where
  pairs : PiecesAll h.S k.pw
  size : h.S.cf.lgk ≤ k.zg.size
  vg : ∀ j < h.S.cf.lgk, pt ρ k.zg j = vg j
  w : ∀ b < h.S.NP, ρ.val (k.pw.getD b default).wp = wp D C z fam b

/-- The seven scalars of a unit: five planes and the row maxima are named. -/
theorem unit_lin (Z : SizesAre P L h)
    (LA : LateAt W h K3 L.Y tabOf (placeAtt h.S) ul) (hG : LinGood P.D L.ls L.lmS L.Y)
    (hT : tabOf .tA = h.t.tA) {z : ℕ → Kf} {fam : Fam} {reg : Reg} {k : Score} {tb : ScoreTables}
    {pc : PlaneClaim} (U : UnitAt ρ W h K3 k tb pc) (Q : PlanePts ρ h P.D P.C z fam pc) (hnp : pc.np = 5)
    (hs0 : pc.s0 = k.s0)
    (hms : ∀ (r : Kf) (kk : P.J), W.slot (k.s0 + 5) = r - P.msg m kk →
      (linF r kk (rvF P.D P.C L.ls L.lmS L.Y z (.ms reg))).Holds XX)
    {j : ℕ} {c : KSc} (hn : nameU fam reg j = some c) {r : Kf} {kk : P.J}
    (hs : W.slot (k.s0 + j) = r - P.msg m kk) :
    (linF r kk (rvF P.D P.C L.ls L.lmS L.Y z c)).Holds XX := by
  have pl : ∀ x < 5, W.slot (k.s0 + x) = r - P.msg m kk →
      (linF r kk (rvF P.D P.C L.ls L.lmS L.Y z (.cell fam x))).Holds XX := fun x hx e =>
    plane_holds Z LA hG hT Q U.planes (by rw [hnp]; exact hx) hx (by rw [hs0]; exact e)
  match j, hn, hs with
  | 0, hn, hs => cases hn; exact pl 0 (by norm_num) hs
  | 1, hn, hs => cases hn; exact pl 1 (by norm_num) hs
  | 2, hn, hs => cases hn; exact pl 2 (by norm_num) hs
  | 3, hn, hs => cases hn; exact pl 3 (by norm_num) hs
  | 4, hn, hs => cases hn; exact pl 4 (by norm_num) hs
  | 5, hn, hs => cases hn; exact hms r kk hs
  | n + 6, hn, _ => simp [nameU] at hn

/-- The scalars in front of the first unit's sumcheck: three planes of family m1, three of d1, the unit's seven. The three premises on slots are cut at 3 and 6: they are meant for two plane messages (P.npl = 2: the library's Fits.npl), as nameM is. -/
theorem clM0_holds (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs)
    (LA : LateAt W h K3 L.Y tabOf (placeAtt h.S) ul) (hG : LinGood P.D L.ls L.lmS L.Y)
    (hT : tabOf .tA = h.t.tA) {pM pD cM : PlaneClaim} {k : Score} {tb : ScoreTables}
    (hTm : tabOf .tMm = tb.tM)
    (SM : PlanesSay ρ W h K3 pM) (SD : PlanesSay ρ W h K3 pD) (U : UnitAt ρ W h K3 k tb cM)
    (QM : PlanePts ρ h P.D P.C (zT u) .m1 pM) (QD : PlanePts ρ h P.D P.C (zT u) .d1 pD)
    (QU : PlanePts ρ h P.D P.C (zT u) .m2 cM) (nM : pM.np = 3) (nD : pD.np = 3) (nU : cM.np = 5)
    (sU : cM.s0 = k.s0) (X : MaxIs ρ h P.D P.C (zT u) .m2 (zg P.D P.C (zT u)) k)
    (hs1 : ∀ j : Fin (3 * P.npl + 7), j.val < 3 → W.slot (pM.s0 + j.val) = u.rM j - P.msg m (P.kM j))
    (hs2 : ∀ j : Fin (3 * P.npl + 7), 3 ≤ j.val → j.val < 6 →
      W.slot (pD.s0 + (j.val - 3)) = u.rM j - P.msg m (P.kM j))
    (hs3 : ∀ j : Fin (3 * P.npl + 7), 6 ≤ j.val →
      W.slot (k.s0 + (j.val - 6)) = u.rM j - P.msg m (P.kM j)) :
    ∀ f ∈ clM0 L u, f.Holds XX := by
  refine linCl_holds fun j c hn => ?_
  unfold nameM at hn
  split at hn
  · rename_i h3
    cases hn
    exact plane_holds Z LA hG hT QM SM (by rw [nM]; exact h3) (by omega) (hs1 j h3)
  · rename_i h3
    split at hn
    · rename_i h6
      cases hn
      exact plane_holds Z LA hG hT QD SD (by rw [nD]; omega) (by omega) (hs2 j (by omega) h6)
    · rename_i h6
      exact unit_lin Z LA hG hT U QU nU sU
        (fun r kk e => msMF_at Z.D Z.ls Z.lmS A LA P.C (zT u) hG r kk hTm X.pairs X.size X.vg X.w
          U.maximum e) hn (hs3 j (by omega))

/-- The scalars of the unit on the diagonal. -/
theorem clD0_holds (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs)
    (LA : LateAt W h K3 L.Y tabOf (placeAtt h.S) ul) (hG : LinGood P.D L.ls L.lmS L.Y)
    (hT : tabOf .tA = h.t.tA) {cD : PlaneClaim} {k : Score} {tb : ScoreTables} (hTd : tabOf .tMd = tb.tM)
    (U : UnitAt ρ W h K3 k tb cD) (QU : PlanePts ρ h P.D P.C (zT u) .d2 cD) (nU : cD.np = 5)
    (sU : cD.s0 = k.s0) (X : MaxIs ρ h P.D P.C (zT u) .d2 (zgD P.D P.C (zT u)) k)
    (hs : ∀ j : Fin 7, W.slot (k.s0 + j.val) = u.rD j - P.msg m (P.kD j)) :
    ∀ f ∈ clD0 L u, f.Holds XX := by
  refine linCl_holds fun j c hn => ?_
  exact unit_lin Z LA hG hT U QU nU sU
    (fun r kk e => msDF_at Z.D Z.ls Z.lmS A LA P.C (zT u) hG r kk hTd X.pairs X.size X.vg X.w
      U.maximum e) hn (hs j)

/-- The slot of further scalar number j of the denominator times the output. -/
def slotEh (h : Attention.Heard) (lT j : ℕ) : ℕ :=
  if j < 5 then h.d.s5 + j else if j < 5 + lT then h.d.sIB + (j - 5) else h.d.s5h + (j - (5 + lT))

/-- What is asked of the division's scalars: public facts. -/
structure DivIs (ρ : Reading Kf) (h : Attention.Heard) (D : Dim) (C : Calls) (z : ℕ → Kf) : Prop where
  pW : PiecesAll h.S h.d.pwW
  pX : PiecesAll h.S h.d.pwX
  pH : PiecesAll h.S h.d.pwH
  wW : ∀ b < h.S.NP, ρ.val (h.d.pwW.getD b default).wp = wp D C z .w3 b
  wX : ∀ b < h.S.NP, ρ.val (h.d.pwX.getD b default).wp = wp D C z .x3 b
  wH : ∀ b < h.S.NP, ρ.val (h.d.pwH.getD b default).wp = wp D C z .f4 b
  gW : h.S.cf.lgk ≤ h.d.zgW.size
  gX : h.S.cf.lgk ≤ h.d.zgX.size
  gH : h.S.cf.lgk ≤ h.d.zgH.size
  cW : h.d.zcW.size = h.S.cf.ldh
  cH : h.d.zcH.size = h.S.cf.ldh
  vgW : ∀ j < h.S.cf.lgk, pt ρ h.d.zgW j = yg D C z j
  vgX : ∀ j < h.S.cf.lgk, pt ρ h.d.zgX j = xg D C z j
  vgH : ∀ j < h.S.cf.lgk, pt ρ h.d.zgH j = yg D C z j
  vnW : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn D C z j
  vnH : ∀ j < h.S.cf.ldh, pt ρ h.d.zcH j = yn D C z j
  /-- the heads' features are lawful: the kind's own runs test it on the way -/
  fe : ∀ (first : Bool) (pw : Array PW), pw = h.d.pwW ∨ pw = h.d.pwH → ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk,
    headFeat (if first then Attention.atRh h.S else Attention.atRhp h.S)
      (g * h.S.HA + (pw.getD b default).a) h.S.dh = .ok ((g * h.S.HA + (pw.getD b default).a) * h.S.dh)

/-- The scalars of the division: ZC, RH, RHP, the bits of the index, RH2, RHP2 are named. -/
theorem clE0_holds (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs)
    (LA : LateAt W h K3 L.Y tabOf (placeAtt h.S) ul) (hG : LinGood P.D L.ls L.lmS L.Y)
    (hW : tabOf .hW = h.t.hW) (hX : tabOf .hX = h.t.hX) (hO : tabOf .tO = h.t.tO)
    (s5 : Say5 ρ W h K3) (Q : DivIs ρ h P.D P.C (zT u))
    (hs : ∀ j : Fin (5 + P.D.lT + 2), W.slot (slotEh h P.D.lT j.val) = u.rE j - P.msg m (P.kE j)) :
    ∀ f ∈ clE0 L u, f.Holds XX := by
  have hlT : P.D.lT = h.S.cf.lt := by rw [Z.D]; exact pub_lT A
  refine linCl_holds fun j c hn => ?_
  have e := hs j
  unfold slotEh at e
  unfold nameE at hn
  split at hn
  · cases hn
  rename_i h2
  split at hn
  · rename_i j2
    cases hn
    rw [if_pos (by omega), j2] at e
    exact zcF_at Z.D Z.ls Z.lmS A LA P.C (zT u) hG _ _ hW Q.pW Q.gW Q.vgW Q.wW s5.zc e
  rename_i j2
  split at hn
  · rename_i j3
    cases hn
    rw [if_pos (by omega), j3] at e
    exact highF_at Z.D Z.ls Z.lmS A LA P.C (zT u) hG _ _ true .w3 hO Q.pW Q.gW Q.cW Q.vgW Q.vnW Q.wW
      (Q.fe true _ (.inl rfl)) s5.rh e
  rename_i j3
  split at hn
  · rename_i j4
    cases hn
    rw [if_pos (by omega), j4] at e
    exact highF_at Z.D Z.ls Z.lmS A LA P.C (zT u) hG _ _ false .w3 hO Q.pW Q.gW Q.cW Q.vgW Q.vnW Q.wW
      (Q.fe false _ (.inl rfl)) s5.rhp e
  rename_i j4
  split at hn
  · rename_i j5
    cases hn
    rw [if_neg (by omega), if_pos j5] at e
    exact ibF_at Z.D Z.ls Z.lmS A LA P.C (zT u) hG _ _ (j.val - 5) (by omega) hX Q.pX Q.gX Q.vgX Q.wX
      (s5.ib _ (by omega)) e
  rename_i j5
  split at hn
  · rename_i j6
    cases hn
    rw [if_neg (by omega), if_neg j5, j6, Nat.sub_self, Nat.add_zero] at e
    exact highF_at Z.D Z.ls Z.lmS A LA P.C (zT u) hG _ _ true .f4 hO Q.pH Q.gH Q.cH Q.vgH Q.vnH Q.wH
      (Q.fe true _ (.inr rfl)) s5.r2 e
  rename_i j6
  split at hn
  · rename_i j7
    cases hn
    rw [if_neg (by omega), if_neg j5, j7, show 5 + P.D.lT + 1 - (5 + P.D.lT) = 1 by omega] at e
    exact highF_at Z.D Z.ls Z.lmS A LA P.C (zT u) hG _ _ false .f4 hO Q.pH Q.gH Q.cH Q.vgH Q.vnH Q.wH
      (Q.fe false _ (.inr rfl)) s5.r2p e
  · cases hn

/-! ### the whole ledger -/

open Cb.Pv.Att.End (ownCl joinF attA JoinLay)

/-- **The ledger of the own rounds' claims holds where its fourteen parts hold.** -/
theorem ownCl_of_parts {Q : JoinLay P} {x : P.J ⊕ J₂ → Kf}
    (a1 : ∀ f ∈ clM0 L u, f.Holds x) (a2 : ∀ f ∈ clM L u, f.Holds x) (a3 : ∀ f ∈ clD0 L u, f.Holds x)
    (a4 : ∀ f ∈ clD L u, f.Holds x) (a5 : ∀ f ∈ clE0 L u, f.Holds x) (a6 : ∀ f ∈ clE L u, f.Holds x)
    (a7 : (joinF (J₂ := J₂) Q u).Holds x) (a8 : (lineF (J₂ := J₂) u).Holds x)
    (a9 : ∀ f ∈ clVM L u, f.Holds x) (a10 : ∀ f ∈ clVD L u, f.Holds x) (a11 : ∀ f ∈ clM6 L u, f.Holds x)
    (a12 : ∀ f ∈ clF L u, f.Holds x) (a13 : ∀ f ∈ clK L u, f.Holds x) (a14 : ∀ f ∈ clH L u, f.Holds x) :
    ∀ f ∈ ownCl L Q u, f.Holds x := by
  intro f hf
  unfold ownCl at hf
  simp only [List.mem_append, List.mem_cons] at hf
  rcases hf with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact a1 f h
  · exact a2 f h
  · exact a3 f h
  · exact a4 f h
  · exact a5 f h
  · exact a6 f h
  · rw [h]; exact a7
  · rw [h]; exact a8
  · exact a9 f h
  · exact a10 f h
  · exact a11 f h
  · exact a12 f h
  · exact a13 f h
  · exact a14 f h

/-- The same for the pull-backs: at the late entries' meant values. -/
theorem ownCl_pull {Q : JoinLay P}
    (hh : ∀ f ∈ ownCl L Q u, f.Holds (Sum.elim (P.msg m) fun i => (attA L u i).val (P.msg m))) :
    ∀ f ∈ ownCl L Q u, (Cb.Sub.pullF (attA L u) f).Holds (P.msg m) := by
  intro f hf
  rw [Cb.Sub.pullF_holds]
  exact hh f hf

end K5Law
