-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PortClLin.lean: kind K5: what the claims on the named scalars say (the
written forms lessF … worth 0: Johnson/Desc/First/Att/Claims/Say.lean,
Johnson/Desc/First/Att/Claims/Say58.lean) gives the library-side claims linF r k (rvF …)
(Cb/Pv/Att/End/Lin.lean), at any values of the late entries. Twins of zc_cl, ib_cl, msM_cl, msD_cl,
high_cl and cell_cl (Johnson/Road/Rows/AttPortClLin.lean), which take a run of a routine in a
context. lin_holds of that file speaks of no run and is used as it stands.

Main names: `zcF_cl`, `ibF_cl`, `msMF_cl`, `msDF_cl`, `highF_cl`, `cellF_cl`.
Taken as given, as in that file: AttPub; LateAt; LinGood; PiecesAll with the library's weights; that
the verifier's points are the library's, coordinate by coordinate; "W.slot s = r − m k". And the
lawful heads (highF_cl).
Used: as Johnson/Desc/First/Att/Claims/PortLin.lean, and lin_holds; the library's linF, rvF,
LinGood, IsPlane, KSc, inn, zg, zgD, yg, yn, xg.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttPortClLin
import Johnson.Desc.First.Att.Claims.PortLin

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Raw Reg Calls Fam KSc wp inn zg zgD yg yn xg)
open Cb.Pv.Att.End (LateLay AttTab linF rvF LinGood IsPlane val_aSub val_aConst val_aEnt)

variable {Kf : Type} [Field Kf]

variable {ρ : Reading Kf} {W : World Kf} {K3 : ℕ} {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {u : J₂ → Kf} {m : J₁ → Kf}

variable (A : AttPub ρ h lid cf fs)
  (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Cc : Calls) (z : ℕ → Kf)
  (hG : LinGood (L5.dimOf h.S) h.S.ls h.S.cf.lmS Y) (r : Kf) (k : J₁)
include A L hG

/-- ZC. -/
theorem zcF_cl (hT : tabOf .hW = h.t.hW) (P : PiecesAll h.S h.d.pwW)
    (hz : h.S.cf.lgk ≤ h.d.zgW.size)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgW j = yg (L5.dimOf h.S) Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwW.getD b default).wp = wp (L5.dimOf h.S) Cc z .w3 b)
    (v : (Fo.lessF (Aff.slot h.d.sZC) h.d.pwW fun w =>
      Fo.readDenominatorF h K3 h.t.hW h.d.zgW w.lam w.a).value ρ W = 0)
    (hs : W.slot h.d.sZC = r - m k) :
    (linF r k (rvF (L5.dimOf h.S) Cc h.S.ls h.S.cf.lmS Y z .zc)).Holds (Sum.elim m u) :=
  lin_holds (zcF_port m A L hT P Cc z hz hvg hw (fun b hb g hg l hl => hG.hW b hb g hg l hl)) v hs

/-- IB_i. -/
theorem ibF_cl (i : ℕ) (hi : i < (L5.dimOf h.S).lT) (hT : tabOf .hX = h.t.hX)
    (P : PiecesAll h.S h.d.pwX) (hz : h.S.cf.lgk ≤ h.d.zgX.size)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgX j = xg (L5.dimOf h.S) Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwX.getD b default).wp = wp (L5.dimOf h.S) Cc z .x3 b)
    (v : (Fo.lessF (Aff.slot (h.d.sIB + i)) h.d.pwX fun w =>
      Fo.readIndexBitF h K3 h.t.hX h.d.zgX w.lam w.a i).value ρ W = 0)
    (hs : W.slot (h.d.sIB + i) = r - m k) :
    (linF r k (rvF (L5.dimOf h.S) Cc h.S.ls h.S.cf.lmS Y z (.ib i))).Holds (Sum.elim m u) :=
  lin_holds (ibF_port m A L hT P Cc z i hz hvg hw (fun b hb g hg => hG.hX i hi b hb g hg)) v hs

/-- The row maxima of the unit below the diagonal. t: where the unit's table on the maxima begins; s: the scalar's slot. -/
theorem msMF_cl {t s : ℕ} (hT : tabOf .tMm = t) {pw : Array PW} (P : PiecesAll h.S pw)
    {zz : Array E} (hz : h.S.cf.lgk ≤ zz.size)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ zz j = zg (L5.dimOf h.S) Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z .m2 b)
    (v : (Fo.lessF (Aff.slot s) pw fun w => Fo.readMaximumF h K3 t zz w.lam w.a).value ρ W = 0)
    (hs : W.slot s = r - m k) :
    (linF r k (rvF (L5.dimOf h.S) Cc h.S.ls h.S.cf.lmS Y z (.ms .M))).Holds (Sum.elim m u) :=
  lin_holds (msF_port m A L .tMm hT rfl s P Cc z .m2 hz hvg hw
    (fun b hb g hg l hl => hG.tMm b hb g hg l hl)) v hs

/-- The row maxima of the unit on the diagonal. -/
theorem msDF_cl {t s : ℕ} (hT : tabOf .tMd = t) {pw : Array PW} (P : PiecesAll h.S pw)
    {zz : Array E} (hz : h.S.cf.lgk ≤ zz.size)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ zz j = zgD (L5.dimOf h.S) Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z .d2 b)
    (v : (Fo.lessF (Aff.slot s) pw fun w => Fo.readMaximumF h K3 t zz w.lam w.a).value ρ W = 0)
    (hs : W.slot s = r - m k) :
    (linF r k (rvF (L5.dimOf h.S) Cc h.S.ls h.S.cf.lmS Y z (.ms .D))).Holds (Sum.elim m u) :=
  lin_holds (msF_port m A L .tMd hT rfl s P Cc z .d2 hz hvg hw
    (fun b hb g hg l hl => hG.tMd b hb g hg l hl)) v hs

/-- The four scalars on the remainders' high parts, in one statement. first: the first remainder's, else the second's. fam: w3 for RH and RHP, f4 for RH2 and RHP2. -/
theorem highF_cl (first : Bool) (fam : Fam) {s : ℕ} (hT : tabOf .tO = h.t.tO) {pw : Array PW}
    (P : PiecesAll h.S pw) {zz zc : Array E} (hzg : h.S.cf.lgk ≤ zz.size)
    (hzc : zc.size = h.S.cf.ldh)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ zz j = yg (L5.dimOf h.S) Cc z j)
    (hvn : ∀ j < h.S.cf.ldh, pt ρ zc j = yn (L5.dimOf h.S) Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z fam b)
    (hfe : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk,
      headFeat (if first then Attention.atRh h.S else Attention.atRhp h.S)
        (g * h.S.HA + (pw.getD b default).a) h.S.dh = .ok ((g * h.S.HA + (pw.getD b default).a) * h.S.dh))
    (v : (Fo.lessF (Aff.slot s) pw fun w => Fo.readHeadT h K3 h.t.tO
      (if first then Attention.atRh h.S else Attention.atRhp h.S) zz zc w.lam w.a).value ρ W = 0)
    (hs : W.slot s = r - m k) :
    (linF r k (Cb.Pv.Att.End.overPairs (L5.dimOf h.S) Cc z fam fun b =>
      Cb.Pv.Att.End.rdLong (L5.dimOf h.S) h.S.ls Y .tO (yg (L5.dimOf h.S) Cc z)
        (yn (L5.dimOf h.S) Cc z) 1
        fun _ g => if first then Raw.qh b g 0 0 else Raw.qh' b g 0 0)).Holds (Sum.elim m u) := by
  cases first with
  | true =>
    exact lin_holds (highF_port m A L hT (X := Attention.atRh h.S) rfl
      (fun b g n => .qh b g 0 n) (fun _ _ _ => rfl) (fun _ _ _ => rfl) s P Cc z fam hzg hzc hvg
      hvn hw (fun b hb g hg ch hch => (hG.tO b hb g hg ch hch).1) hfe) v hs
  | false =>
    exact lin_holds (highF_port m A L hT (X := Attention.atRhp h.S) rfl
      (fun b g n => .qh' b g 0 n) (fun _ _ _ => rfl) (fun _ _ _ => rfl) s P Cc z fam hzg hzc hvg
      hvn hw (fun b hb g hg ch hch => (hG.tO b hb g hg ch hch).2) hfe) v hs

omit A in
/-- A plane of a plane claim. fam: the family of planes; x: the plane's number; s: the scalar's slot. -/
theorem cellF_cl (fam : Fam) (hf : IsPlane fam) (x : ℕ) (hx : x < 5) {s : ℕ}
    (hT : tabOf .tA = h.t.tA) {pw : Array PW} (P : PiecesAll h.S pw) {zz : Array E} {isD : Bool}
    (hreg : fam.reg = if isD then Reg.D else Reg.M)
    (hnb : (if isD then h.S.nD else h.S.nM) = fam.l (L5.dimOf h.S))
    (hz : zz.size = fam.l (L5.dimOf h.S))
    (hvz : ∀ j < fam.l (L5.dimOf h.S) - h.S.cf.lmS,
      pt ρ zz j = inn (L5.dimOf h.S) Cc z fam j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z fam b)
    (v : (Fo.lessF (Aff.slot s) pw fun w => Fo.planeF h K3 h.t.tA x w.lam w.a zz isD).value ρ W = 0)
    (hs : W.slot s = r - m k) :
    (linF r k (rvF (L5.dimOf h.S) Cc h.S.ls h.S.cf.lmS Y z (.cell fam x))).Holds
      (Sum.elim m u) :=
  lin_holds (cellF_port m L hT s x P Cc z fam fam.reg hreg hnb hz hvz hw
    (fun b hb hi hh => hG.tA fam x b hf hx hb hi hh)) v hs

end K5Law
