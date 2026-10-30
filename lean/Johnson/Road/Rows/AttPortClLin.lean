-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttPortClLin.lean: if a claim of the verifier on a named scalar of an attention
sub-proof has the value 0, the library-side claim holds, at any values of the late entries.

Cb/Pv/Att/End/Riders.lean lists the verifier's claims on the named scalars in the library's names:
linF r k (rvF .. name), for what was sent (r), the place of its mask entry (k) and the scalar's
name. Johnson/Road/Rows/AttPortLin.lean holds the forms against each other. This file draws the
conclusion for the claims, name by name.

Main theorems. x is Sum.elim m u.
 - lin_holds: from a form that is worth the slot's hidden value less a library-side form.
 - zc_cl, ib_cl, msM_cl, msD_cl, cell_cl: one for each kind of name that one claim ties to a table.
   high_cl: the four names rh, rh', rg, rg' in one statement; its library-side forms are rvF's cases
   at these names, by rvF's definition.

What the theorems take as given: that the form has been made and has the value 0; the dictionary
LateAt; the premise LinGood on names; that the hidden value under the scalar's slot is what was sent
less the mask entry; that the list of pieces has a piece for each pair, with the library's weights;
that the verifier's points are the library's.

What is not claimed: as in Johnson/Road/Rows/AttPortCl.lean. The join of the key forms is not
treated.


-/
import Johnson.Road.Rows.AttPortLin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff Fork)
open OnBytes.Attention (Heard PW lessPieces)
open OnBytes.Road.Hd (Ok)
open Inst.Model.AttSeg (Raw Reg Calls Fam KSc wp inn zg zgD yg yn xg)
open Cb.Pv.Att.End (LateLay AttTab linF rvF LinGood IsPlane val_aSub val_aConst val_aEnt)

variable {K : Type} [Field K]

variable {ρ : Reading K} {W : World K} {K3 : ℕ} {h : Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {u : J₂ → K} {m : J₁ → K}
  {F : Fork} {C : Ctx} {q : Aff} {G : Fork} {D : Ctx}

/-- From a form that is worth the slot's hidden value less a library-side form. -/
theorem lin_holds {s : ℕ} {r : K} {k : J₁} {R : TWhole.Aff K (J₁ ⊕ J₂)}
    (hq : q.value ρ W = W.slot s - R.val (Sum.elim m u)) (v : q.value ρ W = 0)
    (hs : W.slot s = r - m k) : (linF r k R).Holds (Sum.elim m u) := by
  rw [v, hs] at hq
  unfold Cb.Pv.Att.End.linF Cb.Pv.Att.End.hidF
  rw [TWhole.Aff.claim_holds, val_aSub, val_aSub, val_aConst, val_aEnt]
  exact hq.symm

variable (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
  (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Cc : Calls) (z : ℕ → K)
  (hG : LinGood (L5.dimOf h.S) h.S.ls h.S.cf.lmS Y) (r : K) (k : J₁)
include A hc L hG

/-- ZC. -/
theorem zc_cl (hT : tabOf .hW = h.t.hW) (P : PiecesAll h.S h.d.pwW)
    (hz : h.S.cf.lgk ≤ h.d.zgW.size)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgW j = yg (L5.dimOf h.S) Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwW.getD b default).wp = wp (L5.dimOf h.S) Cc z .w3 b)
    (hq : Ok (lessPieces (Aff.slot h.d.sZC) h.d.pwW fun w =>
      Attention.readDenominator h h.t.hW h.d.zgW w.lam w.a) F C q G D)
    (v : q.value ρ W = 0) (hs : W.slot h.d.sZC = r - m k) :
    (linF r k (rvF (L5.dimOf h.S) Cc h.S.ls h.S.cf.lmS Y z .zc)).Holds (Sum.elim m u) :=
  lin_holds (zc_port m A hc L hT P Cc z hz hvg hw (fun b hb g hg l hl => hG.hW b hb g hg l hl) hq)
    v hs

/-- IB_i. -/
theorem ib_cl (i : ℕ) (hi : i < (L5.dimOf h.S).lT) (hT : tabOf .hX = h.t.hX)
    (P : PiecesAll h.S h.d.pwX) (hz : h.S.cf.lgk ≤ h.d.zgX.size)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgX j = xg (L5.dimOf h.S) Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwX.getD b default).wp = wp (L5.dimOf h.S) Cc z .x3 b)
    (hq : Ok (lessPieces (Aff.slot (h.d.sIB + i)) h.d.pwX fun w =>
      Attention.readIndexBit h h.t.hX h.d.zgX w.lam w.a i) F C q G D)
    (v : q.value ρ W = 0) (hs : W.slot (h.d.sIB + i) = r - m k) :
    (linF r k (rvF (L5.dimOf h.S) Cc h.S.ls h.S.cf.lmS Y z (.ib i))).Holds (Sum.elim m u) :=
  lin_holds (ib_port m A hc L hT P Cc z i hz hvg hw (fun b hb g hg => hG.hX i hi b hb g hg) hq)
    v hs

/-- The row maxima of the unit below the diagonal. t: where the unit's table on the maxima begins;
s: the scalar's slot. -/
theorem msM_cl {t s : ℕ} (hT : tabOf .tMm = t) {pw : Array PW} (P : PiecesAll h.S pw)
    {zz : Array E} (hz : h.S.cf.lgk ≤ zz.size)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ zz j = zg (L5.dimOf h.S) Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z .m2 b)
    (hq : Ok (lessPieces (Aff.slot s) pw fun w => Attention.readMaximum h t zz w.lam w.a)
      F C q G D)
    (v : q.value ρ W = 0) (hs : W.slot s = r - m k) :
    (linF r k (rvF (L5.dimOf h.S) Cc h.S.ls h.S.cf.lmS Y z (.ms .M))).Holds (Sum.elim m u) :=
  lin_holds (ms_port m A hc L .tMm hT rfl s P Cc z .m2 hz hvg hw
    (fun b hb g hg l hl => hG.tMm b hb g hg l hl) hq) v hs

/-- The row maxima of the unit on the diagonal. -/
theorem msD_cl {t s : ℕ} (hT : tabOf .tMd = t) {pw : Array PW} (P : PiecesAll h.S pw)
    {zz : Array E} (hz : h.S.cf.lgk ≤ zz.size)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ zz j = zgD (L5.dimOf h.S) Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z .d2 b)
    (hq : Ok (lessPieces (Aff.slot s) pw fun w => Attention.readMaximum h t zz w.lam w.a)
      F C q G D)
    (v : q.value ρ W = 0) (hs : W.slot s = r - m k) :
    (linF r k (rvF (L5.dimOf h.S) Cc h.S.ls h.S.cf.lmS Y z (.ms .D))).Holds (Sum.elim m u) :=
  lin_holds (ms_port m A hc L .tMd hT rfl s P Cc z .d2 hz hvg hw
    (fun b hb g hg l hl => hG.tMd b hb g hg l hl) hq) v hs

/-- The four scalars on the remainders' high parts, in one statement. first: the first remainder's,
else the second's. fam: w3 for RH and RHP, f4 for RH2 and RHP2. -/
theorem high_cl (first : Bool) (fam : Fam) {s : ℕ} (hT : tabOf .tO = h.t.tO) {pw : Array PW}
    (P : PiecesAll h.S pw) {zz zc : Array E} (hzg : h.S.cf.lgk ≤ zz.size)
    (hzc : zc.size = h.S.cf.ldh)
    (hvg : ∀ j < h.S.cf.lgk, pt ρ zz j = yg (L5.dimOf h.S) Cc z j)
    (hvn : ∀ j < h.S.cf.ldh, pt ρ zc j = yn (L5.dimOf h.S) Cc z j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z fam b)
    (hq : Ok (lessPieces (Aff.slot s) pw fun w => Attention.readHead h h.t.tO
      (if first then Attention.atRh h.S else Attention.atRhp h.S) zz zc w.lam w.a) F C q G D)
    (v : q.value ρ W = 0) (hs : W.slot s = r - m k) :
    (linF r k (Cb.Pv.Att.End.overPairs (L5.dimOf h.S) Cc z fam fun b =>
      Cb.Pv.Att.End.rdLong (L5.dimOf h.S) h.S.ls Y .tO (yg (L5.dimOf h.S) Cc z)
        (yn (L5.dimOf h.S) Cc z) 1
        fun _ g => if first then Raw.qh b g 0 0 else Raw.qh' b g 0 0)).Holds (Sum.elim m u) := by
  cases first with
  | true =>
    exact lin_holds (high_port m A hc L hT (X := Attention.atRh h.S) rfl
      (fun b g n => .qh b g 0 n) (fun _ _ _ => rfl) (fun _ _ _ => rfl) s P Cc z fam hzg hzc hvg
      hvn hw (fun b hb g hg ch hch => (hG.tO b hb g hg ch hch).1) hq) v hs
  | false =>
    exact lin_holds (high_port m A hc L hT (X := Attention.atRhp h.S) rfl
      (fun b g n => .qh' b g 0 n) (fun _ _ _ => rfl) (fun _ _ _ => rfl) s P Cc z fam hzg hzc hvg
      hvn hw (fun b hb g hg ch hch => (hG.tO b hb g hg ch hch).2) hq) v hs

omit A in
/-- A plane of a plane claim. fam: the family of planes; x: the plane's number; s: the scalar's
slot. -/
theorem cell_cl (fam : Fam) (hf : IsPlane fam) (x : ℕ) (hx : x < 5) {s : ℕ}
    (hT : tabOf .tA = h.t.tA) {pw : Array PW} (P : PiecesAll h.S pw) {zz : Array E} {isD : Bool}
    (hreg : fam.reg = if isD then Reg.D else Reg.M)
    (hnb : (if isD then h.S.nD else h.S.nM) = fam.l (L5.dimOf h.S))
    (hz : zz.size = fam.l (L5.dimOf h.S))
    (hvz : ∀ j < fam.l (L5.dimOf h.S) - h.S.cf.lmS,
      pt ρ zz j = inn (L5.dimOf h.S) Cc z fam j)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) Cc z fam b)
    (hq : Ok (lessPieces (Aff.slot s) pw fun w =>
      Attention.plane h h.t.tA x w.lam w.a zz isD) F C q G D)
    (v : q.value ρ W = 0) (hs : W.slot s = r - m k) :
    (linF r k (rvF (L5.dimOf h.S) Cc h.S.ls h.S.cf.lmS Y z (.cell fam x))).Holds
      (Sum.elim m u) :=
  lin_holds (cell_port m hc L hT s x P Cc z fam fam.reg hreg hnb hz hvz hw
    (fun b hb hi hh => hG.tA fam x b hf hx hb hi hh) hq) v hs

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.zc_cl
#print axioms OnBytes.Road.Rows.ib_cl
#print axioms OnBytes.Road.Rows.msM_cl
#print axioms OnBytes.Road.Rows.msD_cl
#print axioms OnBytes.Road.Rows.high_cl
#print axioms OnBytes.Road.Rows.cell_cl
