-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StageOutsFirst.lean: THE FIRST GROUP's twin of Johnson/Road/K4/StageOuts.lean (its
part at the typed chain): the first, fifth and seventh typed outputs are K4's records.

The statements and proofs are that file's, turned to the first group's letters by a program
(FullFPar for FullPar; the chain P.ownF.toOwn.tail; the records LedG and TgRecF, which stand in
every group, with the tail's tape t0.drop (k0 g)) and compiled; each name bears an F.

Main names: `fitsAt1F` · `out1F` · `fitsAt5F` · `out5F` · `out7F`.

Limits. As that file's. Nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.StageOuts
import Johnson.Road.K4.StageFitsRestFirst
import Johnson.Road.K4.AtFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Reading Fork Forest.Heard Level Tsc Psc orderDefault orderRange)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard downFrom normsStart)
open OnBytes.Tie.Pv.Lay (StgFits OutIs eDefault eRange)
open OnBytes.Desc.First.P1 (gl NzT TailM TailR Tg7 aD1 aS1 aD4 aD5 aS5 aS7 stgT drawnOf
  levelRec levelWs plainWs)
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd lF lFe zpos)
open OnBytes.Desc.First.K4 (k0)

variable [scl : Scl] {M Xs : Type} (P : FullFPar Cb.Gl.E M Xs) {R : TailR}
  (W : TailM P.ownF.toOwn.tail R) {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}

/-- The weights of the product layer of the sums of squares, at a hearing. -/
theorem fitsAt1F (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (hS : P.eS = eDefault _) (hmu : P.D.lL + 1 + (lDd P.D + P.D.lT) = Pp.rd.muV)
    (hlI : P.D.lL + 1 = Pp.rd.lNI) (hlP : lDd P.D = Pp.y.lPd)
    (hhalf : gl.val (invE (OnBytes.Model.ofNat 2)) = 2⁻¹)
    (x : P.ofp.fs.X3)
    (hx : ∀ j : Fin P.D.lT, P.ofp.fs.pvF x j = gl.val (H1.PV.getD j.val zeroE)) :
    StgFits gl P.ownF.toOwn.tail.s1 (aS1 P.ownF.toOwn.tail (ksOf Pp hp) (t0.drop (k0 g)) x)
      (levelWs Pp.rd.muV
        (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).2
        (orderDefault Pp.rd.muV)) Pp.rd.muV 2 := by
  have f0 := fits1F P hS (aS1 P.ownF.toOwn.tail (ksOf Pp hp) (t0.drop (k0 g)) x)
    (Johnson.L5.Layers.rd gl (P.D.lL + 1) (drawnOf ((t0.drop (k0 g)).drop 1))) (P.ofp.fs.pvF x) (fun
        _ => rfl)
    (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV (invE (OnBytes.Model.ofNat 2))
    (by rw [List.size_toArray, Ld.lI, hlI])
    (fun i => by
      show gl.val ((drawnOf ((t0.drop (k0 g)).drop 1)).getD i.val zeroE) = _
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD])
    hx hhalf
  rw [hmu, hlP] at f0
  exact f0

/-- **The product layer of the sums of squares.** -/
theorem out1F (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (hS : P.eS = eDefault _) (hmu : P.D.lL + 1 + (lDd P.D + P.D.lT) = Pp.rd.muV)
    (hlI : P.D.lL + 1 = Pp.rd.lNI) (hlP : lDd P.D = Pp.y.lPd)
    (hhalf : gl.val (invE (OnBytes.Model.ofNat 2)) = 2⁻¹)
    (nz : NzT P.ownF.toOwn.tail (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7) {p1 : Psc}
    (hp1 : p1 = levelRec Pp.rd.muV
      (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).2
      (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).1
      (orderDefault Pp.rd.muV) F4 ((ksOf Pp hp).tc1 (t0.drop (k0 g))))
    (ht1 : g7.t1 = p1.target)
    (hx : ∀ j : Fin P.D.lT, P.ofp.fs.pvF x j = gl.val (H1.PV.getD j.val zeroE)) :
    OutIs gl (aD1 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) p1 := by
  obtain ⟨v1, c1⟩ := Ld.c1
  subst hp1
  exact stgT_out W.w1.num (ksOf Pp hp).k1 _ nz.b1 _ g7.t1 rfl (level_recAt c1) ht1
    (fitsAt1F P Ld hS hmu hlI hlP hhalf x hx)

/-- The weights of the product layer of the gated products, at a hearing. -/
theorem fitsAt5F (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (h9 : 9 ≤ P.D.lL + lF P.D + P.D.lT) (h5 : P.e5 = eRange _ h9)
    (hmu : P.D.lL + lF P.D + P.D.lT = Pp.rd.muH) (hk : kS P.D = hp.lamS)
    (hwD : o.K.fin.wD = P.D.lL + lF P.D) (hle : P.D.lL + lF P.D ≤ kS P.D)
    (hrs : kS P.D ≤ o.K.rs.size)
    (nz : NzT P.ownF.toOwn.tail (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7) {p4 : Psc}
    (O4 : OutIs gl (aD4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) p4) (hz0 : P.zOf (P.ofp.fs.x0F x) =
        zAt fo)
    (hzp : ∀ j, j < P.D.lT → zpos P.D (zAt fo) j = gl.val (o.H.ztF.getD j zeroE)) :
    StgFits gl P.ownF.toOwn.tail.s5 (aS5 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (levelWs Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (orderRange Pp.rd.muH))
      Pp.rd.muH 2 := by
  have hζ : ∀ j, j < kS P.D → P.toOwnPar.zeta (aD4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7).out j =
      gl.val (o.K.rs.getD (kS P.D - 1 - j) zeroE) := fun _ hj =>
    stgT_stack_point W.w4.num (ksOf Pp hp).k4 ((ksOf Pp hp).tc4 (t0.drop (k0 g))) nz.b4 _ g7.t4 O4
        hk
      Ld.c4 hj
  have f0 := fits5F P h9 h5 (aS5 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
    (downFrom o.K.rs (P.D.lL + lF P.D)) o.H.ztF
    (by
      unfold downFrom
      rw [rev_size o.K.rs (le_trans hle hrs), Nat.sub_zero])
    (fun i => down_reads _ o.K.rs (kS P.D) (P.D.lL + lF P.D) hle hrs hζ i)
    (fun i => by
      show zpos P.D (P.zOf (P.ofp.fs.x0F x)) i.val = _
      rw [hz0, hzp i.val i.isLt])
  rw [hmu, ← hwD] at f0
  exact f0

/-- **The product layer of the gated products.** -/
theorem out5F (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (h9 : 9 ≤ P.D.lL + lF P.D + P.D.lT) (h5 : P.e5 = eRange _ h9)
    (hmu : P.D.lL + lF P.D + P.D.lT = Pp.rd.muH) (hk : kS P.D = hp.lamS)
    (hwD : o.K.fin.wD = P.D.lL + lF P.D) (hle : P.D.lL + lF P.D ≤ kS P.D)
    (hrs : kS P.D ≤ o.K.rs.size)
    (nz : NzT P.ownF.toOwn.tail (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7) {p4 p5 : Psc}
    (O4 : OutIs gl (aD4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) p4)
    (hp5 : p5 = levelRec Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF)
      (OnBytes.Model.Aff.slot o.K.sH1) (orderRange Pp.rd.muH) G3 ((ksOf Pp hp).tc5 (t0.drop (k0
          g))))
    (ht5 : g7.t5 = p5.target) (hz0 : P.zOf (P.ofp.fs.x0F x) = zAt fo)
    (hzp : ∀ j, j < P.D.lT → zpos P.D (zAt fo) j = gl.val (o.H.ztF.getD j zeroE)) :
    OutIs gl (aD5 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) p5 := by
  obtain ⟨v5, c5⟩ := Ld.c5
  subst hp5
  exact stgT_out W.w5.num (ksOf Pp hp).k5 _ nz.b5 _ g7.t5 rfl (level_recAt c5) ht5
    (fitsAt5F P W Ld h9 h5 hmu hk hwD hle hrs nz x g7 O4 hz0 hzp)

/-- **The merge.** -/
theorem out7F (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (hk : P.ownF.toOwn.tail.s7.L.S.k = Pp.wsLay.lk)
    (nz : NzT P.ownF.toOwn.tail (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7) (ht7 : g7.t7 = o.wo.p.target) :
    OutIs gl (stgT W.w7.num (ksOf Pp hp).k7 (((ksOf Pp hp).tcW (t0.drop (k0 g))).drop 1) nz.b7
      (aS7 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) g7.t7) o.wo.p := by
  obtain ⟨cl, c7⟩ := Ld.c7
  have r := (merge_recAt c7).1
  rw [Ld.u5d] at r
  exact stgT_out W.w7.num (ksOf Pp hp).k7 _ nz.b7 _ g7.t7 rfl r ht7
    (fits7F P _ Pp.wsLay.lk hk)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.fitsAt1F
#print axioms OnBytes.Road.K4.out1F
#print axioms OnBytes.Road.K4.fitsAt5F
#print axioms OnBytes.Road.K4.out5F
#print axioms OnBytes.Road.K4.out7F
