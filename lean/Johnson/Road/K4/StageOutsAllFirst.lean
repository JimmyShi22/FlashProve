-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StageOutsAllFirst.lean: THE FIRST GROUP's twin of Johnson/Road/K4/StageOutsAll.lean
(its part at the typed chain): all seven typed outputs from LedG, TgRecF and one record of public
ties.

The statements and proofs are that file's, turned to the first group's letters by a program
(FullFPar for FullPar; the chain P.ownF.toOwn.tail; the records LedG and TgRecF, which stand in
every group, with the tail's tape t0.drop (k0 g)) and compiled; each name bears an F.

Main names: `OutTiesF` · `pv_drawnF` · `outs_of_ledF`.

Limits. As that file's. Nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.StageOutsAll
import Johnson.Road.K4.StageOutSixFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Reading Fork Forest.Heard Level Tsc Psc orderDefault orderRange)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard downFrom normsStart)
open OnBytes.Tie.Pv.Lay (OutIs eDefault eRange)
open OnBytes.Desc.First.P1 (gl NzT TailM TailR Tg7 aD1 aD2 aD3 aD4 aD5 aD6 aS7 stgT drawnOf
  levelRec tscIn_heard)
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd lF lFe zpos)
open OnBytes.Desc.First.K4 (k0)

variable [scl : Scl] {M Xs : Type}

/-- The public ties that the seven `OutIs` want. -/
structure OutTiesF (P : FullFPar Cb.Gl.E M Xs) (Pp : Pub) (hp : HPlan2) (o : Own) : Prop where
  eS : P.eS = eDefault _
  n5 : 9 ≤ P.D.lL + lF P.D + P.D.lT
  e5 : P.e5 = eRange _ n5
  n6 : 9 ≤ P.D.lL - 1 + (lFe P.D + P.D.lT)
  e6 : P.e6 = eRange _ n6
  m1 : P.D.lL + 1 + (lDd P.D + P.D.lT) = Pp.rd.muV
  lt : P.D.lT = Pp.y.h.lt
  k4 : kS P.D = hp.lamS
  m5 : P.D.lL + lF P.D + P.D.lT = Pp.rd.muH
  m6 : P.D.lL - 1 + (lFe P.D + P.D.lT) = Pp.rd.muH2
  k7 : P.ownF.toOwn.tail.s7.L.S.k = Pp.wsLay.lk
  lI : P.D.lL + 1 = Pp.rd.lNI
  lP : lDd P.D = Pp.y.lPd
  lfe : Pp.y.lfe = lFe P.D
  ll : Pp.y.h.ll - 1 = P.D.lL - 1
  wD : o.K.fin.wD = P.D.lL + lF P.D
  le5 : P.D.lL + lF P.D ≤ kS P.D
  le6 : lFe P.D ≤ kS P.D
  rs : kS P.D ≤ o.K.rs.size
  half : gl.val (invE (OnBytes.Model.ofNat 2)) = 2⁻¹

variable (P : FullFPar Cb.Gl.E M Xs) {R : TailR} (W : TailM P.ownF.toOwn.tail R) {Pp : Pub}
  {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork} {t0 u : Tape} {H1 : Heard}
  {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}

omit scl in
/-- The norms' token point that K4 holds is what the tape's first round drew. -/
theorem pv_drawnF (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (j : ℕ) : H1.PV.getD j zeroE = (drawnOf t0).getD j zeroE := by
  obtain ⟨u1, m1, _⟩ := Ld.nt
  obtain ⟨_, _, _, _, _, _, _, _, _, _, d0, _, e0, _, hPV, _⟩ := hearNorms_tape m1
  have hd : drawnOf t0 = d0 := by
    rw [e0]
    rfl
  rw [hPV, hd]
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- **The seven typed outputs are K4's own records, read.** -/
theorem outs_of_ledF (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (S : OutTiesF P Pp hp o) (nz : NzT P.ownF.toOwn.tail (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7)
    (I : TgRecF g7 Pp hp g o t0 H1 tT F4 G2 G3 G3')
    (hx : ∀ j : Fin P.D.lT, P.ofp.fs.pvF x j = gl.val ((drawnOf t0).getD j.val zeroE))
    (hz0 : P.zOf (P.ofp.fs.x0F x) = zAt fo)
    (hzp : ∀ j, j < P.D.lT → zpos P.D (zAt fo) j = gl.val (H1.ztF.getD j zeroE)) :
    OutIs gl (aD1 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) (levelRec Pp.rd.muV
        (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).2
        (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).1
        (orderDefault Pp.rd.muV) F4 ((ksOf Pp hp).tc1 (t0.drop (k0 g)))) ∧
      OutIs gl (aD2 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) H1.tV.p ∧
      OutIs gl (aD3 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) tT.p ∧
      OutIs gl (aD4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
        (stackRec o.v o.H hp.lamS G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g)))) ∧
      OutIs gl (aD5 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
        (levelRec Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF)
          (OnBytes.Model.Aff.slot o.K.sH1) (orderRange Pp.rd.muH) G3
          ((ksOf Pp hp).tc5 (t0.drop (k0 g)))) ∧
      OutIs gl (aD6 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) (levelRec Pp.rd.muH2
        ((drawnOf ((((ksOf Pp hp).tc5 (t0.drop (k0 g))).drop (Pp.rd.muH + 3)).drop 1)).toArray ++
          downFrom o.K.rs Pp.y.lfe ++ tT.r)
        (Road.Rows.start2 Pp.y.LamM o.K.sH1
          (drawnOf ((((ksOf Pp hp).tc5 (t0.drop (k0 g))).drop (Pp.rd.muH + 3)).drop 1)).toArray)
        (orderRange Pp.rd.muH2) G3' ((ksOf Pp hp).tc6 (t0.drop (k0 g)))) ∧
      OutIs gl (stgT W.w7.num (ksOf Pp hp).k7 (((ksOf Pp hp).tcW (t0.drop (k0 g))).drop 1) nz.b7
        (aS7 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) g7.t7) o.wo.p := by
  have O3 := out3F P W Ld S.lt nz x g7 I.t3 hz0 (tscIn_heard Ld.c3).1 hzp
  have O4 := out4F P W Ld S.k4 nz x g7 I.t4
  exact ⟨out1F P W Ld S.eS S.m1 S.lI S.lP S.half nz x g7 rfl I.t1
      (fun j => by rw [pv_drawnF Ld]; exact hx j),
    out2F P W Ld S.lt nz x g7 I.t2 hx, O3, O4,
    out5F P W Ld S.n5 S.e5 S.m5 S.k4 S.wD S.le5 S.rs nz x g7 O4 rfl I.t5 hz0
      (fun j hj => by rw [Ld.ztF]; exact hzp j hj),
    out6F P W Ld S.n6 S.e6 S.m6 S.k4 S.lt S.lfe S.le6 S.rs S.ll nz x g7 O3 O4 rfl I.t6,
    out7F P W Ld S.k7 nz x g7 I.t7⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pv_drawnF
#print axioms OnBytes.Road.K4.outs_of_ledF
