-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/StageOutsAll.lean: THE SEVEN `OutIs` AT A HEARING (StageFits.lean,
StageFitsMore.lean, StageOuts.lean, StageOutSix.lean) GATHERED: FROM `Led7`, `TgRec` AND ONE RECORD
OF PUBLIC TIES. A record, one lemma and one theorem. Bookkeeping.

  `OutTies P Pp hp o`: the value's three orders are the programs' · the typed numbers of rounds are
    muV, lt, lamS, muH, muH2, lk · lL + 1 = lNI, lDd = lPd, lFe = lfe, lL - 1 = ll - 1 · the width
    of the first gated panel that K4's record holds is lL + lF · both widths are at most the
    batched sumcheck's number of rounds, and K4 holds at least so many challenges · the reading of
    the programs' 1/2 is 1/2.
  `pv_drawn`: the norms' token point that K4 holds is what the tape's first round drew.
  `outs_of_led`: `OutIs` at all seven stages, at the data `aD1` … `aD6` and the merge's, against
    K4's seven records.

Limits. PREMISES: `Led7` · `TgRec` · `OutTies` · hx (the token point in the first statement reads
what the tape's first round drew) · hz0, hzp (zOf at the first statement is the lookup's point,
whose tail reads ztF). A group that is not the first.
-/
import Johnson.Road.K4.StageOutSix
import Johnson.Road.K4.ClaimsHeard

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

variable [scl : Scl] {M Xs : Type}

/-- The public ties that the seven `OutIs` want. -/
structure OutTies (P : FullPar Cb.Gl.E M Xs) (Pp : Pub) (hp : HPlan2) (o : Own) : Prop where
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
  k7 : P.own.toOwn.tail.s7.L.S.k = Pp.wsLay.lk
  lI : P.D.lL + 1 = Pp.rd.lNI
  lP : lDd P.D = Pp.y.lPd
  lfe : Pp.y.lfe = lFe P.D
  ll : Pp.y.h.ll - 1 = P.D.lL - 1
  wD : o.K.fin.wD = P.D.lL + lF P.D
  le5 : P.D.lL + lF P.D ≤ kS P.D
  le6 : lFe P.D ≤ kS P.D
  rs : kS P.D ≤ o.K.rs.size
  half : gl.val (invE (OnBytes.Model.ofNat 2)) = 2⁻¹

variable (P : FullPar Cb.Gl.E M Xs) {R : TailR} (W : TailM P.own.toOwn.tail R) {Pp : Pub}
  {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork} {t0 u : Tape} {H1 : Heard}
  {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}

omit scl in
/-- The norms' token point that K4 holds is what the tape's first round drew. -/
theorem pv_drawn (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (j : ℕ) : H1.PV.getD j zeroE = (drawnOf t0).getD j zeroE := by
  obtain ⟨u1, m1, _⟩ := Ld.nt
  obtain ⟨_, _, _, _, _, _, _, _, _, _, d0, _, e0, _, hPV, _⟩ := hearNorms_tape m1
  have hd : drawnOf t0 = d0 := by
    rw [e0]
    rfl
  rw [hPV, hd]
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- **The seven typed outputs are K4's own records, read.** -/
theorem outs_of_led (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (S : OutTies P Pp hp o) (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7)
    (I : TgRec g7 Pp hp o t0 H1 tT F4 G2 G3 G3')
    (hx : ∀ j : Fin P.own.toOwn.gT, x.2 j = gl.val ((drawnOf t0).getD j.val zeroE))
    (hz0 : P.zOf x.1 = zAt fo)
    (hzp : ∀ j, j < P.D.lT → zpos P.D (zAt fo) j = gl.val (H1.ztF.getD j zeroE)) :
    OutIs gl (aD1 W (ksOf Pp hp) (t0.drop 1) nz x g7) (levelRec Pp.rd.muV
        (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).2
        (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).1
        (orderDefault Pp.rd.muV) F4 ((ksOf Pp hp).tc1 (t0.drop 1))) ∧
      OutIs gl (aD2 W (ksOf Pp hp) (t0.drop 1) nz x g7) H1.tV.p ∧
      OutIs gl (aD3 W (ksOf Pp hp) (t0.drop 1) nz x g7) tT.p ∧
      OutIs gl (aD4 W (ksOf Pp hp) (t0.drop 1) nz x g7)
        (stackRec o.v o.H hp.lamS G2 ((ksOf Pp hp).tc4 (t0.drop 1))) ∧
      OutIs gl (aD5 W (ksOf Pp hp) (t0.drop 1) nz x g7)
        (levelRec Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF)
          (OnBytes.Model.Aff.slot o.K.sH1) (orderRange Pp.rd.muH) G3
          ((ksOf Pp hp).tc5 (t0.drop 1))) ∧
      OutIs gl (aD6 W (ksOf Pp hp) (t0.drop 1) nz x g7) (levelRec Pp.rd.muH2
        ((drawnOf ((((ksOf Pp hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).toArray ++
          downFrom o.K.rs Pp.y.lfe ++ tT.r)
        (Road.Rows.start2 Pp.y.LamM o.K.sH1
          (drawnOf ((((ksOf Pp hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).toArray)
        (orderRange Pp.rd.muH2) G3' ((ksOf Pp hp).tc6 (t0.drop 1))) ∧
      OutIs gl (stgT W.w7.num (ksOf Pp hp).k7 (((ksOf Pp hp).tcW (t0.drop 1)).drop 1) nz.b7
        (aS7 W (ksOf Pp hp) (t0.drop 1) nz x g7) g7.t7) o.wo.p := by
  have O3 := out3 P W Ld S.lt nz x g7 I.t3 hz0 (tscIn_heard Ld.c3).1 hzp
  have O4 := out4 P W Ld S.k4 nz x g7 I.t4
  exact ⟨out1 P W Ld S.eS S.m1 S.lI S.lP S.half nz x g7 rfl I.t1
      (fun j => by rw [pv_drawn Ld]; exact hx j),
    out2 P W Ld S.lt nz x g7 I.t2 hx, O3, O4,
    out5 P W Ld S.n5 S.e5 S.m5 S.k4 S.wD S.le5 S.rs nz x g7 O4 rfl I.t5 hz0
      (fun j hj => by rw [Ld.ztF]; exact hzp j hj),
    out6 P W Ld S.n6 S.e6 S.m6 S.k4 S.lt S.lfe S.le6 S.rs S.ll nz x g7 O3 O4 rfl I.t6,
    out7 P W Ld S.k7 nz x g7 I.t7⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pv_drawn
#print axioms OnBytes.Road.K4.outs_of_led
