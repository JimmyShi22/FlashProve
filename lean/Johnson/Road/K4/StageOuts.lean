-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/StageOuts.lean: AT A HEARING OF K4's TEXT IN A GROUP THAT IS NOT THE FIRST: THE
TYPED OUTPUTS OF THE FIRST, FIFTH AND SEVENTH STAGES, READ OFF THE TAPE, ARE K4's OWN
RECORDS, READ (`OutIs`, OnBytes/Tie/Pv/Lay/HearTieL.lean). With `out2`, `out3`, `out4`
(StageFits.lean, StageFitsMore.lean) that is six of the seven. Glue: `fits1`, `fits5`,
`fits7`; `stgT_out` (OwnJoint.lean) and the records of OwnRecs.lean, MergeRec.lean;
`stgT_stack_point` (PointsAt.lean). No draw, no count.

  `down_reads`: the batched sumcheck's typed out point, from the place k - n on, reads K4's
    challenges turned round (`downFrom rs n`).
  `fitsAt1`, `fitsAt5`: `StgFits` at these two stages' states at a hearing, at K4's own weights.
  `out1`: the product layer of the sums of squares. `out5`: the first product layer of the gated
    products. `out7`: the merge. The sixth stage: StageOutSix.lean.

Limits. PREMISES: `Led7` (the hearing's ledgers and tapes) · the targets are the records' · the
sizes' ties (muV, muH, lamS, lk, lNI, lPd against the library's sums; fin.wD) · two of the
value's three orders are the programs' · the token point in the first statement reads what the
tape's first round drew · zOf at the first statement is the lookup's point, whose tail reads ztF ·
the reading of 1/2. A group that is not the first.
-/
import Johnson.Road.K4.StageFitsRest
import Johnson.Road.K4.PointsAt
import Johnson.Road.K4.MergeRec
import Johnson.Road.FormsKeysEnd

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

/-- The typed out point from the place k - n on reads the challenges turned round. -/
theorem down_reads (ζ : ℕ → Cb.Gl.E) (rs : Array E) (k n : ℕ) (hn : n ≤ k) (hs : k ≤ rs.size)
    (hζ : ∀ j, j < k → ζ j = gl.val (rs.getD (k - 1 - j) zeroE)) (i : Fin n) :
    tailPt n (k - n) ζ i = gl.val ((downFrom rs n).getD i.val zeroE) := by
  have hi := i.isLt
  show ζ (k - n + i.val) = _
  rw [hζ _ (by omega)]
  unfold downFrom
  rw [rev_getD rs (le_trans hn hs) (by omega)]
  congr 2
  omega

variable [scl : Scl] {M Xs : Type} (P : FullPar Cb.Gl.E M Xs) {R : TailR}
  (W : TailM P.own.toOwn.tail R) {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}

/-- The weights of the product layer of the sums of squares, at a hearing. -/
theorem fitsAt1 (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (hS : P.eS = eDefault _) (hmu : P.D.lL + 1 + (lDd P.D + P.D.lT) = Pp.rd.muV)
    (hlI : P.D.lL + 1 = Pp.rd.lNI) (hlP : lDd P.D = Pp.y.lPd)
    (hhalf : gl.val (invE (OnBytes.Model.ofNat 2)) = 2⁻¹)
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E))
    (hx : ∀ j : Fin P.D.lT, (x.2 : Fin P.D.lT → Cb.Gl.E) j = gl.val (H1.PV.getD j.val zeroE)) :
    StgFits gl P.own.toOwn.tail.s1 (aS1 P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1) x)
      (levelWs Pp.rd.muV
        (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).2
        (orderDefault Pp.rd.muV)) Pp.rd.muV 2 := by
  have f0 := fits1 P hS (aS1 P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1) x)
    (Johnson.L5.Layers.rd gl (P.D.lL + 1) (drawnOf ((t0.drop 1).drop 1))) x.2 (fun _ => rfl)
    (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV (invE (OnBytes.Model.ofNat 2))
    (by rw [List.size_toArray, Ld.lI, hlI])
    (fun i => by
      show gl.val ((drawnOf ((t0.drop 1).drop 1)).getD i.val zeroE) = _
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD])
    hx hhalf
  rw [hmu, hlP] at f0
  exact f0

/-- **The product layer of the sums of squares.** -/
theorem out1 (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (hS : P.eS = eDefault _) (hmu : P.D.lL + 1 + (lDd P.D + P.D.lT) = Pp.rd.muV)
    (hlI : P.D.lL + 1 = Pp.rd.lNI) (hlP : lDd P.D = Pp.y.lPd)
    (hhalf : gl.val (invE (OnBytes.Model.ofNat 2)) = 2⁻¹)
    (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7) {p1 : Psc}
    (hp1 : p1 = levelRec Pp.rd.muV
      (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).2
      (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).1
      (orderDefault Pp.rd.muV) F4 ((ksOf Pp hp).tc1 (t0.drop 1)))
    (ht1 : g7.t1 = p1.target)
    (hx : ∀ j : Fin P.D.lT, (x.2 : Fin P.D.lT → Cb.Gl.E) j = gl.val (H1.PV.getD j.val zeroE)) :
    OutIs gl (aD1 W (ksOf Pp hp) (t0.drop 1) nz x g7) p1 := by
  obtain ⟨v1, c1⟩ := Ld.c1
  subst hp1
  exact stgT_out W.w1.num (ksOf Pp hp).k1 _ nz.b1 _ g7.t1 rfl (level_recAt c1) ht1
    (fitsAt1 P Ld hS hmu hlI hlP hhalf x hx)

/-- The weights of the product layer of the gated products, at a hearing. -/
theorem fitsAt5 (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (h9 : 9 ≤ P.D.lL + lF P.D + P.D.lT) (h5 : P.e5 = eRange _ h9)
    (hmu : P.D.lL + lF P.D + P.D.lT = Pp.rd.muH) (hk : kS P.D = hp.lamS)
    (hwD : o.K.fin.wD = P.D.lL + lF P.D) (hle : P.D.lL + lF P.D ≤ kS P.D)
    (hrs : kS P.D ≤ o.K.rs.size)
    (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7) {p4 : Psc}
    (O4 : OutIs gl (aD4 W (ksOf Pp hp) (t0.drop 1) nz x g7) p4) (hz0 : P.zOf x.1 = zAt fo)
    (hzp : ∀ j, j < P.D.lT → zpos P.D (zAt fo) j = gl.val (o.H.ztF.getD j zeroE)) :
    StgFits gl P.own.toOwn.tail.s5 (aS5 W (ksOf Pp hp) (t0.drop 1) nz x g7)
      (levelWs Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (orderRange Pp.rd.muH))
      Pp.rd.muH 2 := by
  have hζ : ∀ j, j < kS P.D → P.toOwnPar.zeta (aD4 W (ksOf Pp hp) (t0.drop 1) nz x g7).out j =
      gl.val (o.K.rs.getD (kS P.D - 1 - j) zeroE) := fun _ hj =>
    stgT_stack_point W.w4.num (ksOf Pp hp).k4 ((ksOf Pp hp).tc4 (t0.drop 1)) nz.b4 _ g7.t4 O4 hk
      Ld.c4 hj
  have f0 := fits5 P h9 h5 (aS5 W (ksOf Pp hp) (t0.drop 1) nz x g7)
    (downFrom o.K.rs (P.D.lL + lF P.D)) o.H.ztF
    (by
      unfold downFrom
      rw [rev_size o.K.rs (le_trans hle hrs), Nat.sub_zero])
    (fun i => down_reads _ o.K.rs (kS P.D) (P.D.lL + lF P.D) hle hrs hζ i)
    (fun i => by
      show zpos P.D (P.zOf x.1) i.val = _
      rw [hz0, hzp i.val i.isLt])
  rw [hmu, ← hwD] at f0
  exact f0

/-- **The product layer of the gated products.** -/
theorem out5 (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (h9 : 9 ≤ P.D.lL + lF P.D + P.D.lT) (h5 : P.e5 = eRange _ h9)
    (hmu : P.D.lL + lF P.D + P.D.lT = Pp.rd.muH) (hk : kS P.D = hp.lamS)
    (hwD : o.K.fin.wD = P.D.lL + lF P.D) (hle : P.D.lL + lF P.D ≤ kS P.D)
    (hrs : kS P.D ≤ o.K.rs.size)
    (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7) {p4 p5 : Psc}
    (O4 : OutIs gl (aD4 W (ksOf Pp hp) (t0.drop 1) nz x g7) p4)
    (hp5 : p5 = levelRec Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF)
      (OnBytes.Model.Aff.slot o.K.sH1) (orderRange Pp.rd.muH) G3 ((ksOf Pp hp).tc5 (t0.drop 1)))
    (ht5 : g7.t5 = p5.target) (hz0 : P.zOf x.1 = zAt fo)
    (hzp : ∀ j, j < P.D.lT → zpos P.D (zAt fo) j = gl.val (o.H.ztF.getD j zeroE)) :
    OutIs gl (aD5 W (ksOf Pp hp) (t0.drop 1) nz x g7) p5 := by
  obtain ⟨v5, c5⟩ := Ld.c5
  subst hp5
  exact stgT_out W.w5.num (ksOf Pp hp).k5 _ nz.b5 _ g7.t5 rfl (level_recAt c5) ht5
    (fitsAt5 P W Ld h9 h5 hmu hk hwD hle hrs nz x g7 O4 hz0 hzp)

/-- **The merge.** -/
theorem out7 (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (hk : P.own.toOwn.tail.s7.L.S.k = Pp.wsLay.lk)
    (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7) (ht7 : g7.t7 = o.wo.p.target) :
    OutIs gl (stgT W.w7.num (ksOf Pp hp).k7 (((ksOf Pp hp).tcW (t0.drop 1)).drop 1) nz.b7
      (aS7 W (ksOf Pp hp) (t0.drop 1) nz x g7) g7.t7) o.wo.p := by
  obtain ⟨cl, c7⟩ := Ld.c7
  exact stgT_out W.w7.num (ksOf Pp hp).k7 _ nz.b7 _ g7.t7 rfl (merge_recAt c7).1 ht7
    (fits7 P _ Pp.wsLay.lk hk)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.down_reads
#print axioms OnBytes.Road.K4.fitsAt1
#print axioms OnBytes.Road.K4.out1
#print axioms OnBytes.Road.K4.fitsAt5
#print axioms OnBytes.Road.K4.out5
#print axioms OnBytes.Road.K4.out7
