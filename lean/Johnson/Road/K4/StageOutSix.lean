-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/StageOutSix.lean: Johnson/Road/K4/StageOuts.lean ENDS: AT A HEARING OF K4's TEXT IN
A GROUP THAT IS NOT THE FIRST THE TYPED OUTPUT OF THE SIXTH STAGE (the product layer of the routed
experts' gated products), READ OFF THE TAPE, IS K4's OWN RECORD, READ (`OutIs`). Two theorems
(`fitsAt6`: `StgFits` at that stage's state, at K4's own weights; `out6`). Glue: `fits6`
(StageFitsRest.lean), `down_reads` (StageOuts.lean), `stgT_stack_point`,
`stgT_tsc_point` (PointsAt.lean), `stgT_out` (OwnJoint.lean), `level_recAt` (OwnRecs.lean). No draw,
no count.

Limits. PREMISES: `Led7` · `OutIs` at the third and fourth stages (`out3`, `out4`) · the sixth
target is the record's · the sizes' ties (muH2, lamS, lt, lfe, ll against the library's) · the
value's order e6 is the programs' range order. A group that is not the first.
-/
import Johnson.Road.K4.StageOuts
import Blocks.Wired

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Reading Fork Forest.Heard Level Tsc Psc orderRange)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard downFrom)
open OnBytes.Tie.Pv.Lay (StgFits OutIs eRange)
open OnBytes.Desc.First.P1 (gl NzT TailM TailR Tg7 aD3 aD4 aD6 aS6 drawnOf levelRec levelWs)
open Inst.Model (Scl)
open Inst.Model.FFSeg (lFe)

variable [scl : Scl] {M Xs : Type} (P : FullPar Cb.Gl.E M Xs) {R : TailR}
  (W : TailM P.own.toOwn.tail R) {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}

/-- The weights of the product layer of the routed experts' gated products, at a hearing. -/
theorem fitsAt6 (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (h9 : 9 ≤ P.D.lL - 1 + (lFe P.D + P.D.lT)) (h6 : P.e6 = eRange _ h9)
    (hmu : P.D.lL - 1 + (lFe P.D + P.D.lT) = Pp.rd.muH2) (hk4 : kS P.D = hp.lamS)
    (hk3 : P.D.lT = Pp.y.h.lt) (hlfe : Pp.y.lfe = lFe P.D) (hle : lFe P.D ≤ kS P.D)
    (hrs : kS P.D ≤ o.K.rs.size) (hll : Pp.y.h.ll - 1 = P.D.lL - 1)
    (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7) {p4 : Psc}
    (O3 : OutIs gl (aD3 W (ksOf Pp hp) (t0.drop 1) nz x g7) tT.p)
    (O4 : OutIs gl (aD4 W (ksOf Pp hp) (t0.drop 1) nz x g7) p4) :
    StgFits gl P.own.toOwn.tail.s6 (aS6 W (ksOf Pp hp) (t0.drop 1) nz x g7)
      (levelWs Pp.rd.muH2
        ((drawnOf ((((ksOf Pp hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).toArray ++
          downFrom o.K.rs Pp.y.lfe ++ tT.r) (orderRange Pp.rd.muH2)) Pp.rd.muH2 2 := by
  have hζ : ∀ j, j < kS P.D → P.toOwnPar.zeta (aD4 W (ksOf Pp hp) (t0.drop 1) nz x g7).out j =
      gl.val (o.K.rs.getD (kS P.D - 1 - j) zeroE) := fun _ hj =>
    stgT_stack_point W.w4.num (ksOf Pp hp).k4 ((ksOf Pp hp).tc4 (t0.drop 1)) nz.b4 _ g7.t4 O4 hk4
      Ld.c4 hj
  have hr : ∀ i : Fin P.D.lT,
      (P.toOwnPar.st6 (aD4 W (ksOf Pp hp) (t0.drop 1) nz x g7).out).rt i =
        gl.val (tT.r.getD i.val zeroE) := fun i => by
    have q := stgT_tsc_point W.w3.num (ksOf Pp hp).k3 _ nz.b3 _ g7.t3 O3 hk3 Ld.c3 (j := i.val)
      i.isLt
    exact (q.trans (Blocks.nat_of_lt _ i.isLt)).symm
  have f0 := fits6 P h9 h6 (P.toOwnPar.st6 (aD4 W (ksOf Pp hp) (t0.drop 1) nz x g7).out)
    (Johnson.L5.Layers.rd gl (P.D.lL - 1)
      (drawnOf ((((ksOf Pp hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)))
    (drawnOf ((((ksOf Pp hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).toArray
    (downFrom o.K.rs (lFe P.D)) tT.r
    (by rw [List.size_toArray, Ld.lM, hll])
    (by
      unfold downFrom
      rw [rev_size o.K.rs (le_trans hle hrs), Nat.sub_zero])
    (fun i => by
      show gl.val ((drawnOf
        ((((ksOf Pp hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).getD i.val zeroE) = _
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD])
    (fun i => down_reads _ o.K.rs (kS P.D) (lFe P.D) hle hrs hζ i) hr
  rw [hmu, ← hlfe] at f0
  exact f0

/-- **The product layer of the routed experts' gated products.** -/
theorem out6 (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (h9 : 9 ≤ P.D.lL - 1 + (lFe P.D + P.D.lT)) (h6 : P.e6 = eRange _ h9)
    (hmu : P.D.lL - 1 + (lFe P.D + P.D.lT) = Pp.rd.muH2) (hk4 : kS P.D = hp.lamS)
    (hk3 : P.D.lT = Pp.y.h.lt) (hlfe : Pp.y.lfe = lFe P.D) (hle : lFe P.D ≤ kS P.D)
    (hrs : kS P.D ≤ o.K.rs.size) (hll : Pp.y.h.ll - 1 = P.D.lL - 1)
    (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7) {p4 p6 : Psc}
    (O3 : OutIs gl (aD3 W (ksOf Pp hp) (t0.drop 1) nz x g7) tT.p)
    (O4 : OutIs gl (aD4 W (ksOf Pp hp) (t0.drop 1) nz x g7) p4)
    (hp6 : p6 = levelRec Pp.rd.muH2
      ((drawnOf ((((ksOf Pp hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).toArray ++
        downFrom o.K.rs Pp.y.lfe ++ tT.r)
      (Road.Rows.start2 Pp.y.LamM o.K.sH1
        (drawnOf ((((ksOf Pp hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).toArray)
      (orderRange Pp.rd.muH2) G3' ((ksOf Pp hp).tc6 (t0.drop 1)))
    (ht6 : g7.t6 = p6.target) :
    OutIs gl (aD6 W (ksOf Pp hp) (t0.drop 1) nz x g7) p6 := by
  subst hp6
  exact stgT_out W.w6.num (ksOf Pp hp).k6 _ nz.b6 _ g7.t6 rfl (level_recAt Ld.c6) ht6
    (fitsAt6 P W Ld h9 h6 hmu hk4 hk3 hlfe hle hrs hll nz x g7 O3 O4)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.fitsAt6
#print axioms OnBytes.Road.K4.out6
