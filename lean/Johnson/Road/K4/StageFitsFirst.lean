-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StageFitsFirst.lean: THE FIRST GROUP's twin of Johnson/Road/K4/StageFits.lean (its
part at the typed chain): the third stage fits and its typed output is K4's record.

The statements and proofs are that file's, turned to the first group's letters by a program
(FullFPar for FullPar; the chain P.ownF.toOwn.tail; the records LedG and TgRecF, which stand in
every group, with the tail's tape t0.drop (k0 g)) and compiled; each name bears an F.

Main names: `fits3F` · `out3F`.

Limits. As that file's. Nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.StageFits
import Johnson.Road.K4.OwnLedgersG
import Johnson.Road.K4.ClaimsHeardFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Reading Fork Forest.Heard Level Tsc)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Psc (Weight)
open OnBytes.Tie.Pv.Lay (StgFits OutIs stgFits_eq stgFits_plain)
open OnBytes.Desc.First.P1 (gl NzT TailM TailR Tg7 aD3 aS3 tscWs plainWs)
open Inst.Model (Scl)
open Inst.Model.FFSeg (zpos)
open OnBytes.Desc.First.K4 (k0)

variable [scl : Scl] {M Xs : Type}

/-- **The terms' token sumcheck.** -/
theorem fits3F (P : FullFPar Cb.Gl.E M Xs) (z : ℕ → Cb.Gl.E) (zs : List E) (hl : zs.length = P.D.lT)
    (hz : ∀ j, j < P.D.lT → zpos P.D z j = gl.val (zs.getD j zeroE)) :
    StgFits gl P.ownF.toOwn.tail.s3 z (tscWs zs) P.D.lT 1 :=
  stgFits_tsc P.ownF.toOwn.tail.s3 z zs rfl (fun _ => rfl) hl
    fun i => congrArg some (hz i.val i.isLt)

/-- **At a hearing the typed output of the terms' sumcheck is K4's record, read.** -/
theorem out3F (P : FullFPar Cb.Gl.E M Xs) {R : TailR} (W : TailM P.ownF.toOwn.tail R) {Pp : Pub}
    {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork} {t0 u : Tape} {H1 : Heard}
    {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}
    (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (hlt : P.D.lT = Pp.y.h.lt) (nz : NzT P.ownF.toOwn.tail (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7) (ht3 : g7.t3 = tT.p.target)
    (hz0 : P.zOf (P.ofp.fs.x0F x) = zAt fo) (hzl : Pp.y.h.lt ≤ H1.ztF.size)
    (hzp : ∀ j, j < P.D.lT → zpos P.D (zAt fo) j = gl.val (H1.ztF.getD j zeroE)) :
    OutIs gl (aD3 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) tT.p := by
  have hl : (H1.ztF.toList.take Pp.y.h.lt).length = P.D.lT := by
    rw [List.length_take, Array.length_toList, hlt]
    exact Nat.min_eq_left hzl
  have f0 : StgFits gl P.ownF.toOwn.tail.s3 (aS3 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (tscWs (H1.ztF.toList.take Pp.y.h.lt)) P.D.lT 1 := by
    refine fits3F P _ _ hl fun j hj => ?_
    have e : aS3 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7 = P.zOf (P.ofp.fs.x0F x) := rfl
    rw [e, hz0, hzp j hj]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (hlt ▸ hj),
      ← List.getD_eq_getElem?_getD]
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  have f : StgFits gl P.ownF.toOwn.tail.s3 (aS3 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (tscWs (H1.ztF.toList.take Pp.y.h.lt)) Pp.y.h.lt 1 :=
    ⟨f0.k.trans hlt, f0.dY, f0.two, f0.fit⟩
  exact stgT_out W.w3.num (ksOf Pp hp).k3 _ nz.b3 _ g7.t3 rfl (tsc_recAt Ld.c3) ht3 f

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.fits3F
#print axioms OnBytes.Road.K4.out3F
