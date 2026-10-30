-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StageFitsAt.lean: `StgFits` AT THE STATES OF THE SECOND AND THIRD STAGES AT A
HEARING OF K4's TEXT, AT K4's OWN WEIGHTS AND NUMBERS OF ROUNDS: what the proofs of `out2`
(StageFitsMore.lean) and `out3` (StageFits.lean) make on their way, as statements of their own, for
the own rows. Two theorems. (The first, fifth and sixth stages: `fitsAt1`, `fitsAt5`, `fitsAt6`,
StageOuts.lean and StageOutSix.lean; the fourth and seventh: `fits4`, `fits7` at every state.) No
draw, no count.

Limits. PREMISES: `Led7` · lT = lt · the token point in the first statement reads what the tape's
first round drew · zOf at the first statement is the lookup's point, whose tail reads ztF. A group
that is not the first.
-/
import Johnson.Road.K4.StageFitsMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Reading Fork Forest.Heard Level Tsc)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Tie.Pv.Lay (StgFits)
open OnBytes.Desc.First.P1 (gl NzT TailM TailR Tg7 aS2 aS3 drawnOf tscWs tscIn_heard)
open Inst.Model (Scl)
open Inst.Model.FFSeg (zpos)

variable [scl : Scl] {M Xs : Type} (P : FullPar Cb.Gl.E M Xs) {R : TailR}
  (W : TailM P.own.toOwn.tail R) {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}

/-- The weights of the products' token sumcheck, at a hearing. -/
theorem fitsAt2 (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (hlt : P.D.lT = Pp.y.h.lt) (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7)
    (hx : ∀ j : Fin P.own.toOwn.gT, x.2 j = gl.val ((drawnOf t0).getD j.val zeroE)) :
    StgFits gl P.own.toOwn.tail.s2 (aS2 W (ksOf Pp hp) (t0.drop 1) nz x g7)
      (tscWs (H1.PV.toList.take Pp.y.h.lt)) Pp.y.h.lt 2 := by
  obtain ⟨u1, m1, _⟩ := Ld.nt
  obtain ⟨_, _, _, _, _, _, _, _, _, _, d0, _, e0, l0, hPV, _⟩ := hearNorms_tape m1
  have hd : drawnOf t0 = d0 := by
    rw [e0]
    rfl
  have ht : H1.PV.toList.take Pp.y.h.lt = d0 := by
    rw [hPV, ← l0]
    exact List.take_length
  have f0 : StgFits gl P.own.toOwn.tail.s2 (aS2 W (ksOf Pp hp) (t0.drop 1) nz x g7)
      (tscWs (H1.PV.toList.take Pp.y.h.lt)) P.D.lT 2 := by
    rw [ht]
    refine fits2 P _ d0 (l0.trans hlt.symm) fun i => ?_
    rw [← hd]
    exact congrArg some (hx i)
  exact ⟨f0.k.trans hlt, f0.dY, f0.two, f0.fit⟩

/-- The weights of the terms' token sumcheck, at a hearing. -/
theorem fitsAt3 (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (hlt : P.D.lT = Pp.y.h.lt) (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7) (hz0 : P.zOf x.1 = zAt fo)
    (hzp : ∀ j, j < P.D.lT → zpos P.D (zAt fo) j = gl.val (H1.ztF.getD j zeroE)) :
    StgFits gl P.own.toOwn.tail.s3 (aS3 W (ksOf Pp hp) (t0.drop 1) nz x g7)
      (tscWs (H1.ztF.toList.take Pp.y.h.lt)) Pp.y.h.lt 1 := by
  have hzl : Pp.y.h.lt ≤ H1.ztF.size := (tscIn_heard Ld.c3).1
  have hl : (H1.ztF.toList.take Pp.y.h.lt).length = P.D.lT := by
    rw [List.length_take, Array.length_toList, hlt]
    exact Nat.min_eq_left hzl
  have f0 : StgFits gl P.own.toOwn.tail.s3 (aS3 W (ksOf Pp hp) (t0.drop 1) nz x g7)
      (tscWs (H1.ztF.toList.take Pp.y.h.lt)) P.D.lT 1 := by
    refine fits3 P _ _ hl fun j hj => ?_
    have e : aS3 W (ksOf Pp hp) (t0.drop 1) nz x g7 = P.zOf x.1 := rfl
    rw [e, hz0, hzp j hj]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (hlt ▸ hj),
      ← List.getD_eq_getElem?_getD]
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  exact ⟨f0.k.trans hlt, f0.dY, f0.two, f0.fit⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.fitsAt2
#print axioms OnBytes.Road.K4.fitsAt3
