-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StageFitsMoreFirst.lean: THE FIRST GROUP's twin of
Johnson/Road/K4/StageFitsMore.lean (its part at the typed chain): the second and the fourth stage.

The statements and proofs are that file's, turned to the first group's letters by a program
(FullFPar for FullPar; the chain P.ownF.toOwn.tail; the records LedG and TgRecF, which stand in
every group, with the tail's tape t0.drop (k0 g)) and compiled; each name bears an F.

Main names: `fits2F` · `fits4F` · `out2F` · `out4F`.

Limits. As that file's. Nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.StageFitsMore
import Johnson.Road.K4.StageFitsFirst

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
open OnBytes.Tie.Pv.Lay (StgFits OutIs stgFits_eq)
open OnBytes.Desc.First.P1 (gl NzT TailM TailR Tg7 aD2 aS2 aD4 aS4 tscWs plainWs levelWs drawnOf)
open Inst.Model (Scl)
open OnBytes.Desc.First.K4 (k0)

variable [scl : Scl] {M Xs : Type}

/-- **The products' token sumcheck.** -/
theorem fits2F (P : FullFPar Cb.Gl.E M Xs) (st : P.ownF.toOwn.tail.s2.L.St) (zs : List E)
    (hl : zs.length = P.D.lT)
    (hw : ∀ i, P.ownF.toOwn.tail.s2.L.S.w st i = some (gl.val (zs.getD i.val zeroE))) :
    StgFits gl P.ownF.toOwn.tail.s2 st (tscWs zs) P.D.lT 2 :=
  stgFits_tsc P.ownF.toOwn.tail.s2 st zs rfl (fun _ => rfl) hl hw

/-- **The batched sumcheck.** -/
theorem fits4F (P : FullFPar Cb.Gl.E M Xs) (st : P.ownF.toOwn.tail.s4.L.St) (k : ℕ)
    (hk : P.ownF.toOwn.tail.s4.L.S.k = k) : StgFits gl P.ownF.toOwn.tail.s4 st (plainWs k) k 2 :=
  stgFits_plainAt P.ownF.toOwn.tail.s4 st k hk rfl (fun _ => rfl) fun _ => rfl

variable (P : FullFPar Cb.Gl.E M Xs) {R : TailR} (W : TailM P.ownF.toOwn.tail R) {Pp : Pub}
  {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork} {t0 u : Tape} {H1 : Heard}
  {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}

/-- **At a hearing the typed output of the products' token sumcheck is K4's record, read.** -/
theorem out2F (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (hlt : P.D.lT = Pp.y.h.lt) (nz : NzT P.ownF.toOwn.tail (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7) (ht2 : g7.t2 = H1.tV.p.target)
    (hx : ∀ j : Fin P.D.lT, P.ofp.fs.pvF x j = gl.val ((drawnOf t0).getD j.val zeroE)) :
    OutIs gl (aD2 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) H1.tV.p := by
  obtain ⟨u1, m1, _⟩ := Ld.nt
  obtain ⟨_, _, _, _, _, _, _, _, _, _, d0, _, e0, l0, hPV, _⟩ := hearNorms_tape m1
  obtain ⟨v2, c2⟩ := Ld.c2
  have hd : drawnOf t0 = d0 := by
    rw [e0]
    rfl
  have ht : H1.PV.toList.take Pp.y.h.lt = d0 := by
    rw [hPV, ← l0]
    exact List.take_length
  have f0 : StgFits gl P.ownF.toOwn.tail.s2 (aS2 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (tscWs (H1.PV.toList.take Pp.y.h.lt)) P.D.lT 2 := by
    rw [ht]
    refine fits2F P _ d0 (l0.trans hlt.symm) fun i => ?_
    rw [← hd]
    exact congrArg some (hx i)
  exact stgT_out W.w2.num (ksOf Pp hp).k2 _ nz.b2 _ g7.t2 rfl (tsc_recAt c2) ht2
    ⟨f0.k.trans hlt, f0.dY, f0.two, f0.fit⟩

/-- **At a hearing the typed output of the batched sumcheck is K4's record, read.** -/
theorem out4F (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (hk : P.ownF.toOwn.tail.s4.L.S.k = hp.lamS)
    (nz : NzT P.ownF.toOwn.tail (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7)
    (ht4 : g7.t4 = (stackRec o.v o.H hp.lamS G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g)))).target) :
    OutIs gl (aD4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (stackRec o.v o.H hp.lamS G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g)))) :=
  stgT_out W.w4.num (ksOf Pp hp).k4 _ nz.b4 _ g7.t4 rfl (stack_recAt Ld.c4) ht4
    (fits4F P _ hp.lamS hk)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.fits2F
#print axioms OnBytes.Road.K4.fits4F
#print axioms OnBytes.Road.K4.out2F
#print axioms OnBytes.Road.K4.out4F
