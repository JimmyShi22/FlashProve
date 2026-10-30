-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Claim4HeardFirst.lean: THE FIRST GROUP's twin of Johnson/Road/K4/Claim4Heard.lean
(its part at the typed chain): the fourth stage's claimed sum at a hearing.

The statements and proofs are that file's, turned to the first group's letters by a program
(FullFPar for FullPar; the chain P.ownF.toOwn.tail; the records LedG and TgRecF, which stand in
every group, with the tail's tape t0.drop (k0 g)) and compiled; each name bears an F.

Main names: `first4F`.

Limits. As that file's. Nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.Claim4Heard
import Johnson.Road.K4.Claim4First
import Johnson.Road.K4.OwnLedgersG
import Cb.Pv.Lay.At.OwnFirstW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Reading World Aff Fork Forest.Heard Level Tsc powers)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Road.Rows (Pub34)
open OnBytes.Tie.Pv.Att (shownW public_value)
open OnBytes.Tie.Pv.Lay (OutIs)
open OnBytes.Desc.First.P1 (gl Ks NzT TailM TailR Tg7 aY4 aD3 sentOf tapeEps tapeCl powers_val)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)
open OnBytes.Desc.First.K4 (k0)

variable [scl : Scl] {M Xs : Type}

/-- **The fourth equation on the claimed sums, at a hearing.** -/
theorem first4F (P : FullFPar Cb.Gl.E M Xs) {R : TailR} (W : TailM P.ownF.toOwn.tail R) {Pp : Pub}
    {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork} {t0 u : Tape} {H1 : Heard}
    {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}
    (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (X : Pub34 Cb.Gl.E) (hρ : X.ρ = Reading.gl) (hH : X.H = o.H) (hfo : o.H.fo = fo)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (hD : X.D = P.D) (htb : X.tb = P.tb)
    (hα : X.alpha = o.H.fo.alpha) (hθ : X.theta = o.H.fo.theta) (hT : o.H.tT = some X.tT)
    (hom : X.om = powers (tapeEps ((ksOf Pp hp).tc4 (t0.drop (k0 g)))) 2)
    (hst : stackStart o.v o.H G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g))) = startOf X.H X.om X.parts)
    (w : ℕ → LW Cb.Gl.E) (nz : NzT P.ownF.toOwn.tail (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7)
    (ht4 : g7.t4 = (stackRec o.v o.H hp.lamS G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g)))).target)
    (O3 : OutIs gl (aD3 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) tT.p)
    (hz0 : P.zOf (P.ofp.fs.x0F x) = zAt fo) (hk0 : P.kTg (P.ofp.fs.x0F x) = kTgAt fo F) (hfil :
        Fo.FilledA F
        fo.cEnd) :
    (P.ownF.toOwn.tail.s4.cl (aY4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (Johnson.L5.Layers.rd gl P.ownF.toOwn.tail.s4.n
        (sentOf (((ksOf Pp hp).tc4 (t0.drop (k0 g))).drop 1)))).1 = gl.val g7.t4 := by
  obtain ⟨u1, _, hTm⟩ := Ld.nt
  have eT : X.tT = { tT with p := { tT.p with rowMade := true } } :=
    Option.some.inj (hT.symm.trans Ld.kTT)
  have sh := terms_shown gl Ld.s1 hTm X.tT hT G2 (Fo.Later.refl G2)
  have ht : gl.val g7.t4 = (startOf X.H X.om X.parts).value Reading.gl
      (G2.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0) := by
    rw [ht4, public_value gl G2 _ _ (stack_target Ld.c4), hst, worldOf_zero_eq]
  refine claim4F X hρ hscl P hD htb F G2 w _ _ _ rfl g7.t4 ht (by rw [hH]; exact hα)
    (by rw [hH]; exact hθ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (sh.2 _)
  · rw [hH, hfo]
    exact hz0
  · rw [hH, hfo]
    exact hk0
  · rw [eT]
    show _ = gl.val (G2.vp.getD tT.sCl zeroE)
    rw [tsc_cl_shown Ld.s1 Ld.c3 G2 Ld.l1, tapeCl_sent]
    rfl
  · rw [hom, powers_val gl _ 2 1 (by decide), pow_one]
    rfl
  · rw [eT]
    exact O3.fin
  · rw [eT]
    exact O3.eps
  · rw [hH, hfo]
    exact kept_value gl Ld.l2 fo.cEnd hfil _ _
  · intro j h1 h2
    rw [sh.1 j h1 h2]
    exact gl.zero

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.first4F
