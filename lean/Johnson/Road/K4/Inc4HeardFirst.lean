-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Inc4HeardFirst.lean: THE FIRST GROUP's twin of Johnson/Road/K4/Inc4Heard.lean (its
part at the typed chain): the premise (D2) of the batched sumcheck's own row at a hearing.

The statements and proofs are that file's, turned to the first group's letters by a program
(FullFPar for FullPar; the chain P.ownF.toOwn.tail; the records LedG and TgRecF, which stand in
every group, with the tail's tape t0.drop (k0 g)) and compiled; each name bears an F.

Main names: `d2_fourF`.

Limits. As that file's. Nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.Inc4Heard
import Johnson.Road.K4.Claim4HeardFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Reading World Aff Fork Forest.Heard Level Tsc powers)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Road.Rows (Pub34)
open OnBytes.Tie.Pv.Lay (OutIs)
open OnBytes.Desc.First.P1 (gl Ks NzT TailM TailR Tg7 aY4 aS4 aD3 sentOf tapeEps tapeCl powers_val)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)
open OnBytes.Desc.First.K4 (k0)

variable [scl : Scl] {M Xs : Type}

/-- **(D2) at the batched sumcheck, at a hearing.** -/
theorem d2_fourF (P : FullFPar Cb.Gl.E M Xs) {R : TailR} (W : TailM P.ownF.toOwn.tail R) {Pp : Pub}
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
        fo.cEnd)
    (Hl : Fork) (hL : Fo.Later G Hl) (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (m : P.J → Cb.Gl.E) (cc : Cells Cb.Gl.E)
    (T : TrueAt Reading.gl (Hl.worldOf Reading.gl mask entry) X.p.v X.h.lt cc
      (pt Reading.gl X.Zp) (pt Reading.gl X.H.ztF))
    (hcc : cellsOf P.D cc = P.rd m) (n : ℕ) (he : fo.cEnd.ents = #[])
    (hsl : ∀ y ∈ fo.cEnd.slots.toList, y.1 < n)
    (hkI : ∑ j, P.kInc (P.ofp.fs.x0F x) j * m j = ∑ s : Fin n, kIncAt fo F s * mask s)
    (hmr : m P.rT = mask tT.sCl)
    (ho : overAt P.ip.Y3 (aD3 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7).out m =
      o.H.KT.value Reading.gl (Hl.worldOf Reading.gl mask entry)) :
    P.ownF.toOwn.tail.s4.L.T.par.inc (aS4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) m =
      gl.val g7.t4 - (stackStart o.v o.H G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g)))).value Reading.gl
        (Hl.worldOf Reading.gl mask entry) := by
  have c4 := first4F P W Ld X hρ hH hfo hscl hD htb hα hθ hT hom hst w nz x g7 ht4 O3 hz0 hk0 hfil
  have eT : X.tT = { tT with p := { tT.p with rowMade := true } } :=
    Option.some.inj (hT.symm.trans Ld.kTT)
  have h := startVal_pub X hρ hscl P.toMidPar hD htb (Hl.worldOf Reading.gl mask entry) cc T w
    (aS4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) m hcc
    (by rw [hH, hfo]; exact hz0) (by rw [hH]; exact hα) (by rw [hH]; exact hθ)
    (by
      rw [hH, hfo, kept_value gl ((Ld.l2.trans Ld.g2).trans hL) fo.cEnd hfil mask entry,
        ← kEnd_at fo F n mask entry he hsl, ← hkI, ← hk0]
      rfl)
    (by
      rw [eT]
      show gl.val ((sentOf ((((ksOf Pp hp).tcP (t0.drop (k0 g))).drop 1).drop
        ((ksOf Pp hp).k2 + 3))).getD 0 zeroE) - m P.rT =
          gl.val (Hl.vp.getD tT.sCl zeroE) - gl.val (Hl.mf.getD tT.sCl zeroE) * mask tT.sCl
      rw [tsc_cl_shown Ld.s1 Ld.c3 Hl (Ld.g1'.trans hL), tsc_cl_factor Ld.s1 Ld.c3 Hl
        (Ld.g1'.trans hL), tapeCl_sent, gl.one, one_mul, hmr]
      rfl)
    (by
      rw [hom, powers_val gl _ 2 1 (by decide), pow_one]
      rfl)
    (by rw [hH]; exact ho)
  have c4' : P.ip.inn.tg (aS4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) = gl.val g7.t4 := c4
  show ∑ j, P.ip.inn.inc (aS4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) j * m j = _
  rw [hst, ← h, c4']
  ring

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.d2_fourF
