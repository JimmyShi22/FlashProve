-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Inc4Heard.lean: AT A HEARING OF K4's TEXT IN A GROUP THAT IS NOT THE FIRST: THE
INCOMING FORM OF THE BATCHED SUMCHECK, TYPED, AT THE ENTRIES m, IS THE READING OF K4's TARGET LESS
THE VALUE OF K4's START FORM IN THE WORLD OF A LATER LEDGER WITH MASKS AND TRUE TABLES. It is the
clause (D2) of the own rows (Johnson/Road/K4/OwnD2.lean) at the fourth stage. One theorem. Glue:
`first4` (Claim4Heard.lean: the typed target is the reading of K4's) and `startVal_pub` (Inc4.lean).
No draw, no count.

  `d2_four`: under `Led7`, a public record X with the ties of `first4`, a ledger Hl later than G,
    a mask row, entries, and m:
    `s4.L.T.par.inc (aS4 …) m = gl g.t4 - (stackStart …).value gl (Hl.worldOf gl mask entry)`.

Limits. PREMISES THAT STAY, beside `first4`'s: T (the tables of the world are true at cells cc, and
these are the cells of m) · he, hsl (the lookup's end form has no entries, and slots below n) · hkI
(the typed form kInc at m is the end form's slots' factors against the mask row) · hmr (m at the
name rT is the mask under the terms' claimed sum) · ho (what the terms' sumcheck leaves, typed, is
KT's value in that world: `tie_scaled_over`, OnBytes/Desc/First/P1/RowValue.lean, with the summand's
public part 0). A group that is not the first.
-/
import Johnson.Road.K4.Claim4Heard
import Johnson.Road.K4.Inc4
import OnBytes.Desc.First.K4.FactorUnder

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

variable [scl : Scl] {M Xs : Type}

/-- **(D2) at the batched sumcheck, at a hearing.** -/
theorem d2_four (P : FullPar Cb.Gl.E M Xs) {R : TailR} (W : TailM P.own.toOwn.tail R) {Pp : Pub}
    {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork} {t0 u : Tape} {H1 : Heard}
    {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}
    (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (X : Pub34 Cb.Gl.E) (hρ : X.ρ = Reading.gl) (hH : X.H = o.H) (hfo : o.H.fo = fo)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (hD : X.D = P.D) (htb : X.tb = P.tb)
    (hα : X.alpha = o.H.fo.alpha) (hθ : X.theta = o.H.fo.theta) (hT : o.H.tT = some X.tT)
    (hom : X.om = powers (tapeEps ((ksOf Pp hp).tc4 (t0.drop 1))) 2)
    (hst : stackStart o.v o.H G2 ((ksOf Pp hp).tc4 (t0.drop 1)) = startOf X.H X.om X.parts)
    (w : ℕ → LW Cb.Gl.E) (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7)
    (ht4 : g7.t4 = (stackRec o.v o.H hp.lamS G2 ((ksOf Pp hp).tc4 (t0.drop 1))).target)
    (O3 : OutIs gl (aD3 W (ksOf Pp hp) (t0.drop 1) nz x g7) tT.p)
    (hz0 : P.zOf x.1 = zAt fo) (hk0 : P.kTg x.1 = kTgAt fo F) (hfil : Fo.FilledA F fo.cEnd)
    (Hl : Fork) (hL : Fo.Later G Hl) (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (m : P.J → Cb.Gl.E) (cc : Cells Cb.Gl.E)
    (T : TrueAt Reading.gl (Hl.worldOf Reading.gl mask entry) X.p.v X.h.lt cc
      (pt Reading.gl X.Zp) (pt Reading.gl X.H.ztF))
    (hcc : cellsOf P.D cc = P.rd m) (n : ℕ) (he : fo.cEnd.ents = #[])
    (hsl : ∀ y ∈ fo.cEnd.slots.toList, y.1 < n)
    (hkI : ∑ j, P.kInc x.1 j * m j = ∑ s : Fin n, kIncAt fo F s * mask s)
    (hmr : m P.rT = mask tT.sCl)
    (ho : overAt P.ip.Y3 (aD3 W (ksOf Pp hp) (t0.drop 1) nz x g7).out m =
      o.H.KT.value Reading.gl (Hl.worldOf Reading.gl mask entry)) :
    P.own.toOwn.tail.s4.L.T.par.inc (aS4 W (ksOf Pp hp) (t0.drop 1) nz x g7) m =
      gl.val g7.t4 - (stackStart o.v o.H G2 ((ksOf Pp hp).tc4 (t0.drop 1))).value Reading.gl
        (Hl.worldOf Reading.gl mask entry) := by
  have c4 := first4 P W Ld X hρ hH hfo hscl hD htb hα hθ hT hom hst w nz x g7 ht4 O3 hz0 hk0 hfil
  have eT : X.tT = { tT with p := { tT.p with rowMade := true } } :=
    Option.some.inj (hT.symm.trans Ld.kTT)
  have h := startVal_pub X hρ hscl P.toMidPar hD htb (Hl.worldOf Reading.gl mask entry) cc T w
    (aS4 W (ksOf Pp hp) (t0.drop 1) nz x g7) m hcc
    (by rw [hH, hfo]; exact hz0) (by rw [hH]; exact hα) (by rw [hH]; exact hθ)
    (by
      rw [hH, hfo, kept_value gl ((Ld.l2.trans Ld.g2).trans hL) fo.cEnd hfil mask entry,
        ← kEnd_at fo F n mask entry he hsl, ← hkI, ← hk0]
      rfl)
    (by
      rw [eT]
      show gl.val ((sentOf ((((ksOf Pp hp).tcP (t0.drop 1)).drop 1).drop
        ((ksOf Pp hp).k2 + 3))).getD 0 zeroE) - m P.rT =
          gl.val (Hl.vp.getD tT.sCl zeroE) - gl.val (Hl.mf.getD tT.sCl zeroE) * mask tT.sCl
      rw [tsc_cl_shown Ld.s1 Ld.c3 Hl (Ld.g1'.trans hL), tsc_cl_factor Ld.s1 Ld.c3 Hl
        (Ld.g1'.trans hL), tapeCl_sent, gl.one, one_mul, hmr]
      rfl)
    (by
      rw [hom, powers_val gl _ 2 1 (by decide), pow_one]
      rfl)
    (by rw [hH]; exact ho)
  have c4' : P.ip.inn.tg (aS4 W (ksOf Pp hp) (t0.drop 1) nz x g7) = gl.val g7.t4 := c4
  show ∑ j, P.ip.inn.inc (aS4 W (ksOf Pp hp) (t0.drop 1) nz x g7) j * m j = _
  rw [hst, ← h, c4']
  ring

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.d2_four
