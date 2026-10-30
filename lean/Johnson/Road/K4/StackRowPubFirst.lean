-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackRowPubFirst.lean: THE FIRST GROUP's twin of Johnson/Road/K4/StackRowPub.lean:
the premise (D4) of the batched sumcheck's own row at a hearing of K4's text, for the first group's
chain, with what d4_of_led_numF (Johnson/Road/K4/StackRowFirst.lean) asks of the panels paid from a
public record Pub34 that is tied to the hearing.

The statement and proof are that file's, turned to the first group's letters
(Johnson/Road/K4/AtFirst.lean says which) by a program and compiled.

Main name: `d4_of_pubF`.
Limits. As that file's. An identity on public numbers and the tape's words: nothing on a draw, on
soundness or on hiding.


-/
import Johnson.Road.K4.StackRowFirst
import Johnson.Road.K4.StackRowPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open OnBytes.Model (World Fork Psc Level Tsc)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard nEndT callsTS)
open OnBytes.Tie.Pv.Lay (OutIs)
open OnBytes.Desc.First.P1 (gl NzT Adds7 TailM TailR tailT)
open OnBytes.Desc.First.K4 (hearStack_rs k0)
open Inst.Model (Scl)

variable [scl : Scl] {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}
  {M X0 : Type} (Pf : FullFPar Cb.Gl.E M X0) {R : TailR} (W' : TailM (tailW Pf) R)

/-- **(D4) of the batched sumcheck at a hearing, from a public record.** -/
theorem d4_of_pubF (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 (tailW Pf)) (x : Pf.ofp.fs.X3)
    (hc : (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d4.Claim ((tailT W' (ksOf P hp) (t0.drop (k0
        g)) nz a).y4 x)) {p3 p4 : Psc}
    (O3 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d3 p3) (O4 : OutIs gl (tailT W'
        (ksOf P hp) (t0.drop (k0 g)) nz a).d4 p4)
    (k3 : (tailW Pf).s3.L.S.k = P.y.h.lt) (k4 : kS Pf.D = hp.lamS)
    (n3 : ∀ q : ShA Pf.D, W'.w3.num q = numA Pf.D q)
    (n4 : ∀ q : IA Pf.D ⊕ IB Pf.D, W'.w4.num q = num4 Pf.D (numK Pf.D) q)
    (hyv : o.v.y = P.y) (hNN : P.y.NN * P.y.Lam = Pf.D.nNu) (hLM : P.y.LamM = Pf.D.ne)
    (hNE : P.y.h.NE = Pf.D.nx) (hEnd : Pf.D.nNu + Pf.D.ne + Pf.D.ne * Pf.D.nx ≤ nEndT P.y)
    (X : Rows.Pub34 Cb.Gl.E) (Xρ : X.ρ = gl) (Xp : X.p = envOfHear P o X.p.shownT)
    (XH : X.H = o.H) (Xrd : X.rd = P.rd)
    (Xsh : ((Array.range (nEndT P.y)).mapM fun i => G2.shown (tT.sEnd + i)) = some X.p.shownT)
    (hD : X.D = Pf.D) (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam)
    (hz0 : ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2.st.z = zOf gl
        o.H.fo.zx o.H.fo.zy)
    (hz3 : Pf.ip.zP ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2.st .QK =
      zOf gl o.H.fo.zx o.H.fo.zy)
    (Wo : World Cb.Gl.E) (Mm : Mats Cb.Gl.E) (hRd : X.ReadsTrue Wo Mm) :
    Pf.ip.inn.Sm.pol a.st4
        (Pf.ip.inn.Kp.outPt Pf.ip.inn.Mk ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz
            a).z7 x)).2)
        (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d4.v =
      gl.val (mulE o.K.fin.As o.K.fin.Bs) := by
  have eTS : X.TS = [0, 1, 2, 5] := ts_eq X.hy X.S.p3 X.hN X.hrd X.hTS
  have hvy : X.p.v.y = P.y := by
    rw [Xp]
    exact hyv
  have hTS : callsTS P = some [0, 1, 2, 5] := by
    have q := X.hTS
    rw [Xrd, hvy, eTS] at q
    exact q
  have hcl : X.c.weightClaims [0, 1, 2, 5] = some X.cl := by
    rw [← eTS]
    exact X.hcl
  have S0 := sigFits_of_pub34 X Wo Mm hRd
  rw [← hscl, Xρ, hD, XH] at S0
  have S : SigFits gl Wo (envOfHear P o X.p.shownT) X.c X.h X.pc X.s Pf.D X.lk
      (X.c.v.g * X.c.v.y.Lam) (cellsAt X.p.v.y Mm) (cellsOf Pf.D (cellsAt X.p.v.y Mm))
      (pt gl X.Zp) (zOf gl o.H.fo.zx o.H.fo.zy) (pt gl X.c.rt) (zetaOf gl X.c Pf.D) X.tb := by
    rw [← Xp]
    exact S0
  exact d4_of_led_numF Pf W' Ld nz a x hc O3 O4 k3 k4 n3 n4
    (le_of_eq (ncl_of_ledF Ld Xsh S hTS hcl)) hyv hNN hLM hNE hEnd Xsh hz0 hz3 S hTS hcl
    (by rw [hearStack_rs Ld.c4, k4])

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.d4_of_pubF
