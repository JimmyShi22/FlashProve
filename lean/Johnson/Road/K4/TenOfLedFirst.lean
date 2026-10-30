-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/TenOfLedFirst.lean: the first group's twin of TenOfLed.lean. At a hearing of K4's
text, under the record LedG (Johnson/Road/K4/OwnLedgersG.lean: any group), at the letters tailW Pf
of the first sub-proof's chain behind its three points (Cb/Pv/Lay/End/FirstShare.lean) and the tape
behind the points in front (t0.drop (k0 g)): the pairs of the typed merge of the weight claims, at
what the first group's merge reads of the typed batched sumcheck's output off the tape (st7F,
Cb/Pv/Lay/At/OwnFirstW.lean), and the weight claims of a public record Pub34 that is tied to the
hearing, number by number, say the same of every matrix W.

  `ten_of_ledF`: claim number i of the record's list X.cl is there, and on every W it is worth what
    the typed merge's pair number i is worth.

It lays ten_of_out (Johnson/Road/K4/TenOfOut.lean) at the hearing: StackTies by stackTies_of_ledF
and the end point by hpt_of_ledF (Johnson/Road/K4/OfLedFirst.lean), SigFits by sigFits_of_pub34
(Johnson/Road/K4/StackPub34.lean), the room and the layers by the typed parameters' own fields.
TenOfLed.lean's proof, turned to these letters by program; by hand: st7F in the place of st7 (st7F
is st7 with three further fields set, which the pairs do not read: Lean takes the one for the other
by unfolding), and its letter z7.

Limits. Premises: LedG; the fourth stage's claim; OutIs at the third and fourth stages; two numbers
of rounds; the numbering of the terms' end values; four sizes; the record X with its ties to the
hearing (its reading; what was heard; the challenges; the end point of the second token sumcheck;
its shown values; the drawn weights; D, the tables, the first layer, the matrix's column bits) and
the table of scales; ReadsTrue in some world (SigFits asks it); the two clauses on the lookup's
point; that the typed numbering is numK's. THE PAIRS ARE THE Pf.nW OLDER ONES: NOTHING ON THE
EMBEDDING's CLAIM, which the first group's merge hears last (tenEF). That X.cl is the front of the
list on which K4's text calls its merge is not said here, nor that Pf.nW is the number of claims
that the batched sumcheck hears in the first group. The group g is a letter: nothing here says that
it is the first. An identity on public data and any matrix W: nothing on which matrix is committed,
on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.TenOfLed
import Johnson.Road.K4.OfLedFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open OnBytes.Model (World Fork Psc Level Tsc powers)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard nEndT)
open OnBytes.Tie.Pv.Lay (OutIs)
open OnBytes.Desc.First.P1 (gl NzT Adds7 TailM TailR tailT tapeEps)
open OnBytes.Desc.First.K4 (k0)
open Inst.Model (Scl)

variable [scl : Scl] {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}
  {M X0 : Type} (Pf : FullFPar Cb.Gl.E M X0) {R : TailR} (W' : TailM (tailW Pf) R)

/-- **The typed merge's pairs against the record's claims, at a hearing**, at the first
sub-proof's letters. z7: the statement off which `st7F` reads the two further points and the
tokens; the pairs read none of the three. -/
theorem ten_of_ledF (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 (tailW Pf)) (x : Pf.ofp.fs.X3)
    (hc : (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d4.Claim
        ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).y4 x)) {p3 p4 : Psc}
    (O3 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d3 p3)
    (O4 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d4 p4)
    (k3 : (tailW Pf).s3.L.S.k = P.y.h.lt) (k4 : kS Pf.D = hp.lamS)
    (n3 : ∀ q : ShA Pf.D, W'.w3.num q = numA Pf.D q)
    (hNN : P.y.NN * P.y.Lam = Pf.D.nNu) (hLM : P.y.LamM = Pf.D.ne)
    (hNE : P.y.h.NE = Pf.D.nx) (hEnd : Pf.D.nNu + Pf.D.ne + Pf.D.ne * Pf.D.nx ≤ nEndT P.y)
    (X : Rows.Pub34 Cb.Gl.E) (Xρ : X.ρ = gl) (XH : X.H = o.H) (Xrs : X.c.rs = o.K.rs)
    (Xrt : X.c.rt = tT.r)
    (Xsh : ((Array.range (nEndT P.y)).mapM fun i => G2.shown (tT.sEnd + i)) = some X.p.shownT)
    (Xom : X.om = powers (tapeEps ((ksOf P hp).tc4 (t0.drop (k0 g)))) 2)
    (hD : X.D = Pf.D) (htb : X.tb = Pf.ip.tb) (hL0 : X.c.v.g * X.c.v.y.Lam = Pf.ip.L0)
    (hlk : X.lk = Pf.kW) (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam)
    (hz0 : ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2.st.z =
      zOf gl o.H.fo.zx o.H.fo.zy)
    (hz3 : Pf.ip.zP ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2.st .QK =
      zOf gl o.H.fo.zx o.H.fo.zy)
    (Wo : World Cb.Gl.E) (Mm : Mats Cb.Gl.E) (hRd : X.ReadsTrue Wo Mm)
    (hnum : ∀ i : Fin Pf.nW, ((numK Pf.D).symm (Pf.num i)).val = i.val) (z7 : Pf.ofp.fs.X3)
    (i : Fin Pf.nW) :
    ∃ c0, X.cl[i.val]? = some c0 ∧ ∀ W : Wm Cb.Gl.E,
      tval (Pf.wp0.ten i
          (Pf.st7F z7 ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2))
          (Inst.Model.Layout.Tensor.matOf W) =
        claimVal gl X.c.wsLay W c0 := by
  have T := stackTies_of_ledF Pf W' Ld nz a x hc O3 k3 n3 hNN hLM hNE hEnd Xsh Xom hz0 hz3
  have S := sigFits_of_pub34 X Wo Mm hRd
  rw [← hscl, Xρ, hD, XH, htb, hL0, hlk, Xrt] at S
  have hpt := hpt_of_ledF Pf W' Ld nz a x O4 k4
  rw [← Xrs] at hpt
  exact ten_of_out Pf.ip Pf.kW Pf.hW Pf.nW Pf.Wn Pf.num Pf.w7 Pf.c7 _ T S hpt
    (Pf.ip.rP ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2.st
      (fun _ => 0) .G) Pf.hH
    (ts_eq X.hy X.S.p3 X.hN X.hrd X.hTS) X.hp X.hcl Pf.hL hnum i

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ten_of_ledF
