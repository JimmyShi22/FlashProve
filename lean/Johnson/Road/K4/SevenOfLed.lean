-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SevenOfLed.lean: seven of the eight parts of the library's ledger of a layers'
sub-proof hold, at a hearing of K4's text in a group that is not the first: seven_parts
(Johnson/Road/K4/SevenParts.lean) with its ties of letters paid from the record Led7 of the
hearing's calls and ledgers.

  `ztS`: the letter zt: the token part of the lookup's point in the batched sumcheck's state.
  `seven_of_led`: the parts sq, bat, led, terms, gated, hot and stack of the ledger clF hold of yL,
    at the last statement e that the chain's data off K4's tape make.
Paid here, premises of seven_parts no more: PointTies (points_of_led), SlotTies (slotTies_of over
slots_of_led, with sqW_of_led, sqG_of_led, batW_of_led, eps_of_words, two_of_words, g5W_of_led,
g6W_of_led), StackTies (stackTies_of_led), the batched sumcheck's number of rounds, end point
(hpt_of_led) and two hidden end values (stack_of_led).
What is still asked, and by nothing here shown:
  Led7 at a ledger that is Sized; OutIs at six stages; the numbering NumTies; the fourth stage's
    claim; that each typed stage has as many variables' rounds as the plan says, and the three typed
    permutations are eDefault and eRange;
  a public record X : Pub34 whose letters are the hearing's (eleven equations);
  two ledgers later than the hearing's, F1 for the run "front" and F2 for the run "back"; in the
    world of each, every table of the reads holds what it says of the matrices Mm (ReadsTrue); the
    forms of "front" are worth 0 in the first, the record's two side claims in the second;
  the typed parameters' table of scales, sizes, tables and first layer are the record's; the typed
    cells at the messages m are the cells of Mm; NormWords;
  the entries at the mask entries' names are the mask at the slots' numbers (MaskTies, two more);
  sizes; that the statement's token point reads the words drawn; the two clauses on the lookup's
    point; the five claims that the sumchecks themselves leave are worth 0 at yL.
Limits. All of these are premises. The part merge is not spoken of. Implications in given worlds: no
draw, nothing on soundness or on hiding.


-/
import Johnson.Road.K4.SevenParts
import Johnson.Road.K4.WeightsOfLed
import Johnson.Road.K4.SlotTiesAt
import Johnson.Road.K4.LedWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Cb Cb.Sub Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd lF lFe zpos)
open OnBytes.Model (Fork Psc Level Tsc powers ledNS ledNP ledNO)
open OnBytes.Model.Layer (Pub Own Heard HPlan2 nEndT)
open OnBytes.Tie.Pv.Lay (OutIs eDefault eRange)
open OnBytes.Desc.First.P1 (gl NzT Adds7 TailM TailR tapeEps drawnOf)

variable [scl : Scl] {M X0 : Type} (Pf : FullPar Cb.Gl.E M X0)

/-- The letter zt: the token part of the lookup's point in the batched sumcheck's state. -/
noncomputable def ztS (e : (tailF Pf).s7.Nx) : ℕ → Cb.Gl.E :=
  zpos Pf.D ((tailF Pf).b4 e).2.st.z

variable {R : TailR} (W' : TailM (tailF Pf) R) (b B sG : ℕ)
  (Rr : (tailF Pf).s7.Nx → Rest3 Cb.Gl.E (Pf.J ⊕ J3 (roomFor Pf.D B sG))) (m : M)
  {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Model.Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}

/-- **Seven parts of the ledger at a hearing.** -/
theorem seven_of_led (hF : OnBytes.PscRun.Sized F) (hg : (g == 0) = false)
    (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT (tailF Pf) (ksOf P hp) (t0.drop 1)) (a : Adds7 (tailF Pf)) (x : Pf.XT)
    (e : (tailF Pf).s7.Nx) (he : e = (k4Tail W' P hp t0 nz a).z7 x) {p1 p4 p5 p6 : Psc}
    (O1 : OutIs gl (k4Tail W' P hp t0 nz a).d1 p1)
    (O2 : OutIs gl (k4Tail W' P hp t0 nz a).d2 H1.tV.p)
    (O3 : OutIs gl (k4Tail W' P hp t0 nz a).d3 tT.p)
    (O4 : OutIs gl (k4Tail W' P hp t0 nz a).d4 p4) (O5 : OutIs gl (k4Tail W' P hp t0 nz a).d5 p5)
    (O6 : OutIs gl (k4Tail W' P hp t0 nz a).d6 p6) (Nm : NumTies Pf W' P.y.LamM)
    (hc : (k4Tail W' P hp t0 nz a).d4.Claim ((k4Tail W' P hp t0 nz a).y4 x))
    (k1 : (tailF Pf).s1.L.S.k = P.rd.muV) (k2 : (tailF Pf).s2.L.S.k = P.y.h.lt)
    (k3 : (tailF Pf).s3.L.S.k = P.y.h.lt) (k4 : kS Pf.D = hp.lamS)
    (k5 : (tailF Pf).s5.L.S.k = P.rd.muH) (k6 : (tailF Pf).s6.L.S.k = P.rd.muH2)
    (e1 : Pf.nr.sq.R.L.e = eDefault (tailF Pf).s1.L.S.k) (n5 : 9 ≤ (tailF Pf).s5.L.S.k)
    (e5 : Pf.fp.gp.e = eRange (tailF Pf).s5.L.S.k n5) (n6 : 9 ≤ (tailF Pf).s6.L.S.k)
    (e6 : Pf.fp.rt.L.e = eRange (tailF Pf).s6.L.S.k n6)
    (X : Rows.Pub34 Cb.Gl.E) (Xρ : X.ρ = gl) (XH : X.H = o.H) (Xv : X.p.v = o.v)
    (Xrs : X.c.rs = o.K.rs) (Xhd : X.hd = o.hd) (Xhd2 : X.hd2 = o.hd2) (Xlam : X.lam = hp.lamS)
    (XsA : X.sA0 = o.K.sA0) (XsB : X.sB0 = o.K.sB0)
    (Xom : X.om = powers (tapeEps ((ksOf P hp).tc4 (t0.drop 1))) 2)
    (Xsh : ((Array.range (nEndT P.y)).mapM fun i => G2.shown (X.tT.sEnd + i)) = some X.p.shownT)
    (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) {F1 F2 : Fork} (l1 : Fo.Later G F1)
    (l2 : Fo.Later G F2) (Mm : Mats Cb.Gl.E) (hR1 : X.ReadsTrue (F1.worldOf gl mask entry) Mm)
    (hR2 : X.ReadsTrue (F2.worldOf gl mask entry) Mm)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (hyv : o.v.y = P.y)
    (hls : P.y.ls = sG) (hD : X.D = Pf.D) (htb : X.tb = Pf.ip.tb)
    (hL0 : X.c.v.g * X.c.v.y.Lam = Pf.ip.L0) (Nw : NormWords o.v Pf.D)
    (Z : P.y.Lam = 2 ^ Pf.D.lL ∧ P.y.h.f / P.y.S2 = 2 ^ (lF Pf.D - P.y.ls) ∧
      P.y.LamM = 2 ^ (Pf.D.lL - 1) ∧ P.y.h.fe / P.y.S2 = 2 ^ (lFe Pf.D - P.y.ls) ∧
      P.y.xb.nl = 5 ∧ ledNP P.y.h.xl * P.y.NI = 7 * Pf.D.nNu ∧ P.y.NI = Pf.D.nNu)
    (hB : P.y.h.d / P.y.S2 = B) (h0 : 0 < Pf.D.nNu)
    (nl : lDd Pf.D = b + sG) (nd : Pf.D.d = B * 2 ^ sG) (nB : B ≤ 2 ^ b)
    (g1 : 1 ≤ Pf.D.lL) (gs1 : sG ≤ lF Pf.D) (gs2 : sG ≤ lFe Pf.D) (gfe : Pf.D.fe = 2 ^ lFe Pf.D)
    (hNS : ledNS P.y.h.xl = 9) (hNP : ledNP P.y.h.xl = 7) (hNO : ledNO P.y.h.xl = 4)
    (hEnd : Pf.D.nNu + Pf.D.ne + Pf.D.ne * Pf.D.nx ≤ nEndT P.y)
    (hNN : P.y.NN * P.y.Lam = Pf.D.nNu) (hLM : P.y.LamM = Pf.D.ne) (hNE : P.y.h.NE = Pf.D.nx)
    (hsB : o.K.sB0 = o.K.sA0 + (1 + (1 + P.y.LamM))) (hla : P.y.h.la = sG + Pf.D.lT)
    (s1 : P.rd.muV = Pf.D.lL + 1 + b + P.y.h.la)
    (s5 : P.rd.muH = Pf.D.lL + lF Pf.D - sG + P.y.h.la)
    (s6 : P.rd.muH2 = Pf.D.lL - 1 + lFe Pf.D - sG + P.y.h.la) (s2 : P.y.h.lt = Pf.D.lT)
    (w1 : P.rd.lNI + P.y.lPd - P.y.ls = Pf.D.lL + 1 + b) (wP : P.y.Pd = 2 ^ b * P.y.S2)
    (wS : 0 < P.y.S2) (wn : Pf.D.nNu ≤ 2 ^ (Pf.D.lL + 1))
    (w5 : P.y.h.ll + P.y.lPf - P.y.ls = Pf.D.lL + lF Pf.D - sG)
    (w5s : P.y.Pf / P.y.S2 = 2 ^ (lF Pf.D - sG))
    (w6 : P.y.h.ll - 1 + P.y.lfe - P.y.ls = Pf.D.lL - 1 + lFe Pf.D - sG)
    (hcells : cellsOf Pf.D (cellsAt X.p.v.y Mm) = Pf.rd (Pf.msg m))
    (hx : ∀ i : Fin Pf.D.lT, x.2 i = gl.val ((drawnOf t0).getD i.val zeroE))
    (hz0 : ((tailF Pf).b4 e).2.st.z = zOf gl o.H.fo.zx o.H.fo.zy)
    (hz3 : Pf.ip.zP ((tailF Pf).b4 e).2.st .QK = zOf gl o.H.fo.zx o.H.fo.zy)
    (Mk : MaskTies mask o Pf.D (namesAt Pf.nr (readsAt (lateOf (roomFor Pf.D B sG)) Sum.inl))
      (namesT Pf.tp (readsT (lateOf (roomFor Pf.D B sG)) fun x => Sum.inr (Sum.inl x)))
      (gNamesAt Pf.fp (gReadsAt (lateOf (roomFor Pf.D B sG)) fun x => Sum.inr (Sum.inr x)))
      (yL Pf (lateOf (roomFor Pf.D B sG)) (fmOf Pf (ztS Pf) b sG sG) e m))
    (mA : Pf.msg m (Pf.ip.cI (.inl (.inl ()))) = mask o.K.sA0)
    (mB : Pf.msg m (Pf.ip.cI (.inr (.inl ()))) = mask o.K.sB0)
    {rows : Bool} {F0 : Fork} {fs : Array OnBytes.Model.Aff}
    (h : Desc.First.K4.formsFrontWith rows P g o F0 = some (fs, F1))
    (hz : ∀ f ∈ fs.toList, f.value gl (F1.worldOf gl mask entry) = 0)
    (hS : ∀ f ∈ X.sideClaims, f.value gl (F2.worldOf gl mask entry) = 0)
    (u1 : Blocks.Form.val (yL Pf (lateOf (roomFor Pf.D B sG)) (fmOf Pf (ztS Pf) b sG sG) e m)
      (u1At Pf.nr ((tailF Pf).b1 e).2) = 0)
    (u2 : Blocks.Form.val (yL Pf (lateOf (roomFor Pf.D B sG)) (fmOf Pf (ztS Pf) b sG sG) e m)
      (u2At Pf.nr ((tailF Pf).b2 e).2) = 0)
    (u5 : Blocks.Form.val (yL Pf (lateOf (roomFor Pf.D B sG)) (fmOf Pf (ztS Pf) b sG sG) e m)
      (prodU Pf.fp.gp ((tailF Pf).b5 e).2) = 0)
    (u6 : Blocks.Form.val (yL Pf (lateOf (roomFor Pf.D B sG)) (fmOf Pf (ztS Pf) b sG sG) e m)
      (prodU Pf.fp.rt.L ((tailF Pf).b6 e).2) = 0)
    (u4 : Blocks.Form.val (yL Pf (lateOf (roomFor Pf.D B sG)) (fmOf Pf (ztS Pf) b sG sG) e m)
      (upForm (J₂ := J3 (roomFor Pf.D B sG)) (Cb.Sub.formU Pf.ip.inn.toSum.T.par
        (fun _ b _ _ => PEmpty.elim b) ((tailF Pf).b4 e).2)) = 0) :
    Ledger.Holds (clF Pf (lateOf (roomFor Pf.D B sG)) Sum.inl (fun x => Sum.inr (Sum.inl x))
        (fun x => Sum.inr (Sum.inr x)) Rr sG (ztS Pf) b B e).sq
        (yL Pf (lateOf (roomFor Pf.D B sG)) (fmOf Pf (ztS Pf) b sG sG) e m) ∧
      Ledger.Holds (clF Pf (lateOf (roomFor Pf.D B sG)) Sum.inl (fun x => Sum.inr (Sum.inl x))
        (fun x => Sum.inr (Sum.inr x)) Rr sG (ztS Pf) b B e).bat
        (yL Pf (lateOf (roomFor Pf.D B sG)) (fmOf Pf (ztS Pf) b sG sG) e m) ∧
      Ledger.Holds (clF Pf (lateOf (roomFor Pf.D B sG)) Sum.inl (fun x => Sum.inr (Sum.inl x))
        (fun x => Sum.inr (Sum.inr x)) Rr sG (ztS Pf) b B e).led
        (yL Pf (lateOf (roomFor Pf.D B sG)) (fmOf Pf (ztS Pf) b sG sG) e m) ∧
      Ledger.Holds (clF Pf (lateOf (roomFor Pf.D B sG)) Sum.inl (fun x => Sum.inr (Sum.inl x))
        (fun x => Sum.inr (Sum.inr x)) Rr sG (ztS Pf) b B e).terms
        (yL Pf (lateOf (roomFor Pf.D B sG)) (fmOf Pf (ztS Pf) b sG sG) e m) ∧
      Ledger.Holds (clF Pf (lateOf (roomFor Pf.D B sG)) Sum.inl (fun x => Sum.inr (Sum.inl x))
        (fun x => Sum.inr (Sum.inr x)) Rr sG (ztS Pf) b B e).gated
        (yL Pf (lateOf (roomFor Pf.D B sG)) (fmOf Pf (ztS Pf) b sG sG) e m) ∧
      Ledger.Holds (clF Pf (lateOf (roomFor Pf.D B sG)) Sum.inl (fun x => Sum.inr (Sum.inl x))
        (fun x => Sum.inr (Sum.inr x)) Rr sG (ztS Pf) b B e).hot
        (yL Pf (lateOf (roomFor Pf.D B sG)) (fmOf Pf (ztS Pf) b sG sG) e m) ∧
      Ledger.Holds (clF Pf (lateOf (roomFor Pf.D B sG)) Sum.inl (fun x => Sum.inr (Sum.inl x))
        (fun x => Sum.inr (Sum.inr x)) Rr sG (ztS Pf) b B e).stack
        (yL Pf (lateOf (roomFor Pf.D B sG)) (fmOf Pf (ztS Pf) b sG sG) e m) := by
  subst he
  -- the record's second token sumcheck is the hearing's, but for a mark on its record
  have hT : X.tT = { tT with p := { tT.p with rowMade := true } } := by
    have q := X.hT
    rw [XH, Ld.kTT] at q
    exact (Option.some.inj q).symm
  have hrt : X.c.rt = tT.r := by rw [X.hcrt, hT]
  have hse : X.tT.sEnd = tT.sEnd := by rw [hT]
  have hvy : X.p.v.y = P.y := by rw [Xv, hyv]
  rw [hse] at Xsh
  have St := stack_of_led Pf W' Ld nz a x O4 Nm hsB mask entry l2 mA mB
  have Sl : SlotTies gl (F1.worldOf gl mask entry) P o Pf.D _ _ _ _ _ _ b B sG _ :=
    slotTies_of
      (slots_of_led Pf W' hF hg Ld nz a x O1 O2 O3 O5 O6 Nm Z.2.2.2.2.2.2 hNS hNP hNO hEnd mask
        entry l1 (ztS Pf ((k4Tail W' P hp t0 nz a).z7 x)) _ _ _ _ Mk)
      (sqW_of_led Pf W' Ld nz a x O1 k1 e1 _ w1 (by omega) wP wS wn nB)
      (sqG_of_led Pf W' Ld nz a x hNS _) (batW_of_led Pf W' Ld nz a x hNP Z.2.2.2.2.2.2 _)
      (eps_of_words gl_numerals Nw) (two_of_words gl_numerals Nw _)
      (g5W_of_led Pf W' Ld nz a x O5 k5 n5 e5 w5 (by omega) w5s gs1)
      (g6W_of_led Pf W' Ld nz a x O6 k6 n6 e6 w6 (by omega) gs2)
  refine seven_parts Pf b B sG Rr (ztS Pf) _ m X (F1.worldOf gl mask entry)
    (F2.worldOf gl mask entry) Mm hR1 hR2 hscl Xv.symm Ld.eHd2 (Xhd2.trans Ld.eHd2) hyv
    (by rw [hyv]; exact hls) hD htb hL0 Z hB h0 nl nd nB g1 gs1 gs2 gfe hcells ?_
    (by rw [Xρ]; exact Sl) h (by rw [Xρ]; exact hz) (by rw [Xρ]; exact hS) ?_
    (Xlam.trans k4.symm) ?_ (by rw [XsA]; exact St.1) (by rw [XsB]; exact St.2) u1 u2 u5 u6 u4
  · rw [Xρ, XH, Xhd, hrt, hvy]
    exact points_of_led Pf W' Ld nz a x O1 O2 O3 O5 O6 k1 k2 k3 k5 k6 e1 n5 e5 n6 e6 hla s1 s5 s6
      s2 hx _ _ (zt_at Pf W' (ksOf P hp) (t0.drop 1) nz a x hz0)
  · rw [Xρ, XH, hrt, hvy]
    exact stackTies_of_led Pf W' Ld nz a x hc O3 k3 Nm.n3 hNN hLM hNE hEnd Xsh Xom hz0 hz3
  · rw [Xρ, Xrs]
    exact hpt_of_led Pf W' Ld nz a x O4 k4

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.seven_of_led
