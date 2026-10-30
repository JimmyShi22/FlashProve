-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SevenSizes.lean: the public sizes that seven_of_led
(Johnson/Road/K4/SevenOfLed.lean) asks, gathered in one record, and the theorem once more, taking
the record.

  `SevenSizes`: equations and bounds between the typed parameters' sizes (Pf.D, the typed stages'
    numbers of variables' rounds, the three typed permutations) and the verifier's public numbers
    (the layout P.y, the reads' numbers P.rd, the plan hp), with the three letters b (the bits of
    the stream's blocks), B (their number) and sG (the bits of a feature in its block).
  `seven_of_sizes`: seven_of_led from the record.
Limits. The record is a premise: that a layout which the verifier admits meets it is shown nowhere
here. All other premises as in seven_of_led. Nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.SevenOfLed

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

/-- The public sizes that seven_of_led asks. -/
structure SevenSizes [scl : Scl] {M X0 : Type} (Pf : FullPar Cb.Gl.E M X0) (P : Pub)
    (hp : HPlan2) (b B sG : ℕ) : Prop where
  /-- the typed stages have as many variables' rounds as the plan says -/
  k1 : (tailF Pf).s1.L.S.k = P.rd.muV
  k2 : (tailF Pf).s2.L.S.k = P.y.h.lt
  k3 : (tailF Pf).s3.L.S.k = P.y.h.lt
  k4 : kS Pf.D = hp.lamS
  k5 : (tailF Pf).s5.L.S.k = P.rd.muH
  k6 : (tailF Pf).s6.L.S.k = P.rd.muH2
  /-- the three typed permutations are the programs' orders -/
  e1 : Pf.nr.sq.R.L.e = eDefault (tailF Pf).s1.L.S.k
  n5 : 9 ≤ (tailF Pf).s5.L.S.k
  e5 : Pf.fp.gp.e = eRange (tailF Pf).s5.L.S.k n5
  n6 : 9 ≤ (tailF Pf).s6.L.S.k
  e6 : Pf.fp.rt.L.e = eRange (tailF Pf).s6.L.S.k n6
  /-- the bits of a feature in its block -/
  hls : P.y.ls = sG
  /-- FrontDict's seven sizes -/
  Z : P.y.Lam = 2 ^ Pf.D.lL ∧ P.y.h.f / P.y.S2 = 2 ^ (lF Pf.D - P.y.ls) ∧
    P.y.LamM = 2 ^ (Pf.D.lL - 1) ∧ P.y.h.fe / P.y.S2 = 2 ^ (lFe Pf.D - P.y.ls) ∧
    P.y.xb.nl = 5 ∧ ledNP P.y.h.xl * P.y.NI = 7 * Pf.D.nNu ∧ P.y.NI = Pf.D.nNu
  hB : P.y.h.d / P.y.S2 = B
  h0 : 0 < Pf.D.nNu
  /-- NormsOk's and GatedOk's clauses on sizes -/
  nl : lDd Pf.D = b + sG
  nd : Pf.D.d = B * 2 ^ sG
  nB : B ≤ 2 ^ b
  g1 : 1 ≤ Pf.D.lL
  gs1 : sG ≤ lF Pf.D
  gs2 : sG ≤ lFe Pf.D
  gfe : Pf.D.fe = 2 ^ lFe Pf.D
  /-- the numbers of a norm's sums, products and shown values; of the terms' end values -/
  hNS : ledNS P.y.h.xl = 9
  hNP : ledNP P.y.h.xl = 7
  hNO : ledNO P.y.h.xl = 4
  hEnd : Pf.D.nNu + Pf.D.ne + Pf.D.ne * Pf.D.nx ≤ nEndT P.y
  hNN : P.y.NN * P.y.Lam = Pf.D.nNu
  hLM : P.y.LamM = Pf.D.ne
  hNE : P.y.h.NE = Pf.D.nx
  /-- the rows of a block, and the three product layers' numbers of variables -/
  hla : P.y.h.la = sG + Pf.D.lT
  s1 : P.rd.muV = Pf.D.lL + 1 + b + P.y.h.la
  s5 : P.rd.muH = Pf.D.lL + lF Pf.D - sG + P.y.h.la
  s6 : P.rd.muH2 = Pf.D.lL - 1 + lFe Pf.D - sG + P.y.h.la
  s2 : P.y.h.lt = Pf.D.lT
  /-- the tables of weights -/
  w1 : P.rd.lNI + P.y.lPd - P.y.ls = Pf.D.lL + 1 + b
  wP : P.y.Pd = 2 ^ b * P.y.S2
  wS : 0 < P.y.S2
  wn : Pf.D.nNu ≤ 2 ^ (Pf.D.lL + 1)
  w5 : P.y.h.ll + P.y.lPf - P.y.ls = Pf.D.lL + lF Pf.D - sG
  w5s : P.y.Pf / P.y.S2 = 2 ^ (lF Pf.D - sG)
  w6 : P.y.h.ll - 1 + P.y.lfe - P.y.ls = Pf.D.lL - 1 + lFe Pf.D - sG

variable [scl : Scl] {M X0 : Type} (Pf : FullPar Cb.Gl.E M X0)
  {R : TailR} (W' : TailM (tailF Pf) R) (b B sG : ℕ)
  (Rr : (tailF Pf).s7.Nx → Rest3 Cb.Gl.E (Pf.J ⊕ J3 (roomFor Pf.D B sG))) (m : M)
  {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Model.Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}

/-- **seven_of_led, from the record of sizes.** -/
theorem seven_of_sizes (Sz : SevenSizes Pf P hp b B sG) (hF : OnBytes.PscRun.Sized F)
    (hg : (g == 0) = false)
    (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT (tailF Pf) (ksOf P hp) (t0.drop 1)) (a : Adds7 (tailF Pf)) (x : Pf.XT)
    (e : (tailF Pf).s7.Nx) (he : e = (k4Tail W' P hp t0 nz a).z7 x) {p1 p4 p5 p6 : Psc}
    (O1 : OutIs gl (k4Tail W' P hp t0 nz a).d1 p1)
    (O2 : OutIs gl (k4Tail W' P hp t0 nz a).d2 H1.tV.p)
    (O3 : OutIs gl (k4Tail W' P hp t0 nz a).d3 tT.p)
    (O4 : OutIs gl (k4Tail W' P hp t0 nz a).d4 p4) (O5 : OutIs gl (k4Tail W' P hp t0 nz a).d5 p5)
    (O6 : OutIs gl (k4Tail W' P hp t0 nz a).d6 p6) (Nm : NumTies Pf W' P.y.LamM)
    (hc : (k4Tail W' P hp t0 nz a).d4.Claim ((k4Tail W' P hp t0 nz a).y4 x))
    (X : Rows.Pub34 Cb.Gl.E) (Xρ : X.ρ = gl) (XH : X.H = o.H) (Xv : X.p.v = o.v)
    (Xrs : X.c.rs = o.K.rs) (Xhd : X.hd = o.hd) (Xhd2 : X.hd2 = o.hd2) (Xlam : X.lam = hp.lamS)
    (XsA : X.sA0 = o.K.sA0) (XsB : X.sB0 = o.K.sB0)
    (Xom : X.om = powers (tapeEps ((ksOf P hp).tc4 (t0.drop 1))) 2)
    (Xsh : ((Array.range (nEndT P.y)).mapM fun i => G2.shown (X.tT.sEnd + i)) = some X.p.shownT)
    (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) {F1 F2 : Fork} (l1 : Fo.Later G F1)
    (l2 : Fo.Later G F2) (Mm : Mats Cb.Gl.E) (hR1 : X.ReadsTrue (F1.worldOf gl mask entry) Mm)
    (hR2 : X.ReadsTrue (F2.worldOf gl mask entry) Mm)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (hyv : o.v.y = P.y)
    (hD : X.D = Pf.D) (htb : X.tb = Pf.ip.tb)
    (hL0 : X.c.v.g * X.c.v.y.Lam = Pf.ip.L0) (Nw : NormWords o.v Pf.D)
    (hsB : o.K.sB0 = o.K.sA0 + (1 + (1 + P.y.LamM)))
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
        (yL Pf (lateOf (roomFor Pf.D B sG)) (fmOf Pf (ztS Pf) b sG sG) e m) :=
  seven_of_led Pf W' b B sG Rr m hF hg Ld nz a x e he O1 O2 O3 O4 O5 O6 Nm hc Sz.k1 Sz.k2 Sz.k3
    Sz.k4 Sz.k5 Sz.k6 Sz.e1 Sz.n5 Sz.e5 Sz.n6 Sz.e6 X Xρ XH Xv Xrs Xhd Xhd2 Xlam XsA XsB Xom Xsh
    mask entry l1 l2 Mm hR1 hR2 hscl hyv Sz.hls hD htb hL0 Nw Sz.Z Sz.hB Sz.h0 Sz.nl Sz.nd Sz.nB
    Sz.g1 Sz.gs1 Sz.gs2 Sz.gfe Sz.hNS Sz.hNP Sz.hNO Sz.hEnd Sz.hNN Sz.hLM Sz.hNE hsB Sz.hla Sz.s1
    Sz.s5 Sz.s6 Sz.s2 Sz.w1 Sz.wP Sz.wS Sz.wn Sz.w5 Sz.w5s Sz.w6 hcells hx hz0 hz3 Mk mA mB h hz
    hS u1 u2 u5 u6 u4

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.seven_of_sizes
