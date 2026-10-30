-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SevenOfLedFirst.lean: THE FIRST GROUP's twin of SevenOfLed.lean and of the record
in SevenSizes.lean: eight parts of the library's ledger of the first group's layers' sub-proof hold
at a hearing of K4's text: eight_parts_first (Johnson/Road/K4/SevenPartsFirst.lean) with its ties of
letters paid from the record LedG of the hearing's calls and ledgers
(Johnson/Road/K4/OwnLedgersG.lean).

  `ztSF`: the letter zt: the token part of the lookup's point in the batched sumcheck's state.
  `eight_of_ledF`: the parts sq, bat, led, terms, gated, hot, stack and emb of clFirst hold of yLF,
    at the last statement e that the chain's data off K4's tape make.
  `SevenSizesF`: the public sizes that it asks, in one record.
Paid here, premises of eight_parts_first no more: PointTies (points_of_ledF), SlotTies (slotTies_of
over slots_of_ledF, with sqW_of_ledF, sqG_of_ledF, batW_of_ledF, eps_of_words, two_of_words,
g5W_of_ledF, g6W_of_ledF), StackTies (stackTies_of_ledF), the batched sumcheck's number of rounds,
end point (hpt_of_ledF) and two hidden end values (stack_of_ledF).
What is still asked, and by nothing here shown: what seven_of_led's head lists, at the first
group's letters (LedG for Led7; NumTiesF; the statement's token point Pf.ofp.fs.pvF x), and the
embedding's claim worth 0 at yLF. LedG stands in every group; the typed chain here is the first
group's.
Limits. All of these are premises. The part merge is not spoken of. Made from the later groups'
files by a program that turns the letters, the proof's last step by hand; compiled. Implications in
given worlds: no draw, nothing on soundness or on hiding.


-/
import Johnson.Road.K4.SevenPartsFirst
import Johnson.Road.K4.OfLedFirst
import Johnson.Road.K4.SlotTiesAtFirst
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
open OnBytes.Desc.First.P1 (gl NzT Adds7 TailM TailR tailT tapeEps drawnOf)
open OnBytes.Desc.First.K4 (k0)

/-- The public sizes that eight_of_ledF asks. -/
structure SevenSizesF [scl : Scl] {M X0 : Type} (Pf : FullFPar Cb.Gl.E M X0) (P : Pub)
    (hp : HPlan2) (b B sG : ℕ) : Prop where
  /-- the typed stages have as many variables' rounds as the plan says -/
  k1 : (tailW Pf).s1.L.S.k = P.rd.muV
  k2 : (tailW Pf).s2.L.S.k = P.y.h.lt
  k3 : (tailW Pf).s3.L.S.k = P.y.h.lt
  k4 : kS Pf.D = hp.lamS
  k5 : (tailW Pf).s5.L.S.k = P.rd.muH
  k6 : (tailW Pf).s6.L.S.k = P.rd.muH2
  /-- the three typed permutations are the programs' orders -/
  e1 : Pf.ofp.nr.sq.R.L.e = eDefault (tailW Pf).s1.L.S.k
  n5 : 9 ≤ (tailW Pf).s5.L.S.k
  e5 : Pf.fp.gp.e = eRange (tailW Pf).s5.L.S.k n5
  n6 : 9 ≤ (tailW Pf).s6.L.S.k
  e6 : Pf.fp.rt.L.e = eRange (tailW Pf).s6.L.S.k n6
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

variable [scl : Scl] {M X0 : Type} (Pf : FullFPar Cb.Gl.E M X0)

/-- The letter zt: the token part of the lookup's point in the batched sumcheck's state. -/
noncomputable def ztSF (e : (tailW Pf).s7.Nx) : ℕ → Cb.Gl.E :=
  zpos Pf.D ((tailW Pf).b4 e).2.st.z

variable {R : TailR} (W' : TailM (tailW Pf) R) (b B sG : ℕ)
  (Rr : (tailW Pf).s7.Nx → Rest2 Cb.Gl.E (Pf.J ⊕ J4 (roomF Pf.D B sG Pf.nb))) (m : M)
  {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Model.Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}

/-- **Eight parts of the first group's ledger at a hearing.** -/
theorem eight_of_ledF (hF : OnBytes.PscRun.Sized F)
    (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 (tailW Pf)) (x : Pf.ofp.fs.X3)
    (e : (tailW Pf).s7.Nx) (he : e = (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x) {p1 p4 p5 p6
        : Psc}
    (O1 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d1 p1)
    (O2 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d2 H1.tV.p)
    (O3 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d3 tT.p)
    (O4 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d4 p4) (O5 : OutIs gl (tailT W'
        (ksOf P hp) (t0.drop (k0 g)) nz a).d5 p5)
    (O6 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d6 p6) (Nm : NumTiesF Pf W'
        P.y.LamM)
    (hc : (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d4.Claim ((tailT W' (ksOf P hp) (t0.drop (k0
        g)) nz a).y4 x))
    (k1 : (tailW Pf).s1.L.S.k = P.rd.muV) (k2 : (tailW Pf).s2.L.S.k = P.y.h.lt)
    (k3 : (tailW Pf).s3.L.S.k = P.y.h.lt) (k4 : kS Pf.D = hp.lamS)
    (k5 : (tailW Pf).s5.L.S.k = P.rd.muH) (k6 : (tailW Pf).s6.L.S.k = P.rd.muH2)
    (e1 : Pf.ofp.nr.sq.R.L.e = eDefault (tailW Pf).s1.L.S.k) (n5 : 9 ≤ (tailW Pf).s5.L.S.k)
    (e5 : Pf.fp.gp.e = eRange (tailW Pf).s5.L.S.k n5) (n6 : 9 ≤ (tailW Pf).s6.L.S.k)
    (e6 : Pf.fp.rt.L.e = eRange (tailW Pf).s6.L.S.k n6)
    (X : Rows.Pub34 Cb.Gl.E) (Xρ : X.ρ = gl) (XH : X.H = o.H) (Xv : X.p.v = o.v)
    (Xrs : X.c.rs = o.K.rs) (Xhd : X.hd = o.hd) (Xhd2 : X.hd2 = o.hd2) (Xlam : X.lam = hp.lamS)
    (XsA : X.sA0 = o.K.sA0) (XsB : X.sB0 = o.K.sB0)
    (Xom : X.om = powers (tapeEps ((ksOf P hp).tc4 (t0.drop (k0 g)))) 2)
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
    (hx : ∀ i : Fin Pf.D.lT, Pf.ofp.fs.pvF x i = gl.val ((drawnOf t0).getD i.val zeroE))
    (hz0 : ((tailW Pf).b4 e).2.st.z = zOf gl o.H.fo.zx o.H.fo.zy)
    (hz3 : Pf.ip.zP ((tailW Pf).b4 e).2.st .QK = zOf gl o.H.fo.zx o.H.fo.zy)
    (Mk : MaskTies mask o Pf.D (namesAt Pf.ofp.nr (readsAt (lateF (roomF Pf.D B sG Pf.nb)) fun x =>
        Sum.inl (Sum.inl x)))
      (namesT Pf.tp (readsT (lateF (roomF Pf.D B sG Pf.nb)) fun x => Sum.inl (Sum.inr (Sum.inl x))))
      (gNamesAt Pf.fp (gReadsAt (lateF (roomF Pf.D B sG Pf.nb)) fun x => Sum.inl (Sum.inr (Sum.inr
          x))))
      (yLF Pf (ztSF Pf) b B sG e m))
    (mA : Pf.msg m (Pf.ip.cI (.inl (.inl ()))) = mask o.K.sA0)
    (mB : Pf.msg m (Pf.ip.cI (.inr (.inl ()))) = mask o.K.sB0)
    {rows : Bool} {F0 : Fork} {fs : Array OnBytes.Model.Aff}
    (h : Desc.First.K4.formsFrontWith rows P g o F0 = some (fs, F1))
    (hz : ∀ f ∈ fs.toList, f.value gl (F1.worldOf gl mask entry) = 0)
    (hS : ∀ f ∈ X.sideClaims, f.value gl (F2.worldOf gl mask entry) = 0)
    (u1 : Blocks.Form.val (yLF Pf (ztSF Pf) b B sG e m)
      (u1At Pf.ofp.nr ((tailW Pf).b1 e).2) = 0)
    (u2 : Blocks.Form.val (yLF Pf (ztSF Pf) b B sG e m)
      (u2At Pf.ofp.nr ((tailW Pf).b2 e).2) = 0)
    (u5 : Blocks.Form.val (yLF Pf (ztSF Pf) b B sG e m)
      (prodU Pf.fp.gp ((tailW Pf).b5 e).2) = 0)
    (u6 : Blocks.Form.val (yLF Pf (ztSF Pf) b B sG e m)
      (prodU Pf.fp.rt.L ((tailW Pf).b6 e).2) = 0)
    (u4 : Blocks.Form.val (yLF Pf (ztSF Pf) b B sG e m)
      (upForm (J₂ := J4 (roomF Pf.D B sG Pf.nb)) (Cb.Sub.formU Pf.ip.inn.toSum.T.par
        (fun _ b _ _ => PEmpty.elim b) ((tailW Pf).b4 e).2)) = 0)
    (uE : Blocks.Form.val (yLF Pf (ztSF Pf) b B sG e m) (embClaim (lateF (roomF Pf.D B sG Pf.nb))
        Sum.inr
      (((tailW Pf).y7 e).1.2 (0 : Fin 1)) Pf.mkE Pf.nb Pf.gB (stF Pf e).pb) = 0) :
    Ledger.Holds (clFirst Pf (lateF (roomF Pf.D B sG Pf.nb)) (fun x => Sum.inl (Sum.inl x))
        (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr Rr
        (ztSF Pf) b B sG e).sq (yLF Pf (ztSF Pf) b B sG e m) ∧
      Ledger.Holds (clFirst Pf (lateF (roomF Pf.D B sG Pf.nb)) (fun x => Sum.inl (Sum.inl x))
        (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr Rr
        (ztSF Pf) b B sG e).bat (yLF Pf (ztSF Pf) b B sG e m) ∧
      Ledger.Holds (clFirst Pf (lateF (roomF Pf.D B sG Pf.nb)) (fun x => Sum.inl (Sum.inl x))
        (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr Rr
        (ztSF Pf) b B sG e).led (yLF Pf (ztSF Pf) b B sG e m) ∧
      Ledger.Holds (clFirst Pf (lateF (roomF Pf.D B sG Pf.nb)) (fun x => Sum.inl (Sum.inl x))
        (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr Rr
        (ztSF Pf) b B sG e).terms (yLF Pf (ztSF Pf) b B sG e m) ∧
      Ledger.Holds (clFirst Pf (lateF (roomF Pf.D B sG Pf.nb)) (fun x => Sum.inl (Sum.inl x))
        (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr Rr
        (ztSF Pf) b B sG e).gated (yLF Pf (ztSF Pf) b B sG e m) ∧
      Ledger.Holds (clFirst Pf (lateF (roomF Pf.D B sG Pf.nb)) (fun x => Sum.inl (Sum.inl x))
        (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr Rr
        (ztSF Pf) b B sG e).hot (yLF Pf (ztSF Pf) b B sG e m) ∧
      Ledger.Holds (clFirst Pf (lateF (roomF Pf.D B sG Pf.nb)) (fun x => Sum.inl (Sum.inl x))
        (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr Rr
        (ztSF Pf) b B sG e).stack (yLF Pf (ztSF Pf) b B sG e m) ∧
      Ledger.Holds (clFirst Pf (lateF (roomF Pf.D B sG Pf.nb)) (fun x => Sum.inl (Sum.inl x))
        (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr Rr
        (ztSF Pf) b B sG e).emb (yLF Pf (ztSF Pf) b B sG e m) := by
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
  have St := stack_of_ledF Pf W' Ld nz a x O4 Nm hsB mask entry l2 mA mB
  have Sl : SlotTies gl (F1.worldOf gl mask entry) P o Pf.D _ _ _ _ _ _ b B sG _ :=
    slotTies_of
      (slots_of_ledF Pf W' hF Ld nz a x O1 O2 O3 O5 O6 Nm Z.2.2.2.2.2.2 hNS hNP hNO hEnd mask
        entry l1 (ztSF Pf ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)) _ _ _ _ Mk)
      (sqW_of_ledF Pf W' Ld nz a x O1 k1 e1 _ w1 (by omega) wP wS wn nB)
      (sqG_of_ledF Pf W' Ld nz a x hNS _) (batW_of_ledF Pf W' Ld nz a x hNP Z.2.2.2.2.2.2 _)
      (eps_of_words gl_numerals Nw) (two_of_words gl_numerals Nw _)
      (g5W_of_ledF Pf W' Ld nz a x O5 k5 n5 e5 w5 (by omega) w5s gs1)
      (g6W_of_ledF Pf W' Ld nz a x O6 k6 n6 e6 w6 (by omega) gs2)
  refine eight_parts_first Pf (ztSF Pf) b B sG Rr _ m X (F1.worldOf gl mask entry)
    (F2.worldOf gl mask entry) Mm hR1 hR2 hscl Xv.symm Ld.eHd2 (Xhd2.trans Ld.eHd2) hyv
    (by rw [hyv]; exact hls) hD htb hL0 Z hB h0 nl nd nB g1 gs1 gs2 gfe hcells ?_
    (by rw [Xρ]; exact Sl) h (by rw [Xρ]; exact hz) (by rw [Xρ]; exact hS) ?_
    (Xlam.trans k4.symm) ?_ (by rw [XsA]; exact St.1) (by rw [XsB]; exact St.2) u1 u2 u5 u6 u4 uE
  · rw [Xρ, XH, Xhd, hrt, hvy]
    exact points_of_ledF Pf W' Ld nz a x O1 O2 O3 O5 O6 k1 k2 k3 k5 k6 e1 n5 e5 n6 e6 hla s1 s5 s6
      s2 hx _ _ (zt_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x hz0)
  · rw [Xρ, XH, hrt, hvy]
    exact stackTies_of_ledF Pf W' Ld nz a x hc O3 k3 Nm.n3 hNN hLM hNE hEnd Xsh Xom hz0 hz3
  · rw [Xρ, Xrs]
    exact hpt_of_ledF Pf W' Ld nz a x O4 k4

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.eight_of_ledF
