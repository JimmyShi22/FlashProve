-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SlotsOfLed.lean: where the hearing of the layers' own rounds has returned in a group
that is not the first: in the world of every ledger later than the hearing's, the clauses "the
hidden value under a slot is what was shown less the challenge times the mask entry" hold in the
hearing's own letters, at the library's names and records.

Johnson/Road/K4/SlotsAt.lean has each clause at one call on one tape.
Johnson/Road/K4/OwnLedgers.lean (Led7) has the hearing's calls, each on its named tape, with what is
known of the ledgers between them and of the fields that the hearing's record keeps. Here the two
are joined.

Main names:
  `NumTies`: the numberings of the end values of six sumchecks.
  `MaskTies`: the entries at the names of the mask entries are the mask at the slots' numbers.
  `SlotsHeld`: eleven such clauses, in the letters of FrontDict, LedDict and TermsDict.
  `tcP_drop`, `prods_sent`: the tape from the products' round on; what that round sent.
  `slotP_of`: LedDict.slotP from what a world holds under the products' slots.
  `slots_of_led`: SlotsHeld. `stack_of_led`: the premises hA and hB of stack_port
    (Johnson/Road/K4/StackPort.lean).
Limits. PREMISES, NONE SHOWN HERE: Led7 (own_led7 gives it where the hearing returns); OutIs of the
six stages (k4_outs6, Johnson/Road/K4/OwnJoint.lean); NumTies; MaskTies; five equations between the
program's public numbers and the library's sizes; for hB, where the second side's slot lies. A group
that is not the first. One direction: from a return. Nothing on soundness.


-/
import Johnson.Road.K4.SlotsAt
import Johnson.Road.K4.OwnLedgers
import Johnson.Road.K4.OwnJoint
import Johnson.Road.K4.NormsWorld

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Reading World Fork Psc Level Tsc Aff ledNS ledNP ledNO)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard nEndT)
open OnBytes.Tie.Pv.Lay (OutIs)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 TailM TailR sentOf level_world tscIn_heard
  array_getD_toList)
open OnBytes.Desc.First.K4 (k0 prodsOf norms_world0 drop_drop')
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim)

/-! ## Three records -/

/-- The numberings of the end values: of the three product layers (false 0, true 1), of the token
sumcheck of the row products (field k of norm ν: 4 ν + k), of the sumcheck of the terms (numA), and
of the two form parts of the batched sumcheck. LamM: the routed layers. -/
structure NumTies [scl : Scl] {M X : Type} (Pf : FullPar Cb.Gl.E M X) {R : TailR}
    (W' : TailM (tailF Pf) R) (LamM : ℕ) : Prop where
  n1f : W'.w1.num false = 0
  n1t : W'.w1.num true = 1
  n2 : ∀ q : Fin Pf.D.nNu × Fin 4, W'.w2.num q = (finProdFinEquiv q : ℕ)
  n3 : ∀ q : ShA Pf.D, W'.w3.num q = numA Pf.D q
  n4A : W'.w4.num (Sum.inl (Sum.inl ()) : IA Pf.D ⊕ IB Pf.D) = 0
  n4B : W'.w4.num (Sum.inr (Sum.inl ()) : IA Pf.D ⊕ IB Pf.D) = 1 + (1 + LamM)
  n5f : W'.w5.num false = 0
  n5t : W'.w5.num true = 1
  n6f : W'.w6.num false = 0
  n6t : W'.w6.num true = 1

/-- The entries at the names of the mask entries are the mask at the slots' numbers. -/
structure MaskTies {K J : Type} (mask : ℕ → K) (o : Own) (D : Dim) (NN : NormsNames J)
    (NT : TermsNames J) (NG : GatedNames J) (y : J → K) : Prop where
  mL : y NN.mL = mask o.H.wpl.sL
  mR : y NN.mR = mask o.H.wpl.sR
  mCl : y NN.mCl = mask o.H.tV.sCl
  m2 : ∀ n, n < 4 * D.nNu → y (NN.m2 n) = mask (o.H.tV.sEnd + n)
  mW : ∀ n, n < 9 * D.nNu → y (NN.mW n) = mask (o.H.sW + n)
  mP : ∀ n, n < 7 * D.nNu → y (NN.mP n) = mask (o.H.sPv + n)
  mT : ∀ tT, o.H.tT = some tT → ∀ n, n < D.nNu + D.ne + D.ne * D.nx →
    y (NT.mT n) = mask (tT.sEnd + n)
  m5L : y NG.mL5 = mask o.hd.sL
  m5R : y NG.mR5 = mask o.hd.sR
  m6L : ∀ o2, o.hd2 = some o2 → y NG.mL6 = mask o2.sL
  m6R : ∀ o2, o.hd2 = some o2 → y NG.mR6 = mask o2.sR

/-- The hidden values under the slots of the layers' own rounds. -/
structure SlotsHeld {K J : Type} [Field K] (W : World K) (o : Own) (D : Dim) (NN : NormsNames J)
    (eN : NormsE K) (NT : TermsNames J) (eT : TermsE K) (NG : GatedNames J) (eG : GatedE K)
    (y : J → K) : Prop where
  sqL : W.slot o.H.wpl.sL = eN.shL - eN.β1 * y NN.mL
  sqR : W.slot o.H.wpl.sR = eN.shR - eN.β1 * y NN.mR
  batCl : W.slot o.H.tV.sCl = eN.shCl - y NN.mCl
  slot2 : ∀ x, x < 4 * D.nNu → W.slot (o.H.tV.sEnd + x) = eN.sh2 x - eN.β2 * y (NN.m2 x)
  slotW : ∀ x, x < 9 * D.nNu → W.slot (o.H.sW + x) = eN.shW x - y (NN.mW x)
  slotP : ∀ x, x < 7 * D.nNu → W.slot (o.H.sPv + x) = eN.shP x - y (NN.mP x)
  slotT : ∀ tT, o.H.tT = some tT → ∀ x, x < D.nNu + D.ne + D.ne * D.nx →
    W.slot (tT.sEnd + x) = eT.sh x - eT.β * y (NT.mT x)
  g5L : W.slot o.hd.sL = eG.shL5 - eG.β5 * y NG.mL5
  g5R : W.slot o.hd.sR = eG.shR5 - eG.β5 * y NG.mR5
  g6L : ∀ o2, o.hd2 = some o2 → W.slot o2.sL = eG.shL6 - eG.β6 * y NG.mL6
  g6R : ∀ o2, o.hd2 = some o2 → W.slot o2.sR = eG.shR6 - eG.β6 * y NG.mR6

/-! ## The products' round -/

/-- The tape from the products' round on, counted from the hearing's tape. -/
theorem tcP_drop (P : Pub) (hp : HPlan2) (t0 : Tape) :
    (ksOf P hp).tcP (t0.drop 1) = t0.drop (1 + P.rd.muV + 6) := by
  have T0 : (t0.drop 1).drop 1 = t0.drop (1 + 1) := drop_drop' 1 1 t0
  have T1 : (ksOf P hp).tc1 (t0.drop 1) = t0.drop (1 + 2) := by
    unfold Ks.tc1
    rw [T0, drop_drop']
  unfold Ks.tcP
  rw [T1, drop_drop', drop_drop']
  congr 1
  show 1 + 2 + (P.rd.muV + 3) + 1 = _
  omega

/-- What the products' round sent, in the two ways of writing, in a group that is not the first. -/
theorem prods_sent (P : Pub) (hp : HPlan2) {g : ℕ} (hg : (g == 0) = false) (t0 : Tape) (n : ℕ) :
    (prodsOf P g t0).getD n zeroE = (sentOf ((ksOf P hp).tcP (t0.drop 1))).getD n zeroE := by
  have hk0 : k0 g = 1 := by
    unfold k0
    rw [hg]
    rfl
  rw [array_getD_toList, tcP_drop]
  show (sentOf (t0.drop (k0 g + P.rd.muV + 6))).getD n zeroE = _
  rw [hk0]

section Join

variable [scl : Scl] {M X : Type} (Pf : FullPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailF Pf) R)

/-- LedDict.slotP, from what a world holds under the products' slots. -/
theorem slotP_of (k : Ks) (t : Tape) (nz : NzT (tailF Pf) k t) (a : Adds7 (tailF Pf)) (x : Pf.XT)
    {W : World Cb.Gl.E} {mask : ℕ → Cb.Gl.E} {first : ℕ}
    (hw : ∀ n, n < 7 * Pf.D.nNu →
      W.slot (first + n) = gl.val ((sentOf (k.tcP t)).getD n zeroE) - mask (first + n))
    (zt : ℕ → Cb.Gl.E) {J₂ : Type} (U : NormsReads J₂) (y : Pf.J ⊕ J₂ → Cb.Gl.E)
    (hy : ∀ n, n < 7 * Pf.D.nNu → y ((namesAt Pf.nr U).mP n) = mask (first + n)) :
    ∀ n, n < 7 * Pf.D.nNu → W.slot (first + n) =
      (eAt Pf.toOwnPar Pf.wPart ((OnBytes.Desc.First.P1.tailT W' k t nz a).z7 x) zt).shP n -
        y ((namesAt Pf.nr U).mP n) := by
  intro n hn
  have hn' : n < Pf.D.nNu * 7 := by omega
  rw [eAt_shP, dif_pos hn', hy n hn, hw n hn]
  rfl

variable {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own} {F G : Fork}
  {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}

/-- **The eleven clauses of SlotsHeld, where the hearing has returned.** -/
theorem slots_of_led (hF : OnBytes.PscRun.Sized F) (hg : (g == 0) = false)
    (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT (tailF Pf) (ksOf P hp) (t0.drop 1)) (a : Adds7 (tailF Pf)) (x : Pf.XT)
    {p1 p5 p6 : Psc} (O1 : OutIs gl (k4Tail W' P hp t0 nz a).d1 p1)
    (O2 : OutIs gl (k4Tail W' P hp t0 nz a).d2 H1.tV.p)
    (O3 : OutIs gl (k4Tail W' P hp t0 nz a).d3 tT.p)
    (O5 : OutIs gl (k4Tail W' P hp t0 nz a).d5 p5) (O6 : OutIs gl (k4Tail W' P hp t0 nz a).d6 p6)
    (Nm : NumTies Pf W' P.y.LamM) (hNI : P.y.NI = Pf.D.nNu) (hNS : ledNS P.y.h.xl = 9)
    (hNP : ledNP P.y.h.xl = 7) (hNO : ledNO P.y.h.xl = 4)
    (hEnd : Pf.D.nNu + Pf.D.ne + Pf.D.ne * Pf.D.nx ≤ nEndT P.y) (mask : ℕ → Cb.Gl.E)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) {Hl : Fork} (lH : Fo.Later G Hl) (zt : ℕ → Cb.Gl.E) {J₂ : Type}
    (UN : NormsReads J₂) (UT : TermsReads J₂) (UG : GatedReads J₂) (y : Pf.J ⊕ J₂ → Cb.Gl.E)
    (Mk : MaskTies mask o Pf.D (namesAt Pf.nr UN) (namesT Pf.tp UT) (gNamesAt Pf.fp UG) y) :
    SlotsHeld (Hl.worldOf gl mask entry) o Pf.D (namesAt Pf.nr UN)
      (eAt Pf.toOwnPar Pf.wPart ((k4Tail W' P hp t0 nz a).z7 x) zt) (namesT Pf.tp UT)
      (termsEAt Pf.tp ((tailF Pf).b3 ((k4Tail W' P hp t0 nz a).z7 x)).2) (gNamesAt Pf.fp UG)
      (gatedEAt Pf.fp ((tailF Pf).b5 ((k4Tail W' P hp t0 nz a).z7 x)).2
        ((tailF Pf).b6 ((k4Tail W' P hp t0 nz a).z7 x)).2) y := by
  obtain ⟨v1, c1⟩ := Ld.c1
  obtain ⟨v2, c2⟩ := Ld.c2
  obtain ⟨v5, c5⟩ := Ld.c5
  obtain ⟨vW, hvW, hszW, hrW⟩ := Ld.runW
  obtain ⟨u1, hN, _⟩ := Ld.nt
  have eL : o.H.wpl.sL = H1.wpl.sL := congrArg Level.sL Ld.kWpl
  have eR : o.H.wpl.sR = H1.wpl.sR := congrArg Level.sR Ld.kWpl
  have eCl : o.H.tV.sCl = H1.tV.sCl := congrArg Tsc.sCl Ld.kTV
  have eEnd : o.H.tV.sEnd = H1.tV.sEnd := congrArg Tsc.sEnd Ld.kTV
  have eW : o.H.sW = F.next := Ld.kSW.trans Ld.sW
  have hCl : H1.tV.sCl = F8.next := (tscIn_heard c2).2.2.2.2.2.2.2.2.2.2.1
  have hF' : OnBytes.PscRun.Sized
      ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork) := hF
  have l4 : Fo.Later F4 Hl := ((level_world gl mask entry Ld.s4 c1).1.trans Ld.g7).trans lH
  have wP := (norms_world0 gl mask entry hF hN (Ld.g1.trans lH)).2.1
  exact
    { sqL := (congrArg (Hl.worldOf gl mask entry).slot eL).trans
        (sqL_at Pf W' (ksOf P hp) (t0.drop 1) nz a x mask entry O1 Ld.s4 c1 (Ld.g7.trans lH) Nm.n1f
          zt UN y (Mk.mL.trans (congrArg mask eL)))
      sqR := (congrArg (Hl.worldOf gl mask entry).slot eR).trans
        (sqR_at Pf W' (ksOf P hp) (t0.drop 1) nz a x mask entry O1 Ld.s4 c1 (Ld.g7.trans lH) Nm.n1t
          zt UN y (Mk.mR.trans (congrArg mask eR)))
      batCl := (congrArg (Hl.worldOf gl mask entry).slot eCl).trans
        (batCl_at Pf W' (ksOf P hp) (t0.drop 1) nz a x mask entry Ld.s8 c2 (Ld.g1.trans lH) zt UN y
          (Mk.mCl.trans (congrArg mask (eCl.trans hCl))))
      slot2 := fun n hn =>
        (congrArg (fun s => (Hl.worldOf gl mask entry).slot (s + n)) eEnd).trans
          (slot2_at Pf W' (ksOf P hp) (t0.drop 1) nz a x mask entry O2 Ld.s8 c2 (Ld.g1.trans lH)
            (le_of_eq (by rw [hNO, hNI])) Nm.n2 zt UN y
            (fun n hn => (Mk.m2 n hn).trans (congrArg (fun s => mask (s + n)) eEnd)) n hn)
      slotW := fun n hn =>
        (congrArg (fun s => (Hl.worldOf gl mask entry).slot (s + n)) eW).trans
          (slotW_at Pf W' (ksOf P hp) (t0.drop 1) nz a x mask entry hF' hrW hvW
            (le_of_eq (by rw [hszW, hNS, hNI])) l4 zt UN y
            (fun n hn => (Mk.mW n hn).trans (congrArg (fun s => mask (s + n)) eW)) n hn)
      slotP := fun n hn =>
        (congrArg (fun s => (Hl.worldOf gl mask entry).slot (s + n)) Ld.kSPv).trans
          (slotP_of Pf W' (ksOf P hp) (t0.drop 1) nz a x (mask := mask)
            (fun n hn => (wP n (by rw [hNP, hNI]; exact hn)).trans
              (congrArg (fun e => gl.val e - mask (H1.sPv + n)) (prods_sent P hp hg t0 n)))
            zt UN y
            (fun n hn => (Mk.mP n hn).trans (congrArg (fun s => mask (s + n)) Ld.kSPv)) n hn)
      slotT := fun tT' hT' n hn =>
        have e0 := Option.some.inj (hT'.symm.trans Ld.kTT)
        have e1 := congrArg Tsc.sEnd e0
        have eT : tT'.sEnd = tT.sEnd := e1
        (congrArg (fun s => (Hl.worldOf gl mask entry).slot (s + n)) eT).trans
          (slotT_at Pf W' (ksOf P hp) (t0.drop 1) nz a x mask entry O3 Ld.s1 Ld.c3
            (Ld.g1'.trans lH) hEnd Nm.n3 UT y
            (fun n hn => (Mk.mT tT' hT' n hn).trans (congrArg (fun s => mask (s + n)) eT)) n hn)
      g5L := g5L_at Pf W' (ksOf P hp) (t0.drop 1) nz a x mask entry O5 Ld.s3 c5 (Ld.g3'.trans lH)
        Nm.n5f UG y Mk.m5L
      g5R := g5R_at Pf W' (ksOf P hp) (t0.drop 1) nz a x mask entry O5 Ld.s3 c5 (Ld.g3'.trans lH)
        Nm.n5t UG y Mk.m5R
      g6L := fun o2 h2 =>
        have e2 : o2 = hd2 := Option.some.inj (h2.symm.trans Ld.eHd2)
        (congrArg (fun L : Level => (Hl.worldOf gl mask entry).slot L.sL) e2).trans
          (g6L_at Pf W' (ksOf P hp) (t0.drop 1) nz a x mask entry O6 Ld.s3' Ld.c6 (Ld.g4.trans lH)
            Nm.n6f UG y ((Mk.m6L o2 h2).trans (congrArg (fun L : Level => mask L.sL) e2)))
      g6R := fun o2 h2 =>
        have e2 : o2 = hd2 := Option.some.inj (h2.symm.trans Ld.eHd2)
        (congrArg (fun L : Level => (Hl.worldOf gl mask entry).slot L.sR) e2).trans
          (g6R_at Pf W' (ksOf P hp) (t0.drop 1) nz a x mask entry O6 Ld.s3' Ld.c6 (Ld.g4.trans lH)
            Nm.n6t UG y ((Mk.m6R o2 h2).trans (congrArg (fun L : Level => mask L.sR) e2))) }

/-- **The premises hA and hB of stack_port, where the hearing has returned.** μA, μB: what the
messages hold at the names of the two mask entries. hsB: where the second side's slot lies. -/
theorem stack_of_led (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT (tailF Pf) (ksOf P hp) (t0.drop 1)) (a : Adds7 (tailF Pf)) (x : Pf.XT) {p4 : Psc}
    (O4 : OutIs gl (k4Tail W' P hp t0 nz a).d4 p4) (Nm : NumTies Pf W' P.y.LamM)
    (hsB : o.K.sB0 = o.K.sA0 + (1 + (1 + P.y.LamM))) (mask : ℕ → Cb.Gl.E)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) {Hl : Fork} (lH : Fo.Later G Hl) {μA μB : Cb.Gl.E}
    (hA : μA = mask o.K.sA0) (hB : μB = mask o.K.sB0) :
    (Hl.worldOf gl mask entry).slot o.K.sA0 =
        ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2.vals (Sum.inl (Sum.inl ())) -
          Pf.ip.inn.Kp.outB Pf.ip.inn.Mk ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2 * μA ∧
      (Hl.worldOf gl mask entry).slot o.K.sB0 =
        ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2.vals (Sum.inr (Sum.inl ())) -
          Pf.ip.inn.Kp.outB Pf.ip.inn.Mk ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2 * μB :=
  ⟨stack_at Pf W' (ksOf P hp) (t0.drop 1) nz a x mask entry O4 Ld.s2 Ld.c4 (Ld.g3.trans lH)
      (Sum.inl (Sum.inl ())) (e := 0) (by omega) Nm.n4A hA,
    (congrArg (Hl.worldOf gl mask entry).slot hsB).trans
      (stack_at Pf W' (ksOf P hp) (t0.drop 1) nz a x mask entry O4 Ld.s2 Ld.c4 (Ld.g3.trans lH)
        (Sum.inr (Sum.inl ())) (e := 1 + (1 + P.y.LamM)) (by omega) Nm.n4B
        (hB.trans (congrArg mask hsB)))⟩

end Join

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tcP_drop
#print axioms OnBytes.Road.K4.prods_sent
#print axioms OnBytes.Road.K4.slotP_of
#print axioms OnBytes.Road.K4.slots_of_led
#print axioms OnBytes.Road.K4.stack_of_led
