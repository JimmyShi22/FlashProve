-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SlotsOfLedFirst.lean: THE FIRST GROUP's twin of Johnson/Road/K4/SlotsOfLed.lean: the
clauses of Johnson/Road/K4/SlotsAtFirst.lean, joined at a hearing of the text of the layers' own
rounds: in the world of every ledger later than the hearing's, the clauses "the hidden value under a
slot is what was shown less the challenge times the mask entry" hold in the hearing's own letters,
at the names and records of the first group's chain.

The calls and ledgers are the record LedG (Johnson/Road/K4/OwnLedgersG.lean), which holds in
every group: its tapes are cuts of the tape behind the points in front, t0.drop (k0 g). So nothing
here asks which group it is: the chain's letters are the first group's. The records MaskTies and
SlotsHeld of SlotsOfLed.lean are general and are imported. The statements and proofs are that
file's, turned to these letters by a program and compiled; each name bears an F or a G.

Main names:
  `k4TailG`: the chain's data, read off the tape behind the points in front.
  `NumTiesF`: the numberings of the end values, at the first group's chain.
  `tcP_dropG`, `prods_sentG`: what the products' round sent, in the two ways of writing, in every
    group.
  `slotP_ofF`, `slots_of_ledF`, `stack_of_ledF`.
Limits. As SlotsOfLed.lean's: LedG, OutIs at the stages named, NumTiesF, MaskTies, five equations on
public numbers and that the ledger is later are premises. One direction: from a return. Nothing on
soundness.


-/
import Johnson.Road.K4.SlotsAtFirst
import Johnson.Road.K4.SlotsOfLed
import Johnson.Road.K4.OwnLedgersG

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
open OnBytes.Tie.Pv.Lay.Eng (TailH)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 TailM TailR tailT sentOf level_world tscIn_heard
  array_getD_toList)
open OnBytes.Desc.First.K4 (k0 prodsOf norms_world0 drop_drop')
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim)

/-- The chain's data, read off the tape behind the points in front, in whichever group. -/
abbrev k4TailG {M X : Type} {T : LayTail Cb.Gl.E M X} {R : TailR} (W : TailM T R) (P : Pub)
    (hp : HPlan2) (g : ℕ) (t0 : Tape) (nz : NzT T (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 T) :
    TailH gl T :=
  tailT W (ksOf P hp) (t0.drop (k0 g)) nz a

/-- The numberings of the end values: of the three product layers (false 0, true 1), of the token
sumcheck of the row products (field k of norm ν: 4 ν + k), of the sumcheck of the terms (numA), and
of the two form parts of the batched sumcheck. LamM: the routed layers. -/
structure NumTiesF [scl : Scl] {M X : Type} (Pf : FullFPar Cb.Gl.E M X) {R : TailR}
    (W' : TailM (tailW Pf) R) (LamM : ℕ) : Prop where
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

/-! ## The products' round -/

/-- The tape from the products' round on, counted from the hearing's tape. -/
theorem tcP_dropG (P : Pub) (hp : HPlan2) (n0 : ℕ) (t0 : Tape) :
    (ksOf P hp).tcP (t0.drop n0) = t0.drop (n0 + P.rd.muV + 6) := by
  have T0 : (t0.drop n0).drop 1 = t0.drop (n0 + 1) := drop_drop' n0 1 t0
  have T1 : (ksOf P hp).tc1 (t0.drop n0) = t0.drop (n0 + 2) := by
    unfold Ks.tc1
    rw [T0, drop_drop']
  unfold Ks.tcP
  rw [T1, drop_drop', drop_drop']
  congr 1
  show n0 + 2 + (P.rd.muV + 3) + 1 = _
  omega

/-- What the products' round sent, in the two ways of writing, in every group. -/
theorem prods_sentG (P : Pub) (hp : HPlan2) (g : ℕ) (t0 : Tape) (n : ℕ) :
    (prodsOf P g t0).getD n zeroE =
      (sentOf ((ksOf P hp).tcP (t0.drop (k0 g)))).getD n zeroE := by
  rw [array_getD_toList, tcP_dropG]
  rfl

section Join

variable [scl : Scl] {M X : Type} (Pf : FullFPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailW Pf) R)

/-- LedDict.slotP, from what a world holds under the products' slots. -/
theorem slotP_ofF (k : Ks) (t : Tape) (nz : NzT (tailW Pf) k t) (a : Adds7 (tailW Pf))
    (x : Pf.ofp.fs.X3) {W : World Cb.Gl.E} {mask : ℕ → Cb.Gl.E} {first : ℕ}
    (hw : ∀ n, n < 7 * Pf.D.nNu →
      W.slot (first + n) = gl.val ((sentOf (k.tcP t)).getD n zeroE) - mask (first + n))
    (zt : ℕ → Cb.Gl.E) {J₂ : Type} (U : NormsReads J₂) (y : Pf.J ⊕ J₂ → Cb.Gl.E)
    (hy : ∀ n, n < 7 * Pf.D.nNu → y ((namesAt Pf.ofp.nr U).mP n) = mask (first + n)) :
    ∀ n, n < 7 * Pf.D.nNu → W.slot (first + n) =
      (eAtF Pf.ofp Pf.wfPart ((tailT W' k t nz a).z7 x) zt).shP n -
        y ((namesAt Pf.ofp.nr U).mP n) := by
  intro n hn
  have hn' : n < Pf.D.nNu * 7 := by omega
  rw [eAt_shPF, dif_pos hn', hy n hn, hw n hn]
  rfl

variable {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own} {F G : Fork}
  {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork}
  {u5 : Tape}

/-- **The eleven clauses of SlotsHeld, where the hearing has returned.** -/
theorem slots_of_ledF (hF : OnBytes.PscRun.Sized F)
    (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 (tailW Pf)) (x : Pf.ofp.fs.X3)
    {p1 p5 p6 : Psc} (O1 : OutIs gl (k4TailG W' P hp g t0 nz a).d1 p1)
    (O2 : OutIs gl (k4TailG W' P hp g t0 nz a).d2 H1.tV.p)
    (O3 : OutIs gl (k4TailG W' P hp g t0 nz a).d3 tT.p)
    (O5 : OutIs gl (k4TailG W' P hp g t0 nz a).d5 p5)
    (O6 : OutIs gl (k4TailG W' P hp g t0 nz a).d6 p6)
    (Nm : NumTiesF Pf W' P.y.LamM) (hNI : P.y.NI = Pf.D.nNu) (hNS : ledNS P.y.h.xl = 9)
    (hNP : ledNP P.y.h.xl = 7) (hNO : ledNO P.y.h.xl = 4)
    (hEnd : Pf.D.nNu + Pf.D.ne + Pf.D.ne * Pf.D.nx ≤ nEndT P.y) (mask : ℕ → Cb.Gl.E)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) {Hl : Fork} (lH : Fo.Later G Hl) (zt : ℕ → Cb.Gl.E) {J₂ : Type}
    (UN : NormsReads J₂) (UT : TermsReads J₂) (UG : GatedReads J₂) (y : Pf.J ⊕ J₂ → Cb.Gl.E)
    (Mk : MaskTies mask o Pf.D (namesAt Pf.ofp.nr UN) (namesT Pf.tp UT) (gNamesAt Pf.fp UG) y) :
    SlotsHeld (Hl.worldOf gl mask entry) o Pf.D (namesAt Pf.ofp.nr UN)
      (eAtF Pf.ofp Pf.wfPart ((k4TailG W' P hp g t0 nz a).z7 x) zt) (namesT Pf.tp UT)
      (termsEAt Pf.tp ((tailW Pf).b3 ((k4TailG W' P hp g t0 nz a).z7 x)).2) (gNamesAt Pf.fp UG)
      (gatedEAt Pf.fp ((tailW Pf).b5 ((k4TailG W' P hp g t0 nz a).z7 x)).2
        ((tailW Pf).b6 ((k4TailG W' P hp g t0 nz a).z7 x)).2) y := by
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
        (sqL_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x mask entry O1 Ld.s4 c1
          (Ld.g7.trans lH) Nm.n1f zt UN y (Mk.mL.trans (congrArg mask eL)))
      sqR := (congrArg (Hl.worldOf gl mask entry).slot eR).trans
        (sqR_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x mask entry O1 Ld.s4 c1
          (Ld.g7.trans lH) Nm.n1t zt UN y (Mk.mR.trans (congrArg mask eR)))
      batCl := (congrArg (Hl.worldOf gl mask entry).slot eCl).trans
        (batCl_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x mask entry Ld.s8 c2
          (Ld.g1.trans lH) zt UN y (Mk.mCl.trans (congrArg mask (eCl.trans hCl))))
      slot2 := fun n hn =>
        (congrArg (fun s => (Hl.worldOf gl mask entry).slot (s + n)) eEnd).trans
          (slot2_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x mask entry O2 Ld.s8 c2
            (Ld.g1.trans lH) (le_of_eq (by rw [hNO, hNI])) Nm.n2 zt UN y
            (fun n hn => (Mk.m2 n hn).trans (congrArg (fun s => mask (s + n)) eEnd)) n hn)
      slotW := fun n hn =>
        (congrArg (fun s => (Hl.worldOf gl mask entry).slot (s + n)) eW).trans
          (slotW_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x mask entry hF' hrW hvW
            (le_of_eq (by rw [hszW, hNS, hNI])) l4 zt UN y
            (fun n hn => (Mk.mW n hn).trans (congrArg (fun s => mask (s + n)) eW)) n hn)
      slotP := fun n hn =>
        (congrArg (fun s => (Hl.worldOf gl mask entry).slot (s + n)) Ld.kSPv).trans
          (slotP_ofF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x (mask := mask)
            (fun n hn => (wP n (by rw [hNP, hNI]; exact hn)).trans
              (congrArg (fun e => gl.val e - mask (H1.sPv + n)) (prods_sentG P hp g t0 n)))
            zt UN y
            (fun n hn => (Mk.mP n hn).trans (congrArg (fun s => mask (s + n)) Ld.kSPv)) n hn)
      slotT := fun tT' hT' n hn =>
        have e0 := Option.some.inj (hT'.symm.trans Ld.kTT)
        have e1 := congrArg Tsc.sEnd e0
        have eT : tT'.sEnd = tT.sEnd := e1
        (congrArg (fun s => (Hl.worldOf gl mask entry).slot (s + n)) eT).trans
          (slotT_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x mask entry O3 Ld.s1 Ld.c3
            (Ld.g1'.trans lH) hEnd Nm.n3 UT y
            (fun n hn => (Mk.mT tT' hT' n hn).trans (congrArg (fun s => mask (s + n)) eT)) n hn)
      g5L := g5L_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x mask entry O5 Ld.s3 c5
        (Ld.g3'.trans lH) Nm.n5f UG y Mk.m5L
      g5R := g5R_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x mask entry O5 Ld.s3 c5
        (Ld.g3'.trans lH) Nm.n5t UG y Mk.m5R
      g6L := fun o2 h2 =>
        have e2 : o2 = hd2 := Option.some.inj (h2.symm.trans Ld.eHd2)
        (congrArg (fun L : Level => (Hl.worldOf gl mask entry).slot L.sL) e2).trans
          (g6L_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x mask entry O6 Ld.s3' Ld.c6
            (Ld.g4.trans lH) Nm.n6f UG y
            ((Mk.m6L o2 h2).trans (congrArg (fun L : Level => mask L.sL) e2)))
      g6R := fun o2 h2 =>
        have e2 : o2 = hd2 := Option.some.inj (h2.symm.trans Ld.eHd2)
        (congrArg (fun L : Level => (Hl.worldOf gl mask entry).slot L.sR) e2).trans
          (g6R_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x mask entry O6 Ld.s3' Ld.c6
            (Ld.g4.trans lH) Nm.n6t UG y
            ((Mk.m6R o2 h2).trans (congrArg (fun L : Level => mask L.sR) e2))) }

/-- **The premises hA and hB of stack_port, where the hearing has returned.** μA, μB: what the
messages hold at the names of the two mask entries. hsB: where the second side's slot lies. -/
theorem stack_of_ledF (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 (tailW Pf)) (x : Pf.ofp.fs.X3)
    {p4 : Psc} (O4 : OutIs gl (k4TailG W' P hp g t0 nz a).d4 p4) (Nm : NumTiesF Pf W' P.y.LamM)
    (hsB : o.K.sB0 = o.K.sA0 + (1 + (1 + P.y.LamM))) (mask : ℕ → Cb.Gl.E)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) {Hl : Fork} (lH : Fo.Later G Hl) {μA μB : Cb.Gl.E}
    (hA : μA = mask o.K.sA0) (hB : μB = mask o.K.sB0) :
    (Hl.worldOf gl mask entry).slot o.K.sA0 =
        ((tailW Pf).b4 ((k4TailG W' P hp g t0 nz a).z7 x)).2.vals (Sum.inl (Sum.inl ())) -
          Pf.ip.inn.Kp.outB Pf.ip.inn.Mk ((tailW Pf).b4 ((k4TailG W' P hp g t0 nz a).z7 x)).2 * μA ∧
      (Hl.worldOf gl mask entry).slot o.K.sB0 =
        ((tailW Pf).b4 ((k4TailG W' P hp g t0 nz a).z7 x)).2.vals (Sum.inr (Sum.inl ())) -
          Pf.ip.inn.Kp.outB Pf.ip.inn.Mk ((tailW Pf).b4 ((k4TailG W' P hp g t0 nz a).z7 x)).2 *
            μB :=
  ⟨stack_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x mask entry O4 Ld.s2 Ld.c4 (Ld.g3.trans lH)
      (Sum.inl (Sum.inl ())) (e := 0) (by omega) Nm.n4A hA,
    (congrArg (Hl.worldOf gl mask entry).slot hsB).trans
      (stack_atF Pf W' (ksOf P hp) (t0.drop (k0 g)) nz a x mask entry O4 Ld.s2 Ld.c4
        (Ld.g3.trans lH) (Sum.inr (Sum.inl ())) (e := 1 + (1 + P.y.LamM)) (by omega) Nm.n4B
        (hB.trans (congrArg mask hsB)))⟩

end Join

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tcP_dropG
#print axioms OnBytes.Road.K4.prods_sentG
#print axioms OnBytes.Road.K4.slotP_ofF
#print axioms OnBytes.Road.K4.slots_of_ledF
#print axioms OnBytes.Road.K4.stack_of_ledF
