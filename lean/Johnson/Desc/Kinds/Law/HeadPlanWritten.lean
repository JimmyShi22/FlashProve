-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadPlanWritten.lean: AT ALL PUBLIC FILES IN THE GOALS' SCOPE THE SIZES OF
THE OUTPUT HEAD's PLAN ARE WRITTEN NUMBERS: the list of its eight matrices, the length of its vector
of reads, the numbers of the lookup of its smallness test, and the number of scalars that its
sub-protocol sends. Statements and proofs.

How. The plan (OnBytes/Model/HeadPlan.lean: planH2) reads of the head's public numbers and layout
sizes alone, and of the plan of the last group of layers one label, which it stores in its list of
matrices. In scope that label is a number too (Johnson/Road/HeadDict.lean: labH_mats;
Johnson/Goal/Meaning/HidOwner.lean: ix_of_core). So the list of matrices is a written list, and the
routine that shapes the smallness test (OnBytes/Model/Tail.lean: HTailF2.shape) runs on a closed
term: Lean's kernel evaluates it there ("decide +kernel").

  layout_fills     one more opening of Head.layout: nine sizes of the three matrices hf, hd, hr.
  planH2_parts     ONE OPENING of planH2 that keeps the accept of HTailF2.shape, the vector's
                   lengths and the number of scalars.
  matsW            the written list of the eight matrices.
  tailChk_true     the smallness test's shape at matsW: thirteen numbers, by the kernel.
  PlanWritten X    the conclusion.
  plan_in_scope    MAIN.

WHAT IT IS NOT. Facts on public parameters alone. Nothing on soundness. UNDER THE LIBRARY's publicOf
ALONE: ix_of_core and the border's numbers are had from it; at publicOfO o nothing is said here.
LETTERS. Under "there is" in planH2_parts: stream, t1, r, Tp2: each pinned by an equation.

-/
import Johnson.Desc.Kinds.Law.HeadFsWritten
import Johnson.Goal.Meaning.HeadAtFullIs
import Johnson.Goal.Meaning.HidOwner
import Johnson.Goal.Meaning.HidOpen
import Johnson.Road.HeadDict
import Johnson.Desc.K12.Law.Sizes.PublicOAtScope
import OnBytes.Tie.Pv.Lookup.Ends.FoMadeTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open OnBytes.Model (TMat HTailF2 T2Foreign Settings Fork Tail2 roundUp)
open OnBytes.Model.Head (Shape HL Border Owner HPlanH2 matsH planH2)
open OnBytes.Road (ok_of_bind)

/-- **One more opening of the head's layout**: the sizes of hf, hd and hr. -/
theorem layout_fills {h : Shape} {tauFC : Array UInt64} {L : HL}
    (hy : OnBytes.Model.Head.layout h tauFC = .ok L) :
    L.filled = roundUp (4 * h.d + (3 + OnBytes.Model.exc) * roundUp h.V h.S2)
        (h.NHf * (2 ^ h.lmhf / h.T)) ∧
      L.fillD = roundUp (2 * h.d) (2 ^ h.lmhd / h.T) ∧
      L.fillR = roundUp (OnBytes.Model.ledNRH h.XL) (2 ^ h.lmhr / h.T) := by
  unfold OnBytes.Model.Head.layout at hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨L0, h3, hy⟩ := ok_of_bind hy
  obtain ⟨calls, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨fs, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨kb, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  cases hy
  unfold OnBytes.Model.Head.numbers at h3
  obtain ⟨-, -, h3⟩ := ok_of_bind h3
  obtain ⟨-, -, h3⟩ := ok_of_bind h3
  cases h3
  exact ⟨rfl, rfl, rfl⟩

/-- **One opening of the head's plan.** -/
theorem planH2_parts {g : Settings} {h : Shape} {L : HL} {b : Border} {O : Owner} {NGr lkW : ℕ}
    {hp : HPlanH2} (hpl : planH2 g h L b O NGr lkW = .ok hp) :
    ∃ (stream : TMat) (t1 : HTailF2) (r : HTailF2 × Fork × Tail2) (Tp2 : Tail2),
      ({ tau := g.tau, lidb := g.lidb } : HTailF2).shape (matsH h L b (1 + NGr) stream.aId)
        (Array.replicate (matsH h L b (1 + NGr) stream.aId).size none)
        #[{ name := "PXf0", K := b.kxb, a := 2, m := b.mxb, wp := 0 }]
        #[false, false, true, false] g.tau = .ok t1 ∧
      t1.addTrees {} {} #[0, 0, OnBytes.Model.Head.readsLength h L b] #[] (g.hb - g.pow) g.hb =
        .ok r ∧
      OnBytes.Model.Head.ownerHeld O NGr r.1 r.2.1 Tp2 = .ok hp.tl ∧
      hp.nU = #[0, 0, OnBytes.Model.Head.readsLength h L b] ∧
      hp.nMsg = OnBytes.Model.Head.slotsH h L t1 lkW := by
  unfold OnBytes.Model.Head.planH2 at hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨pc, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  cases hs : O.tl.mats[O.iXO]? with
  | none =>
    simp only [hs] at hpl
    have h' : (Except.error "internal-h-owner-TX" : Except String HPlanH2) = .ok hp := hpl
    cases h'
  | some M0 =>
    simp only [hs] at hpl
    obtain ⟨stream, -, hpl⟩ := ok_of_bind (x := (pure M0 : Except String TMat)) hpl
    obtain ⟨t1, h1, hpl⟩ := ok_of_bind hpl
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨r, hr, hpl⟩ := ok_of_bind hpl
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨Tp2, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨t3, h3, hpl⟩ := ok_of_bind hpl
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    have e := (Except.ok.inj hpl).symm
    subst e
    exact ⟨stream, t1, r, Tp2, h1, hr, h3, rfl, rfl⟩

/-- **The written list of the head's eight matrices**: the four parts of hf, hd, hr, the lookup's
planes, and the stream that goes out of the last group of layers. -/
def matsW : Array TMat :=
  #[{ name := "hf0", m := 65536, k := 4816, aId := 3328 },
    { name := "hf1", m := 65536, k := 4816, aId := 3329 },
    { name := "hf2", m := 65536, k := 4816, aId := 3330 },
    { name := "hf3", m := 65536, k := 4816, aId := 3331 },
    { name := "hd", m := 16384, k := 640, aId := 3332 },
    { name := "hr", m := 8192, k := 15, aId := 3333 },
    { name := "bH", m := 32768, k := 384, aId := 3334 },
    { name := "xbL", m := 65536, k := 400, kind := 1, foreign := some 0, ttOff := 0,
      aId := 3079 }]

/-- The smallness test's shape at the written list. -/
def tailW : Except String HTailF2 :=
  ({ tau := 128, lidb := 28 } : HTailF2).shape matsW (Array.replicate 8 none)
    #[{ name := "PXf0", K := 400, a := 2, m := 65536, wp := 0 }] #[false, false, true, false] 128

/-- Thirteen numbers of it, as one test. -/
def tailChk : Bool :=
  match tailW with
  | .ok t => t.f9.dT == 26 && t.f9.kT == 10 && t.f9.NC == 2 && t.f9.cK == 1 && t.f9.rK == 1 &&
      t.f9.NT == 2 && t.z1.call.n == 26 && t.z1.call.k == 10 && t.z2.call.n == 26 &&
      t.z2.call.k == 8 && t.lidb == 28 && OnBytes.Model.Forest.elems t.f9 == 1363 &&
      t.f9.calls.size == 2
  | .error _ => false

set_option maxRecDepth 100000 in
theorem tailChk_true : tailChk = true := by decide +kernel

/-- **The sizes of the head's plan.** -/
structure PlanWritten (X : OnBytes.Model.Verify.Public) : Prop where
  mats : X.H.tl.mats = matsW
  nm : X.H.tl.NM = 8
  funOpen : X.H.tl.funClosed = false
  nU : X.H.nU = #[0, 0, 61680]
  ns : X.H.ns = 3570
  lidb : X.H.tl.lidb = 28
  dT : X.H.tl.f9.dT = 26
  kT : X.H.tl.f9.kT = 10
  NC : X.H.tl.f9.NC = 2
  cK : X.H.tl.f9.cK = 1
  rK : X.H.tl.f9.rK = 1
  NT : X.H.tl.f9.NT = 2
  calls : X.H.tl.f9.calls.size = 2
  elems : OnBytes.Model.Forest.elems X.H.tl.f9 = 1363
  z1 : X.H.tl.z1.call.n = 26 ∧ X.H.tl.z1.call.k = 10
  z2 : X.H.tl.z2.call.n = 26 ∧ X.H.tl.z2.call.k = 8

/-- **AT ALL PUBLIC FILES IN THE GOALS' SCOPE THE SIZES OF THE HEAD's PLAN ARE WRITTEN NUMBERS.** -/
theorem plan_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) : PlanWritten X := by
  have St := VerifiableInference.PlanWritten.publicSteps_of h
  obtain ⟨A0, seen, _, _, _, H0, hpl, eH, _⟩ := St.attention
  have hP := OnBytes.Road.Hd.scan_of_scope hZ hR h
  obtain ⟨_, i7, i8⟩ := Meaning.ix_of_core h (OnBytes.Road.Hd.core_of_scope hZ hR h)
  have hG : X.layers.y.NGr = 12 := (H2K.Sizes.pubFull_of_steps hZ St).groups
  have hb : OnBytes.Model.Verify.borderOf X.layers.y = Cond.bFull := border_in_scope hZ hR h
  have N := numbers_in_scope hZ hR h
  have F := fs_in_scope hZ hR h
  have e : X.hS = OnBytes.Model.Verify.headShape
      (VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef (VerifierAndGoals.freeLinesOf pp)) X.layers.y := by
    rw [St.hS, hP]
  have hF : OnBytes.Road.Hd.FullH X.hS := by
    rw [e]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have Nm := OnBytes.Road.Hd.numH_of_layout hF St.head
  have sS2 : X.hS.S2 = 64 := by rw [e]; rfl
  have slm : X.hS.lmbH = 15 := by rw [e]; rfl
  have gtau : X.P.settings.tau = 128 := by rw [hP]; rfl
  have glid : X.P.settings.lidb = 28 := by rw [hP]; rfl
  have glk : X.P.lkW = 18 := by
    rw [hP]
    show VerifierAndGoals.Lines.frameRef.blockLog = 18
    decide +kernel
  obtain ⟨f1, f2, f3⟩ := layout_fills St.head
  rw [hF.d, hF.V, sS2, hF.NHf, hF.lmhf, Nm.T] at f1
  rw [hF.d, hF.lmhd, Nm.T] at f2
  rw [hF.XL, hF.lmhr, Nm.T] at f3
  have f1' : X.HLy.filled = 1232896 := f1.trans (by decide)
  have f2' : X.HLy.fillD = 10240 := f2.trans (by decide)
  have f3' : X.HLy.fillR = 120 := f3.trans (by decide)
  obtain ⟨stream, t1, r, Tp2, h1, hr, h3, hnU, hmsg⟩ := planH2_parts hpl
  obtain ⟨t2, Fp, Tp⟩ := r
  obtain ⟨s1, s2⟩ := OnBytes.Road.shape_mats h1
  obtain ⟨a1, a2⟩ := OnBytes.Road.addTrees_keeps hr
  obtain ⟨o1, o2⟩ := OnBytes.Road.Hd.ownerHeld_keeps h3
  have hm0 : H0.tl.mats = matsH X.hS X.HLy (OnBytes.Model.Verify.borderOf X.layers.y)
      (1 + X.layers.y.NGr) stream.aId := o1.trans (a1.trans s1)
  -- the label
  have hsid : stream.aId = 3079 := by
    have l1 := OnBytes.Road.Hd.labH_mats St.layers St.plans St.owner hpl hF.NHf
      (n := X.hS.NHf + 3) (by omega)
    rw [hm0, (OnBytes.Road.Hd.matsH_last _ _ _ _ hF.NHf).1, OnBytes.Road.Hd.labH_lent _ hG] at l1
    rw [l1]
    unfold OnBytes.Road.labA
    have i7' : (OnBytes.Model.Layer.matIx X.layers.y).iXO = 7 := i7
    have i8' : (OnBytes.Model.Layer.matIx X.layers.y).iXI = 8 := i8
    rw [i7', i8']
    decide
  have hm : matsH X.hS X.HLy (OnBytes.Model.Verify.borderOf X.layers.y) (1 + X.layers.y.NGr)
      stream.aId = matsW := by
    rw [hsid, hG, hb]
    unfold OnBytes.Model.Head.matsH
    rw [hF.NHf, Nm.m, Nm.k, Nm.mD, Nm.kD, Nm.mR, Nm.kR, slm, F.kb]
    decide
  rw [hm, gtau, glid, hb] at h1
  have h1' : tailW = .ok t1 := h1
  have T := tailChk_true
  unfold tailChk at T
  rw [h1'] at T
  simp only [Bool.and_eq_true, beq_iff_eq] at T
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩ := T
  obtain ⟨k1, k2, k3, k4⟩ := Fo.addTreesF_zkeep (tl := t1) hr
  obtain ⟨q1, q2, q3, q4⟩ := Fo.ownerHeld_zkeep h3
  have ez1 : X.H.tl.z1 = t1.z1 := by rw [eH]; exact q1.trans k1
  have ez2 : X.H.tl.z2 = t1.z2 := by rw [eH]; exact q2.trans k2
  have eli : X.H.tl.lidb = t1.lidb := by rw [eH]; exact q3.trans k3
  have ef9 : X.H.tl.f9 = t1.f9 := by rw [eH]; exact q4.trans k4
  refine ⟨by rw [eH]; exact hm0.trans hm, ?_, ?_, ?_, ?_,
    eli.trans c11, by rw [ef9]; exact c1, by rw [ef9]; exact c2, by rw [ef9]; exact c3,
    by rw [ef9]; exact c4, by rw [ef9]; exact c5, by rw [ef9]; exact c6, by rw [ef9]; exact c13,
    by rw [ef9]; exact c12, by rw [ez1]; exact ⟨c7, c8⟩, by rw [ez2]; exact ⟨c9, c10⟩⟩
  · rw [eH]
    show H0.tl.NM = 8
    rw [o2, a2, s2, hm]
    rfl
  · rw [eH]
    show H0.tl.funClosed = false
    exact Meaning.planH2_open hpl
  · rw [eH]
    show H0.nU = _
    rw [hnU]
    unfold OnBytes.Model.Head.readsLength
    rw [f1', f2', f3', F.kb, Nm.T, hF.la, hb]
    decide
  · rw [eH]
    show H0.nMsg = 3570
    rw [hmsg]
    unfold OnBytes.Model.Head.slotsH OnBytes.Model.HTailF2.smallElems
    rw [F.elems, c12, hF.XL, N.lPd, hF.lt, glk]
    decide

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.plan_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.layout_fills
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.planH2_parts
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.tailChk_true
