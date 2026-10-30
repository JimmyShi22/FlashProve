-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Att/HearCut.lean: the run of the verifier program on an accepted proof file, cut at
the borders of the routines that receive an attention sub-proof's own messages.

A block of the verifier program decides a chain whole. Whoever ties a routine inside it to a typed
block needs the routine's own success, from its own state and context. This file gives it for the
three routines scores, divide and attain of an attention link, from the verdict on the file.

Main names:
  (That the routine of an attention link has run Attention.run, and the step of a link in its place:
    attention_of_link, accepted_at, OnBytes/Tie/Pv/Keeps/KeepsKinds.lean.)
  hear_ran: Attention.hear, taken apart: Forest.pad, scores, divide, attain, each from what the one
    before has left.
  start_sized: behind Seam.start the state is the plan's own with its weights filled and ns empty
    slots (F.fillL.slots ns), its arrays on slots have their length (Sized,
    OnBytes/Tie/Pv/Psc/Run/PscHide.lean), and the context is as it was.
  PadSized: the premise that Forest.pad, where it succeeds, keeps Sized.
  OwnCut: the three successes with the states and contexts between; the first state is Sized.
  run_cut: from a success of Attention.run on a view: the success of Forest.pad and the cut behind
    it.
  accepted_cut: from the verdict: if Proof.check accepts a file and the link at place j of the chain
    is an attention link, then: the record of the whole first chain's run (FileRan); the chain over
    the links before it, from the file's own start; the link's step; the chain over the links behind
    it, to the file's own end (OnBytes/Tie/Pv/Keeps/KeepsChain.lean); and inside the step the
    success of Forest.pad, from the state Y.Fp.fillL.slots A.ns and the context in which the link's
    routine began, and the cut OwnCut behind it; the cut's last context is a view without a mark of
    a failed named test.
  OwnCut's four fields are the four premises of hear_tie (OnBytes/Tie/Pv/Att/HearTie.lean): so the
    stages heard, the records and the typed outputs of that theorem are those of the file's own run.

Limits: one direction: from the verdict. Premises: every link's routine keeps (AllKeep,
OnBytes/Tie/Pv/Keeps/KeepsLinks.lean, which holds of the program's own links); PadSized, which is
proved nowhere here. The contexts hold what is left of the view's rounds (c.ch.cur, c.ch.left); the
cut of the view's list of rounds at these contexts is not written out here.
-/
import OnBytes.Tie.Pv.Keeps.KeepsKinds
import OnBytes.Tie.Pv.Keeps.KeepsChainA2
import OnBytes.Tie.Pv.Att.HearTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.Model.Road OnBytes.Attention OnBytes.L5

/-- Attention.hear, taken apart. -/
theorem hear_ran (P : Attention.Plan) (f : Attention.First) (F G : Fork) (c c' : Ctx)
    (h : Attention.hear P F c = .ok ((f, G), c')) :
    ∃ (F0 : Fork) (c0 : Ctx) (F1 : Fork) (c1 : Ctx) (F2 : Fork) (c2 : Ctx),
      Forest.pad (P.S.calls.map (·.call)) P.fs.pub P.lid F c = .ok ((f.g, F0), c0) ∧
      scores P.S f.g.zk F0 c0 = .ok (((f.planes, f.scores), F1), c1) ∧
      divide P.S f.g.zk F1 c1 = .ok ((f.d, F2), c2) ∧ attain P.S F2 c2 = .ok ((f.x, G), c') := by
  simp only [Attention.hear] at h
  obtain ⟨g, F0, c0, h0, k0⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨⟨planes, sc⟩, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 k0
  obtain ⟨d, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨x, F3, c3, h3, k3⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k3
  rw [e1, e2, e3]
  exact ⟨F0, c0, F1, c1, F2, c2, h0, h1, h2, h3⟩

/-- Behind Seam.start the arrays on slots have their length. -/
theorem start_sized (s : Attention.Seam) (ns : Nat) {L L1 : LinkCtx} {F F1 : Fork} {c c1 : Ctx}
    {tl : HTailF2} (h : s.start ns L F c = .ok (((tl, L1), F1), c1)) :
    F1 = F.fillL.slots ns ∧ Sized F1 ∧ c1 = c := by
  have h : Runs (s.start ns) (L, F, c) tl (L1, F1, c1) := h
  unfold Attention.Seam.start at h
  obtain ⟨u, s1, h1, h2⟩ := HasRuns.runs_bind (m := LinkM) h
  obtain ⟨-, e⟩ := HasRuns.runs_pure h2
  subst e
  obtain ⟨a1, a2⟩ := runs_change (runs_sub h1).1
  have a1' : F.fillL.slots ns = F1 := Option.some.inj a1
  exact ⟨a1'.symm, a1' ▸ sized_slots _ _, a2⟩

/-- Forest.pad, where it succeeds, keeps Sized. -/
def PadSized : Prop :=
  ∀ (calls : Array Model.Call) (pub : Array Nat) (lid : Nat) (F G : Fork) (c c' : Ctx)
    (g : Forest.Heard), Forest.pad calls pub lid F c = .ok ((g, G), c') → Sized F → Sized G

/-- The three routines' successes, with the states and contexts between. -/
structure OwnCut (P : Attention.Plan) (f : Attention.First) (F0 F1 F2 G : Fork)
    (c0 c1 c2 c' : Ctx) : Prop where
  scores : scores P.S f.g.zk F0 c0 = .ok (((f.planes, f.scores), F1), c1)
  divide : divide P.S f.g.zk F1 c1 = .ok ((f.d, F2), c2)
  attain : attain P.S F2 c2 = .ok ((f.x, G), c')
  sized : Sized F0

/-- From a success of Attention.run on a view. -/
theorem run_cut (hp : PadSized) (P : Attention.Plan) {L L' : LinkCtx} {F F' : Fork} {c c' : Ctx}
    (hd : c.ch.dry = false) (h : Attention.run P L F c = .ok ((((), L'), F'), c')) :
    ∃ (f : Attention.First) (F0 F1 F2 G : Fork) (c0 c1 c2 cG : Ctx),
      Forest.pad (P.S.calls.map (·.call)) P.fs.pub P.lid (F.fillL.slots P.ns) c =
        .ok ((f.g, F0), c0) ∧
      OwnCut P f F0 F1 F2 G c0 c1 c2 cG ∧ cG.ch.dry = false ∧
      (c'.failed = none → cG.failed = none) := by
  obtain ⟨tl0, f, t, tl1, tlA, tl, laid, L1, L2, L3, L4, F1, F2, F3, F4, F5, F6, F7, F8, F9, F10,
    F11, F12, F13, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, R⟩ :=
    attention_ran P hd h
  obtain ⟨e0, s1, e1⟩ := start_sized P.seam P.ns R.start
  obtain ⟨G0, d0, G1, d1, G2, d2, a0, a1, a2, a3⟩ := hear_ran P f F1 F2 c1 c2 R.hear
  rw [e1] at a0
  have s0 := hp _ _ _ _ _ _ _ _ a0 s1
  rw [e0] at a0
  exact ⟨f, G0, G1, G2, F2, d0, d1, d2, c2, a0, ⟨a1, a2, a3, s0⟩, R.v2, R.m2⟩

/-- From the verdict on a proof file: the cut at the borders of an attention link's three
routines, in its place in the file's own run. -/
theorem accepted_cut (hp : PadSized) (Z : Array LinkH) (hk : AllKeep Z) {c : Params.ProofChains}
    {table : Params.TableName} {copy : Nat} {request words : ByteArray} {reply : E} {wsLay : WsLay}
    {file : ByteArray}
    (h : Proof.check c table copy request words reply (runLinksH Z c.first wsLay) file = .accepted)
    (j : Nat) (Y : LinkH) (hj : Z.toList[j]? = some Y) (A : Attention.Plan)
    (hY : Y.run = (Verify.attentionPlanOf A).run) :
    ∃ r fin cE check0 ca rN cb cc lin cd checkJ outJ cJ r1 cm chk o C' F' k1 k2 f F0 F1 F2 G c0 c1
      c2 cG,
      FileRan Z c table copy request words reply wsLay file r fin cE check0 ca rN cb cc lin cd ∧
      LinksChain Z c.first wsLay cE (Z.toList.take j) 0 check0 {} ca (checkJ, outJ) cJ ∧
      LinkStep Z c.first wsLay cE j Y checkJ outJ cJ r1 cm chk o C' F' k1 k2 ∧
      LinksChain Z c.first wsLay cE (Z.toList.drop (j + 1)) (j + 1) r1.1 r1.2 cm rN cb ∧
      Forest.pad (A.S.calls.map (·.call)) A.fs.pub A.lid (Y.Fp.fillL.slots A.ns) k1 =
        .ok ((f.g, F0), c0) ∧
      OwnCut A f F0 F1 F2 G c0 c1 c2 cG ∧ cG.ch.dry = false ∧ cG.failed = none := by
  obtain ⟨r, fin, cE, check0, ca, rN, cb, cc, lin, cd, checkJ, outJ, cJ, r1, cm, chk, o, C', F', k1,
    k2, R, A1, S, B⟩ := accepted_at Z hk h j Y hj
  have hr := S.run
  rw [hY] at hr
  obtain ⟨f, F0, F1, F2, G, c0, c1, c2, cG, a0, a1, a2, a3⟩ :=
    run_cut hp A S.v1 (attention_of_link hr).1
  exact ⟨r, fin, cE, check0, ca, rN, cb, cc, lin, cd, checkJ, outJ, cJ, r1, cm, chk, o, C', F', k1,
    k2, f, F0, F1, F2, G, c0, c1, c2, cG, R, A1, S, B, a0, a1, a2, a3 (S.m2 R.noMark)⟩

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.hear_ran
#print axioms OnBytes.Tie.Pv.Att.start_sized
#print axioms OnBytes.Tie.Pv.Att.run_cut
#print axioms OnBytes.Tie.Pv.Att.accepted_cut
