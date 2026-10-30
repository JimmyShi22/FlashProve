-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsChainA2.lean: the check of an attention sub-proof (Attention.run,
OnBytes/Model/Attention.lean), taken apart whole.

If Attention.run P succeeds from the link's state L, the sub-proof's state F and a context c that is
no dry run, and leaves L', F', c', then every call of the routine (Seam.finish's calls among them)
has succeeded, the first from L, F, c, each later one from what the one before has left, the last
leaving L', F', c'. The record AttRan has one field for each call, in the routine's order:
  a bare run (the routine applied to its states and the context) for a call that may change
    something; a call of a sub-proof's routine leaves the link's state, a block leaves that and the
    sub-proof's;
  for a test or a read that leaves all as it was: what it tested, or the value in place of a letter
    (the two reads of the next slot).
For every context that the run passes: it is no dry run (v), and if the last context has no mark of
a failed named test, it has none (m).

Limits: one direction: from a success. Nothing is said on what a run does.
-/
import OnBytes.Tie.Pv.Keeps.KeepsPeel
import OnBytes.Tie.Pv.Keeps.KeepsModel

namespace OnBytes.L5

open OnBytes OnBytes.Model

/-- The record that Attention.run hands to its claims. -/
def heardOf' (P : Attention.Plan) (f : Attention.First) (t : Attention.Tables) : Attention.Heard :=
  { S := P.S, g := f.g, planes := f.planes, scores := f.scores, d := f.d, x := f.x, t := t,
    iU3 := P.iU3 }

/-- All calls of one run of Attention.run, in order. L F c: where the run began; L' F' c': what it
left. -/
structure AttRan (P : Attention.Plan) (L : LinkCtx) (F : Fork) (c : Ctx) (L' : LinkCtx) (F' : Fork)
    (c' : Ctx) (tl0 : HTailF2) (f : Attention.First) (t : Attention.Tables) (tl1 tlA tl : HTailF2)
    (laid : Nat) (L1 L2 L3 L4 : LinkCtx) (F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 : Fork)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : Ctx) : Prop where
  start : P.seam.start P.ns L F c = .ok (((tl0, L1), F1), c1)
  hear : Attention.hear P F1 c1 = .ok ((f, F2), c2)
  root : rootInH [P.iU3] L1 F2 c2 = .ok ((((), L2), F3), c3)
  funOpen : tl0.funOpen = true
  tables : Attention.tables P.S P.mats P.nW f.g f.planes f.scores f.d f.x c3 = .ok (t, c4)
  closed : tl0.closeFuns t.funs = some tl1
  transcript : tl1.transcript L2 F3 c4 = .ok (((tlA, L3), F4), c5)
  slotCount : (F4.next == P.nMsg) = true
  setPlan : SubM.setPlanClaims P.nLin F4 c5 = .ok (((), F5), c6)
  batch : t2Batch F5.next L3 F5 c6 = .ok ((((), L4), F6), c7)
  claims : Attention.claims P (heardOf' P f t) F6 c7 = .ok (((), F7), c8)
  objects : tlA.objectsF t.funs F7 c8 = .ok ((tl, F8), c9)
  noFree : Attention.noFreeSlot P.nMsg F8 c9 = .ok (((), F9), c10)
  held : tl.funsHeld t.funs = true
  selfTest : tl.selfTestF P.seam.nU F9 c10 = .ok (((), F10), c11)
  coefficients : tl.coefficientsF F10 c11 = .ok (((), F11), c12)
  tile : tl.tileSelfTestF F11 c12 = .ok (((), F12), c13)
  laidIs : tl.equationsLaidF = some laid
  door : doorH laid L4 F12 c13 = .ok ((((), L'), F13), c14)
  counts : Attention.countsHeld P tl F13 c14 = .ok (((), F'), c')
  v1 : c1.ch.dry = false
  v2 : c2.ch.dry = false
  v3 : c3.ch.dry = false
  v4 : c4.ch.dry = false
  v5 : c5.ch.dry = false
  v6 : c6.ch.dry = false
  v7 : c7.ch.dry = false
  v8 : c8.ch.dry = false
  v9 : c9.ch.dry = false
  v10 : c10.ch.dry = false
  v11 : c11.ch.dry = false
  v12 : c12.ch.dry = false
  v13 : c13.ch.dry = false
  v14 : c14.ch.dry = false
  vEnd : c'.ch.dry = false
  m0 : c'.failed = none → c.failed = none
  m1 : c'.failed = none → c1.failed = none
  m2 : c'.failed = none → c2.failed = none
  m3 : c'.failed = none → c3.failed = none
  m4 : c'.failed = none → c4.failed = none
  m5 : c'.failed = none → c5.failed = none
  m6 : c'.failed = none → c6.failed = none
  m7 : c'.failed = none → c7.failed = none
  m8 : c'.failed = none → c8.failed = none
  m9 : c'.failed = none → c9.failed = none
  m10 : c'.failed = none → c10.failed = none
  m11 : c'.failed = none → c11.failed = none
  m12 : c'.failed = none → c12.failed = none
  m13 : c'.failed = none → c13.failed = none
  m14 : c'.failed = none → c14.failed = none

/-- Attention.run, taken apart whole. -/
theorem attention_ran (P : Attention.Plan) {L L' : LinkCtx} {F F' : Fork} {c c' : Ctx}
    (hd : c.ch.dry = false) (h : Attention.run P L F c = .ok ((((), L'), F'), c')) :
    ∃ tl0 f t tl1 tlA tl laid L1 L2 L3 L4 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 c1 c2 c3 c4 c5
      c6 c7 c8 c9 c10 c11 c12 c13 c14,
      AttRan P L F c L' F' c' tl0 f t tl1 tlA tl laid L1 L2 L3 L4 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11
        F12 F13 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 := by
  have h : Runs (Attention.run P) (L, F, c) () (L', F', c') := h
  have d : View (m := LinkM) (L, F, c) := hd
  unfold Attention.run at h
  peel3 h d
  rename_i tl1 e1
  unfold Attention.Seam.finish at r16
  peel3_from r16 d15 b16 21
  rename_i laid e2
  have dE := runs_view h d16
  down r2
  obtain ⟨t4, e⟩ := mustAs_L r4
  cases e
  down r5
  down r5
  obtain ⟨t7, e⟩ := slot_L r7
  cases e
  obtain ⟨t8, e⟩ := mustAs_L r8
  cases e
  down r9
  obtain ⟨t10, e⟩ := slot_L r10
  cases e
  down r12
  down r13
  down r14
  obtain ⟨t15, e⟩ := mustAs_L r15
  cases e
  down r21
  down r22
  down r23
  down h
  subst t7
  subst t10
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    { start := r1, hear := r2, root := r3, funOpen := t4, tables := r5, closed := e1,
      transcript := r6, slotCount := t8, setPlan := r9, batch := r11, claims := r12,
      objects := r13, noFree := r14, held := t15, selfTest := r21, coefficients := r22,
      tile := r23, laidIs := e2, door := r16, counts := h,
      v1 := d1, v2 := d2, v3 := d3, v4 := d5, v5 := d6, v6 := d9, v7 := d11, v8 := d12,
      v9 := d13, v10 := d14, v11 := d21, v12 := d22, v13 := d23, v14 := d16,
      vEnd := dE, m0 := b0,
      m1 := b1, m2 := b2, m3 := b3, m4 := b5, m5 := b6, m6 := b9, m7 := b11, m8 := b12,
      m9 := b13, m10 := b14, m11 := b21, m12 := b22, m13 := b23, m14 := b16 }⟩

#print axioms attention_ran

end OnBytes.L5
