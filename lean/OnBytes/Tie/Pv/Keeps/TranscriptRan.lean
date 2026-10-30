-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Keeps/TranscriptRan.lean: the messages of a sub-proof's smallness test
(HTailF2.transcript, OnBytes/Model/Tail.lean), taken apart whole.

The records of a whole run of an attention sub-proof's check and of a layers' sub-proof's check keep
the call of HTailF2.transcript whole. Here that call is taken apart, for every plan tl of a closing
part: if it succeeds from the link's state L, the sub-proof's state F and a context c that is no dry
run, then each of its calls has succeeded, the first from L, F, c, each later one from what the one
before has left.

Main names:
  `TrRan`: all calls of one run, in order: the two public tests; the test on the order on which the
    draw of the matrix relies, which leaves all as it was; the draw of the matrix (drawMatrixF); the
    receipt of the commitment to the two arrays of digits (rootInH); the lookup on the digits
    (Forest.pad); what is returned. The contexts between are no dry runs (v), and if the last
    context has no mark of a failed named test, they have none (m).
  `transcript_ran`: HTailF2.transcript, taken apart whole.

Limits: one direction: from a success. Nothing is said on what a run does. drawMatrixF, rootInH and
Forest.pad are kept whole.
-/
import OnBytes.Tie.Pv.Keeps.KeepsPeel
import OnBytes.Tie.Pv.Keeps.KeepsLoop
import OnBytes.Tie.Pv.Keeps.KeepsModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.L5.TranscriptRan
open OnBytes OnBytes.Model OnBytes.L5

/-- A value read off the sub-proof's state, in a link. -/
theorem ask_L {α : Type} {f : Fork → Option α} {s : HasRuns.St LinkM} {a : α}
    {s' : HasRuns.St LinkM} (h : Runs (LinkM.sub (SubM.ask f)) s a s') :
    f s.2.1 = some a ∧ s' = s := by
  obtain ⟨h1, e1⟩ := runs_sub h
  obtain ⟨h2, e2⟩ := runs_ask h1
  exact ⟨h2, Prod.ext e1 e2⟩

/-- Reading the statement leaves the context as it was. -/
theorem statement_B {c : Ctx} {a : Statement} {c' : Ctx} (h : Runs Blk.statement c a c') :
    a = c.st ∧ c' = c := by
  have k : (Except.ok (c.st, c) : Except Failure (Statement × Ctx)) = .ok (a, c') := h
  cases k
  exact ⟨rfl, rfl⟩

/-- All calls of one run of HTailF2.transcript, in order. L F c: where the run began; L' F' c':
what it left. -/
structure TrRan (tl : HTailF2) (L : LinkCtx) (F : Fork) (c : Ctx) (tlA : HTailF2) (L' : LinkCtx)
    (F' : Fork) (c' : Ctx) (tlM : HTailF2) (g : Forest.Heard) (F1 F2 : Fork) (c1 c2 : Ctx) :
    Prop where
  closed : tl.funClosed = true
  map : (tl.shp.size == tl.NM) = true
  order : (L.check.link == L.link && decide (L.link < L.check.links) && tl.gtTree.size == tl.NM &&
      tl.gtTree.all (HTailF2.arrayFixed L c.st) &&
    (List.range 4).all fun n => Option.all (HTailF2.arrayFixed L c.st) (tl.ix.U.getD n none)) = true
  draw : tl.drawMatrixF F c = .ok ((tlM, F1), c1)
  root : rootInH [tlM.ix.ZZ, tlM.ix.BZ] L F1 c1 = .ok ((((), L'), F2), c2)
  pad : Forest.pad #[tlM.z1.call, tlM.z2.call] tlM.f9.pub tlM.lidb F2 c2 = .ok ((g, F'), c')
  out : tlA = { tlM with
    foldDrawn := tlM.foldDrawn + 1, slotA := F.next, slotB := F'.next, heard := some g }
  v1 : c1.ch.dry = false
  v2 : c2.ch.dry = false
  vEnd : c'.ch.dry = false
  m0 : c'.failed = none → c.failed = none
  m1 : c'.failed = none → c1.failed = none
  m2 : c'.failed = none → c2.failed = none

/-- HTailF2.transcript, taken apart whole. -/
theorem transcript_ran (tl : HTailF2) {L L' : LinkCtx} {F F' : Fork} {c c' : Ctx} {tlA : HTailF2}
    (hd : c.ch.dry = false) (h0 : tl.transcript L F c = .ok (((tlA, L'), F'), c')) :
    ∃ tlM g F1 F2 c1 c2, TrRan tl L F c tlA L' F' c' tlM g F1 F2 c1 c2 := by
  have h : Runs tl.transcript (L, F, c) tlA (L', F', c') := h0
  clear h0
  have d : View (m := LinkM) (L, F, c) := hd
  unfold HTailF2.transcript HTailF2.transcriptF at h
  peel3 h d
  unfold HTailF2.fixedBeforeTheMatrixF at r4
  peel3_from r4 d3 b4 11
  obtain ⟨t1, e⟩ := linkMustAs_L r1
  cases e
  obtain ⟨t2, e⟩ := linkMustAs_L r2
  cases e
  obtain ⟨t3, e⟩ := ask_L (f := fun F => some F.next) r3
  cases e
  have t3' := (Option.some.inj t3).symm
  dsimp only at t3'
  subst t3'
  obtain ⟨t11, e⟩ := runs_get r11
  cases e
  dsimp only at t11
  subst t11
  down_sub r12
  down r12
  obtain ⟨e1, e2⟩ := statement_B r12
  dsimp only at e1 e2
  subst e1
  subst e2
  obtain ⟨t4, e⟩ := linkMustAs_L r4
  cases e
  down_sub r5
  down_sub r7
  obtain ⟨t8, e⟩ := ask_L (f := fun F => some F.next) r8
  cases e
  have t8' := (Option.some.inj t8).symm
  dsimp only at t8'
  subst t8'
  obtain ⟨w1, e⟩ := HasRuns.runs_pure h
  cases e
  exact ⟨_, _, _, _, _, _,
    { closed := t1, map := t2, order := t4, draw := r5, root := r6, pad := r7, out := w1,
      v1 := d5, v2 := d6, vEnd := d7, m0 := b0, m1 := b5, m2 := b6 }⟩

end OnBytes.L5.TranscriptRan

#print axioms OnBytes.L5.TranscriptRan.transcript_ran
