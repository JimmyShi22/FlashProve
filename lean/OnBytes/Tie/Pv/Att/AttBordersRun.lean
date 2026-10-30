-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Att/AttBordersRun.lean: a call of runLinkH on a view whose link's routine is that of
an attention plan has the contexts of AttBorders (OnBytes/Tie/Pv/Att/AttBorders.lean).

The call is taken apart by LinkStep (OnBytes/Tie/Pv/Keeps/KeepsChain.lean), the plan's routine by
attention_ran (KeepsChainA2.lean), what it hears first by hear_ran
(OnBytes/Tie/Pv/Att/HearCut.lean), and the tail's transcript by transcript_ran
(OnBytes/Tie/Pv/Keeps/TranscriptRan.lean). That no message is open is carried from border to border:
behind the first call (first_clean, OnBytes/Tie/Pv/Keeps/KeepsTailsFirst.lean); through the own
rounds (hear_tie, OnBytes/Tie/Pv/Att/HearTie.lean); behind the sendings, the draw and the batching
element (rootInH_view, drawMatrix_view, t2Batch_view, OnBytes/Tie/Pv/Tail/); behind doorH
(doorH_ends, OnBytes/Tie/Pv/Keeps/KeepsTails.lean).

Main names:
  PadLaws: three laws that are taken as premises: Forest.pad keeps that the arrays on slots have
    their length (PadSized); from such a state it keeps that no message is open; rootInH keeps the
    lengths.
  AttLeaves: eight premises: the calls of Attention.run that take no round begin none and take none
    (Rests, OnBytes/Tie/Pv/Att/AttBorders.lean): tables, setPlanClaims, claims, objectsF,
    noFreeSlot, selfTestF, coefficientsF, tileSelfTestF.
  BordersMore Fa F4b L L4: what the laws at the two lookups and at the closing ask beside
    AttBorders: the arrays on slots have their length in front of both lookups; the frame in front
    of doorH has the mask that it had where the routine began (OnBytes/Tie/Pv/Keeps/MaskStays.lean).
  BordersEnt b4 s5 b7 s8 b8 s9 b9 bE: across the calls that take no round the plan's entries that
    are still to come are as they were (Lull.ent_tables and eight more, in plain words, by
    OnBytes/Tie/Pv/Tail/EndLullModel.lean). start_stays: Attention.Seam.start leaves the link's own
    state. run_borders_all: from a success of Attention.run from a context without an open message:
    the contexts from b1 on, with AttBorders, BordersMore and BordersEnt.
  run_borders_more: the same without BordersEnt.
  run_borders: the same without BordersMore.
  step_borders: from a LinkStep whose routine is that of an attention plan, begun without an open
    message: AttBorders, with b0 the step's first context and bE its last.
  step_borders_all: the same, with BordersMore at the link's state with which runLinkH calls the
    routine, BordersEnt, and: the frame in front of doorH has a mask. step_borders_more: AttBorders,
    the lengths in front of both lookups, and the mask.

Limits: one direction: from the calls' success, on a view. PadLaws and AttLeaves are premises. No
typed letter occurs.
-/
import OnBytes.Tie.Pv.Att.AttBorders
import OnBytes.Tie.Pv.Keeps.KeepsTailsFirst
import OnBytes.Tie.Pv.Keeps.TranscriptRan
import OnBytes.Tie.Pv.Tail.SendRoot
import OnBytes.Tie.Pv.Tail.BatRan
import OnBytes.Tie.Pv.Keeps.MaskStays
import OnBytes.Tie.Pv.Tail.EndLullModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Lull
open OnBytes OnBytes.Model OnBytes.L5

/-! The calls of Attention.run that take no round leave the plan's entries that are still to come.
In plain words, for use outside this namespace. -/

theorem ent_tables {S : Attention.Shape} {mats : Array TMat} {nW : Nat} {g : Forest.Heard}
    {planes : Array Attention.PlaneClaim} {scores : Array Attention.Score} {d : Attention.Divide}
    {x : Attention.Attain} {c : Ctx} {t : Attention.Tables} {c' : Ctx}
    (h : Attention.tables S mats nW g planes scores d x c = .ok (t, c')) :
    c'.ch.entries = c.ch.entries := (same_blk inferInstance h).entries

theorem ent_sub {α : Type} {x : SubM α} (k : KeepsM x) {F : Fork} {c : Ctx} {a : α} {G : Fork}
    {c' : Ctx} (h : x F c = .ok ((a, G), c')) : c'.ch.entries = c.ch.entries :=
  (same_sub k h).entries

theorem ent_setPlanClaims {n : Nat} {F : Fork} {c : Ctx} {G : Fork} {c' : Ctx}
    (h : SubM.setPlanClaims n F c = .ok (((), G), c')) : c'.ch.entries = c.ch.entries :=
  ent_sub inferInstance h

theorem ent_claims {P : Attention.Plan} {H : Attention.Heard} {F : Fork} {c : Ctx} {G : Fork}
    {c' : Ctx} (h : Attention.claims P H F c = .ok (((), G), c')) :
    c'.ch.entries = c.ch.entries := ent_sub inferInstance h

theorem ent_objectsF {tl : HTailF2} {funs : Array HFun} {F : Fork} {c : Ctx} {tl' : HTailF2}
    {G : Fork} {c' : Ctx} (h : tl.objectsF funs F c = .ok ((tl', G), c')) :
    c'.ch.entries = c.ch.entries := ent_sub inferInstance h

theorem ent_noFreeSlot {n : Nat} {F : Fork} {c : Ctx} {G : Fork} {c' : Ctx}
    (h : Attention.noFreeSlot n F c = .ok (((), G), c')) : c'.ch.entries = c.ch.entries :=
  ent_sub inferInstance h

theorem ent_selfTestF {tl : HTailF2} {nU : Array Nat} {F : Fork} {c : Ctx} {G : Fork} {c' : Ctx}
    (h : tl.selfTestF nU F c = .ok (((), G), c')) : c'.ch.entries = c.ch.entries :=
  ent_sub inferInstance h

theorem ent_coefficientsF {tl : HTailF2} {F : Fork} {c : Ctx} {G : Fork} {c' : Ctx}
    (h : tl.coefficientsF F c = .ok (((), G), c')) : c'.ch.entries = c.ch.entries :=
  ent_sub inferInstance h

theorem ent_tileSelfTestF {tl : HTailF2} {F : Fork} {c : Ctx} {G : Fork} {c' : Ctx}
    (h : tl.tileSelfTestF F c = .ok (((), G), c')) : c'.ch.entries = c.ch.entries :=
  ent_sub inferInstance h

end OnBytes.Tie.Pv.Tail.Lull

namespace OnBytes.Tie.Pv.Att
open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.Model.Road OnBytes.Attention OnBytes.L5
open OnBytes.Tie.Pv.Tail (rootInH_view drawMatrix_view t2Batch_view)
open OnBytes.L5.TranscriptRan (TrRan transcript_ran)
open OnBytes.Tie.Pv.Keeps.Pend (PendAll keeps_pend runs_pend)

/-- Three laws on the lookup's routine and on a sending, taken as premises. -/
structure PadLaws : Prop where
  sized : PadSized
  clean : ∀ (calls : Array Model.Call) (pub : Array Nat) (lid : Nat) (F G : Fork) (c c' : Ctx)
    (g : Forest.Heard), Forest.pad calls pub lid F c = .ok ((g, G), c') → Sized F →
    PscRun.Clean c → PscRun.Clean c'
  root : ∀ (trees : List Nat) (L L' : LinkCtx) (F F' : Fork) (c c' : Ctx),
    rootInH trees L F c = .ok ((((), L'), F'), c') → Sized F → Sized F'

/-- The calls of Attention.run that take no round: each begins none and takes none. -/
structure AttLeaves : Prop where
  tables : ∀ (S : Attention.Shape) mats nW g planes scores d x (c : Ctx) t (c' : Ctx),
    Attention.tables S mats nW g planes scores d x c = .ok (t, c') → Rests c c'
  setPlan : ∀ n (F : Fork) (c : Ctx) (G : Fork) (c' : Ctx),
    SubM.setPlanClaims n F c = .ok (((), G), c') → Rests c c'
  claims : ∀ (P : Attention.Plan) h (F : Fork) (c : Ctx) (G : Fork) (c' : Ctx),
    Attention.claims P h F c = .ok (((), G), c') → Rests c c'
  objects : ∀ (tl : HTailF2) funs (F : Fork) (c : Ctx) (tl' : HTailF2) (G : Fork) (c' : Ctx),
    tl.objectsF funs F c = .ok ((tl', G), c') → Rests c c'
  noFree : ∀ n (F : Fork) (c : Ctx) (G : Fork) (c' : Ctx),
    Attention.noFreeSlot n F c = .ok (((), G), c') → Rests c c'
  selfTest : ∀ (tl : HTailF2) nU (F : Fork) (c : Ctx) (G : Fork) (c' : Ctx),
    tl.selfTestF nU F c = .ok (((), G), c') → Rests c c'
  coefficients : ∀ (tl : HTailF2) (F : Fork) (c : Ctx) (G : Fork) (c' : Ctx),
    tl.coefficientsF F c = .ok (((), G), c') → Rests c c'
  tile : ∀ (tl : HTailF2) (F : Fork) (c : Ctx) (G : Fork) (c' : Ctx),
    tl.tileSelfTestF F c = .ok (((), G), c') → Rests c c'

/-- What the laws at the two lookups and at the closing ask beside AttBorders: the arrays on slots
have their length in front of both lookups, and the frame in front of doorH has the mask that it had
where the routine began. -/
structure BordersMore (Fa F4b : Fork) (L L4 : LinkCtx) : Prop where
  sizedA : Sized Fa
  sized7 : Sized F4b
  mask : L4.check.frame.mask = L.check.frame.mask

/-- Across the calls of Attention.run that take no round the plan's entries that are still to come
are as they were. -/
structure BordersEnt (b4 s5 b7 s8 b8 s9 b9 bE : Ctx) : Prop where
  ent5 : s5.ch.entries = b4.ch.entries
  ent8 : s8.ch.entries = b7.ch.entries
  ent9 : s9.ch.entries = b8.ch.entries
  entE : bE.ch.entries = b9.ch.entries

theorem start_stays (s : Attention.Seam) (ns : Nat) : Stays (s.start ns) := by
  unfold Attention.Seam.start
  repeat' first
    | exact Stays.pure _
    | exact Stays.sub _
    | refine Stays.bind ?_ fun _ => ?_

/-- From a success of Attention.run from a context without an open message. -/
theorem run_borders_all (hp : PadLaws) (hl : AttLeaves) (P : Attention.Plan) {L L' : LinkCtx}
    {F F' : Fork} {c c' : Ctx} (hc : PscRun.Clean c)
    (h : Attention.run P L F c = .ok ((((), L'), F'), c')) {check chk : ChainCheck} {b0 : Ctx}
    (h0 : PscRun.Clean b0) (h1 : check.first b0 = .ok (chk, c)) :
    ∃ f Fa F0 F1 F2 G F3 F4a F4b F4 F5 F6 F12 F13 L1 L2 L3 L4 tl1 tlM g laid b2 m1 m2 b3 b4 s5 b5
      b6 b7 s8 b8 s9 b9,
      AttBorders P check chk f Fa F0 F1 F2 G F3 F4a F4b F4 F5 F6 F12 F13 L1 L2 L3 L4 L' tl1 tlM g
        laid b0 c b2 m1 m2 b3 b4 s5 b5 b6 b7 s8 b8 s9 b9 c' ∧ BordersMore Fa F4b L L4 ∧
      BordersEnt b4 s5 b7 s8 b8 s9 b9 c' := by
  obtain ⟨tl0, f, t, tl1, tlA, tl, laid, L1, L2, L3, L4, F1, F2, F3, F4, F5, F6, F7, F8, F9, F10,
    F11, F12, F13, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, R⟩ :=
    attention_ran P hc.1 h
  obtain ⟨_, sF1, ec⟩ := start_sized P.seam P.ns R.start
  have eL1 : L1 = L :=
    Stays.apply (start_stays P.seam P.ns) (s := (L, F, c)) (s' := (L1, F1, c1)) R.start
  subst ec
  obtain ⟨G0, d0, G1, d1, G2, d2, hpad, hs, hd, hx⟩ := hear_ran P f F1 F2 c1 c2 R.hear
  have s0 : Sized G0 := hp.sized _ _ _ _ _ _ _ _ hpad sF1
  have k2 : PscRun.Clean d0 := hp.clean _ _ _ _ _ _ _ _ hpad sF1 hc
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    ⟨_, _, _, _, _, _, a7⟩, _, hw, _⟩ :=
    hear_tie P.S f.g.zk (f.planes, f.scores) f.d f.x G0 G1 G2 F2 d0 d1 d2 c2 hs hd hx s0
  obtain ⟨_, _, _, _, r4⟩ := hw k2.1
  have k3 : PscRun.Clean c2 := r4 k2
  obtain ⟨_, _, _, _, _, _, t4⟩ := rootInH_view [P.iU3] L1 L2 F2 F3 c2 c3 k3 R.root
  have s3 : Sized F3 := hp.root _ _ _ _ _ _ _ R.root a7
  have e5 : Rests c3 c4 := hl.tables _ _ _ _ _ _ _ _ c3 t c4 R.tables
  have k5 : PscRun.Clean c4 := e5.clean R.v4 t4.clean
  obtain ⟨tlM, g, Fa, Fb, e1, e2, T⟩ := transcript_ran tl1 R.v4 R.transcript
  obtain ⟨eF, _, hr5, _, _⟩ := drawMatrix_view tl1 tlM F3 Fa c4 e1 k5 T.draw
  obtain ⟨_, _, _, _, _, _, t6⟩ := rootInH_view _ L2 L3 Fa Fb e1 e2 hr5.2.1 T.root
  have s6 : Sized Fb := hp.root _ _ _ _ _ _ _ T.root (eF ▸ s3)
  have k7 : PscRun.Clean c5 := hp.clean _ _ _ _ _ _ _ _ T.pad s6 t6.clean
  have e8 : Rests c5 c6 := hl.setPlan _ F4 c5 F5 c6 R.setPlan
  have k8 : PscRun.Clean c6 := e8.clean R.v6 k7
  obtain ⟨_, _, hr8, _, _⟩ := t2Batch_view F5.next L3 L4 F5 F6 c6 c7 () k8 R.batch
  have e9 : Rests c7 c13 :=
    (hl.claims P _ F6 c7 F7 c8 R.claims).trans ((hl.objects tlA _ F7 c8 tl F8 c9 R.objects).trans
      ((hl.noFree _ F8 c9 F9 c10 R.noFree).trans ((hl.selfTest tl _ F9 c10 F10 c11 R.selfTest).trans
        ((hl.coefficients tl F10 c11 F11 c12 R.coefficients).trans
          (hl.tile tl F11 c12 F12 c13 R.tile)))))
  have k9 : PscRun.Clean c14 :=
    ⟨R.v14, Keeps.Cut.doorH_ends laid (L4, F12, c13) () (L', F13, c14) R.door R.v13⟩
  have eE : c'.ch = c14.ch := Keeps.Cut.countsHeld_leaves P tl (F13, c14) () (F', c') R.counts
  have hP : ∀ Q : Fmt.Entry → Fmt.Drawn → Prop, PendAll Q b0 →
      PendAll Q c1 ∧ PendAll Q d0 ∧ PendAll Q c2 ∧ PendAll Q c3 ∧ PendAll Q c4 ∧ PendAll Q e1 ∧
      PendAll Q e2 ∧ PendAll Q c5 ∧ PendAll Q c6 ∧ PendAll Q c7 ∧ PendAll Q c13 ∧ PendAll Q c14 ∧
      PendAll Q c' := fun Q q0 => by
    have q1 : PendAll Q c1 := keeps_pend check.first q0 h1
    have q2 : PendAll Q d0 :=
      runs_pend (x := Forest.pad _ _ _) (s := (F1, c1)) (s' := (G0, d0)) hpad q1
    have q3 : PendAll Q c2 :=
      runs_pend (x := Attention.hear P) (s := (F1, c1)) (s' := (F2, c2)) R.hear q1
    have q4 : PendAll Q c3 :=
      runs_pend (x := rootInH [P.iU3]) (s := (L1, F2, c2)) (s' := (L2, F3, c3)) R.root q3
    have q5 : PendAll Q c4 :=
      runs_pend (x := Attention.tables _ _ _ _ _ _ _ _) (s := c3) (s' := c4) R.tables q4
    have q6 : PendAll Q e1 :=
      runs_pend (x := tl1.drawMatrixF) (s := (F3, c4)) (s' := (Fa, e1)) T.draw q5
    have q7 : PendAll Q e2 :=
      runs_pend (x := rootInH [tlM.ix.ZZ, tlM.ix.BZ]) (s := (L2, Fa, e1)) (s' := (L3, Fb, e2))
        T.root q6
    have q8 : PendAll Q c5 :=
      runs_pend (x := Forest.pad _ _ _) (s := (Fb, e2)) (s' := (F4, c5)) T.pad q7
    have q9 : PendAll Q c6 :=
      runs_pend (x := SubM.setPlanClaims P.nLin) (s := (F4, c5)) (s' := (F5, c6)) R.setPlan q8
    have q10 : PendAll Q c7 :=
      runs_pend (x := t2Batch F5.next) (s := (L3, F5, c6)) (s' := (L4, F6, c7)) R.batch q9
    have q11 : PendAll Q c8 :=
      runs_pend (x := Attention.claims P _) (s := (F6, c7)) (s' := (F7, c8)) R.claims q10
    have q12 : PendAll Q c9 :=
      runs_pend (x := tlA.objectsF _) (s := (F7, c8)) (s' := (F8, c9)) R.objects q11
    have q13 : PendAll Q c10 :=
      runs_pend (x := Attention.noFreeSlot _) (s := (F8, c9)) (s' := (F9, c10)) R.noFree q12
    have q14 : PendAll Q c11 :=
      runs_pend (x := tl.selfTestF _) (s := (F9, c10)) (s' := (F10, c11)) R.selfTest q13
    have q15 : PendAll Q c12 :=
      runs_pend (x := tl.coefficientsF) (s := (F10, c11)) (s' := (F11, c12)) R.coefficients q14
    have q16 : PendAll Q c13 :=
      runs_pend (x := tl.tileSelfTestF) (s := (F11, c12)) (s' := (F12, c13)) R.tile q15
    have q17 : PendAll Q c14 :=
      runs_pend (x := doorH laid) (s := (L4, F12, c13)) (s' := (L', F13, c14)) R.door q16
    have q18 : PendAll Q c' :=
      runs_pend (x := Attention.countsHeld P tl) (s := (F13, c14)) (s' := (F', c')) R.counts q17
    exact ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q16, q17, q18⟩
  exact ⟨f, F1, G0, G1, G2, F2, F3, Fa, Fb, F4, F5, F6, F12, F13, L1, L2, L3, L4, tl1, tlM, g, laid,
    d0, d1, d2, c2, c3, c4, e1, e2, c5, c6, c7, c13, c14,
    ⟨h1, hpad, ⟨hs, hd, hx, s0⟩, R.root, e5.2, T.draw, T.root, T.pad, e8.2, R.batch, e9.2, R.door,
      congrArg (·.left) eE, h0, hc, k2, k3, t4.clean, hr5.2.1, t6.clean, k7, hr8.2.1, k9, k5, k8,
      e9.clean R.v13 hr8.2.1, ⟨R.vEnd, (congrArg (·.cur) eE).trans k9.2⟩, hP⟩,
    ⟨sF1, s6, (t2Batch_mask _ R.batch).trans ((rootInH_mask _ hr5.2.1.1 T.root).trans
      ((rootInH_mask _ k3.1 R.root).trans (by rw [eL1])))⟩,
    ⟨Tail.Lull.ent_tables R.tables, Tail.Lull.ent_setPlanClaims R.setPlan,
      (Tail.Lull.ent_tileSelfTestF R.tile).trans ((Tail.Lull.ent_coefficientsF R.coefficients).trans
        ((Tail.Lull.ent_selfTestF R.selfTest).trans ((Tail.Lull.ent_noFreeSlot R.noFree).trans
          ((Tail.Lull.ent_objectsF R.objects).trans (Tail.Lull.ent_claims R.claims))))),
      congrArg (·.entries) eE⟩⟩

/-- The same without the record on the entries. -/
theorem run_borders_more (hp : PadLaws) (hl : AttLeaves) (P : Attention.Plan) {L L' : LinkCtx}
    {F F' : Fork} {c c' : Ctx} (hc : PscRun.Clean c)
    (h : Attention.run P L F c = .ok ((((), L'), F'), c')) {check chk : ChainCheck} {b0 : Ctx}
    (h0 : PscRun.Clean b0) (h1 : check.first b0 = .ok (chk, c)) :
    ∃ f Fa F0 F1 F2 G F3 F4a F4b F4 F5 F6 F12 F13 L1 L2 L3 L4 tl1 tlM g laid b2 m1 m2 b3 b4 s5 b5
      b6 b7 s8 b8 s9 b9,
      AttBorders P check chk f Fa F0 F1 F2 G F3 F4a F4b F4 F5 F6 F12 F13 L1 L2 L3 L4 L' tl1 tlM g
        laid b0 c b2 m1 m2 b3 b4 s5 b5 b6 b7 s8 b8 s9 b9 c' ∧ BordersMore Fa F4b L L4 := by
  obtain ⟨f, Fa, F0, F1, F2, G, F3, F4a, F4b, F4, F5, F6, F12, F13, L1, L2, L3, L4, tl1, tlM, g,
    laid, b2, m1, m2, b3, b4, s5, b5, b6, b7, s8, b8, s9, b9, B, M, _⟩ :=
    run_borders_all hp hl P hc h h0 h1
  exact ⟨f, Fa, F0, F1, F2, G, F3, F4a, F4b, F4, F5, F6, F12, F13, L1, L2, L3, L4, tl1, tlM, g,
    laid, b2, m1, m2, b3, b4, s5, b5, b6, b7, s8, b8, s9, b9, B, M⟩

/-- The same without the second record. -/
theorem run_borders (hp : PadLaws) (hl : AttLeaves) (P : Attention.Plan) {L L' : LinkCtx}
    {F F' : Fork} {c c' : Ctx} (hc : PscRun.Clean c)
    (h : Attention.run P L F c = .ok ((((), L'), F'), c')) {check chk : ChainCheck} {b0 : Ctx}
    (h0 : PscRun.Clean b0) (h1 : check.first b0 = .ok (chk, c)) :
    ∃ f Fa F0 F1 F2 G F3 F4a F4b F4 F5 F6 F12 F13 L1 L2 L3 L4 tl1 tlM g laid b2 m1 m2 b3 b4 s5 b5
      b6 b7 s8 b8 s9 b9,
      AttBorders P check chk f Fa F0 F1 F2 G F3 F4a F4b F4 F5 F6 F12 F13 L1 L2 L3 L4 L' tl1 tlM g
        laid b0 c b2 m1 m2 b3 b4 s5 b5 b6 b7 s8 b8 s9 b9 c' := by
  obtain ⟨f, Fa, F0, F1, F2, G, F3, F4a, F4b, F4, F5, F6, F12, F13, L1, L2, L3, L4, tl1, tlM, g,
    laid, b2, m1, m2, b3, b4, s5, b5, b6, b7, s8, b8, s9, b9, B, _⟩ :=
    run_borders_more hp hl P hc h h0 h1
  exact ⟨f, Fa, F0, F1, F2, G, F3, F4a, F4b, F4, F5, F6, F12, F13, L1, L2, L3, L4, tl1, tlM, g,
    laid, b2, m1, m2, b3, b4, s5, b5, b6, b7, s8, b8, s9, b9, B⟩

/-- From a call of runLinkH whose link's routine is that of an attention plan. -/
theorem step_borders (hp : PadLaws) (hl : AttLeaves) {links : Array LinkH} {p : Params.First}
    {wsLay : WsLay} {cEnd : Ctx} {l : Nat} {X : LinkH} {check : ChainCheck}
    {out : Proof.LinksResult} {c : Ctx} {r : ChainCheck × Proof.LinksResult} {c' : Ctx}
    {chk : ChainCheck} {o : Option WsForkOut} {C' : LinkCtx} {F' : Fork} {c1 c2 : Ctx}
    (S : LinkStep links p wsLay cEnd l X check out c r c' chk o C' F' c1 c2)
    (A : Attention.Plan) (hY : X.run = (Verify.attentionPlanOf A).run) (hc : PscRun.Clean c) :
    ∃ f Fa F0 F1 F2 G F3 F4a F4b F4 F5 F6 F12 F13 L1 L2 L3 L4 tl1 tlM g laid b2 m1 m2 b3 b4 s5 b5
      b6 b7 s8 b8 s9 b9,
      AttBorders A check chk f Fa F0 F1 F2 G F3 F4a F4b F4 F5 F6 F12 F13 L1 L2 L3 L4 C' tl1 tlM g
        laid c c1 b2 m1 m2 b3 b4 s5 b5 b6 b7 s8 b8 s9 b9 c' := by
  have hr := S.run
  rw [hY] at hr
  obtain ⟨ha, ho⟩ := attention_of_link hr
  have e : c' = c2 := by
    by_cases hv : X.fv = true
    · obtain ⟨o', _, h1, _⟩ := S.row hv
      rw [ho] at h1
      cases h1
    · exact (S.noRow hv).1
  rw [e]
  exact run_borders hp hl A (Keeps.Cut.first_clean hc.1 S.first) ha hc S.first

/-- From a call of runLinkH whose link's routine is that of an attention plan: AttBorders, both
records beside it, and: the frame in front of doorH has a mask. -/
theorem step_borders_all (hp : PadLaws) (hl : AttLeaves) {links : Array LinkH}
    {p : Params.First} {wsLay : WsLay} {cEnd : Ctx} {l : Nat} {X : LinkH} {check : ChainCheck}
    {out : Proof.LinksResult} {c : Ctx} {r : ChainCheck × Proof.LinksResult} {c' : Ctx}
    {chk : ChainCheck} {o : Option WsForkOut} {C' : LinkCtx} {F' : Fork} {c1 c2 : Ctx}
    (S : LinkStep links p wsLay cEnd l X check out c r c' chk o C' F' c1 c2)
    (A : Attention.Plan) (hY : X.run = (Verify.attentionPlanOf A).run) (hc : PscRun.Clean c) :
    ∃ f Fa F0 F1 F2 G F3 F4a F4b F4 F5 F6 F12 F13 L1 L2 L3 L4 tl1 tlM g laid b2 m1 m2 b3 b4 s5 b5
      b6 b7 s8 b8 s9 b9,
      AttBorders A check chk f Fa F0 F1 F2 G F3 F4a F4b F4 F5 F6 F12 F13 L1 L2 L3 L4 C' tl1 tlM g
        laid c c1 b2 m1 m2 b3 b4 s5 b5 b6 b7 s8 b8 s9 b9 c' ∧
      BordersMore Fa F4b { check := chk, link := l, arrayOf := X.arrayOf, list := X.Tp } L4 ∧
      BordersEnt b4 s5 b7 s8 b8 s9 b9 c' ∧ L4.check.frame.mask.isSome = true := by
  have hr := S.run
  rw [hY] at hr
  obtain ⟨ha, ho⟩ := attention_of_link hr
  have e : c' = c2 := by
    by_cases hv : X.fv = true
    · obtain ⟨o', _, h1, _⟩ := S.row hv
      rw [ho] at h1
      cases h1
    · exact (S.noRow hv).1
  rw [e]
  obtain ⟨f, Fa, F0, F1, F2, G, F3, F4a, F4b, F4, F5, F6, F12, F13, L1, L2, L3, L4, tl1, tlM, g,
    laid, b2, m1, m2, b3, b4, s5, b5, b6, b7, s8, b8, s9, b9, B, M, N⟩ :=
    run_borders_all hp hl A (Keeps.Cut.first_clean hc.1 S.first) ha hc S.first
  obtain ⟨q, _, _, _, _, _, _, mask, _, _, _, _, _, Q, e1, _⟩ :=
    check_first_parts check (cEnd := c1) hc.1 id S.first
  refine ⟨f, Fa, F0, F1, F2, G, F3, F4a, F4b, F4, F5, F6, F12, F13, L1, L2, L3, L4, tl1, tlM, g,
    laid, b2, m1, m2, b3, b4, s5, b5, b6, b7, s8, b8, s9, b9, B, M, N, ?_⟩
  rw [M.mask]
  show chk.frame.mask.isSome = true
  rw [e1]
  show q.1.mask.isSome = true
  rw [Q.plain_eq.2.1]
  rfl

/-- From a call of runLinkH whose link's routine is that of an attention plan: AttBorders, and: the
arrays on slots have their length in front of both lookups; the frame in front of doorH has a
mask. -/
theorem step_borders_more (hp : PadLaws) (hl : AttLeaves) {links : Array LinkH}
    {p : Params.First} {wsLay : WsLay} {cEnd : Ctx} {l : Nat} {X : LinkH} {check : ChainCheck}
    {out : Proof.LinksResult} {c : Ctx} {r : ChainCheck × Proof.LinksResult} {c' : Ctx}
    {chk : ChainCheck} {o : Option WsForkOut} {C' : LinkCtx} {F' : Fork} {c1 c2 : Ctx}
    (S : LinkStep links p wsLay cEnd l X check out c r c' chk o C' F' c1 c2)
    (A : Attention.Plan) (hY : X.run = (Verify.attentionPlanOf A).run) (hc : PscRun.Clean c) :
    ∃ f Fa F0 F1 F2 G F3 F4a F4b F4 F5 F6 F12 F13 L1 L2 L3 L4 tl1 tlM g laid b2 m1 m2 b3 b4 s5 b5
      b6 b7 s8 b8 s9 b9,
      AttBorders A check chk f Fa F0 F1 F2 G F3 F4a F4b F4 F5 F6 F12 F13 L1 L2 L3 L4 C' tl1 tlM g
        laid c c1 b2 m1 m2 b3 b4 s5 b5 b6 b7 s8 b8 s9 b9 c' ∧ Sized Fa ∧ Sized F4b ∧
      L4.check.frame.mask.isSome = true := by
  obtain ⟨f, Fa, F0, F1, F2, G, F3, F4a, F4b, F4, F5, F6, F12, F13, L1, L2, L3, L4, tl1, tlM, g,
    laid, b2, m1, m2, b3, b4, s5, b5, b6, b7, s8, b8, s9, b9, B, M, _, hm⟩ :=
    step_borders_all hp hl S A hY hc
  exact ⟨f, Fa, F0, F1, F2, G, F3, F4a, F4b, F4, F5, F6, F12, F13, L1, L2, L3, L4, tl1, tlM, g,
    laid, b2, m1, m2, b3, b4, s5, b5, b6, b7, s8, b8, s9, b9, B, M.sizedA, M.sized7, hm⟩

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.run_borders_all
#print axioms OnBytes.Tie.Pv.Att.step_borders_all
#print axioms OnBytes.Tie.Pv.Att.run_borders_more
#print axioms OnBytes.Tie.Pv.Att.step_borders_more
#print axioms OnBytes.Tie.Pv.Att.run_borders
#print axioms OnBytes.Tie.Pv.Att.step_borders
