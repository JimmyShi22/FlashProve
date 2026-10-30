-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/LayerRan.lean: the check of a layers' sub-proof (Layer.runForkHidG2,
OnBytes/Model/Layer.lean), taken apart whole.

If Layer.runForkHidG2 P hp g succeeds from the link's state L, the sub-proof's state F and a context
c that is no dry run, and leaves L', F', c', then every call of the routine has succeeded, the first
from L, F, c, each later one from what the one before has left, the last leaving L', F', c'. The
record `LayRan` has the cut of OnBytes/Tie/Pv/Keeps/LayerCut.lean for the calls up to rootInH, and
one field for each call behind it, in the routine's order: a bare run (the routine applied to its
states and the context) for a call that may change something; a call of a sub-proof's routine leaves
the link's state; for a test or a read that leaves all as it was: what it tested, or the value in
place of a letter. It does for the layers what OnBytes/Tie/Pv/Keeps/KeepsChainA2.lean does for
attention.

Main names:
  `form_L`, `ask_L`: two reads in a link that leave all as it was.
  `LayRan`: all calls of one run, in order. For every context that the run passes: it is no dry run
    (v), and if the last context has no mark of a failed named test, it has none (m).
  `layer_ran`: Layer.runForkHidG2, taken apart whole.

Limits: one direction: from a success. Nothing is said on what a run does. The claim on the
embedding is added in the first group alone: the field emb says which of the two cases holds. That
Forest.pad keeps `Sized` is a premise, as in OnBytes/Tie/Pv/Keeps/LayerCut.lean.
-/
import OnBytes.Tie.Pv.Keeps.LayerCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.L5.LayerRan
open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.Model.Road OnBytes.L5 OnBytes.L5.LayerCut

/-- A value that must be there, read in a link. -/
theorem form_L {α : Type} {x : Option α} {s : HasRuns.St LinkM} {a : α} {s' : HasRuns.St LinkM}
    (h : Runs (LinkM.sub (Layer.form x)) s a s') : x = some a ∧ s' = s := by
  obtain ⟨h1, e1⟩ := runs_sub h
  unfold Layer.form SubM.get at h1
  obtain ⟨h2, e2⟩ := runs_lift (σ := Fork) h1
  obtain ⟨h3, e3⟩ := runs_blkGet h2
  exact ⟨h3, st_ext e1 e2 e3⟩

/-- A value read off the sub-proof's state, in a link. -/
theorem ask_L {α : Type} {f : Fork → Option α} {s : HasRuns.St LinkM} {a : α}
    {s' : HasRuns.St LinkM} (h : Runs (LinkM.sub (SubM.ask f)) s a s') :
    f s.2.1 = some a ∧ s' = s := by
  obtain ⟨h1, e1⟩ := runs_sub h
  obtain ⟨h2, e2⟩ := runs_ask h1
  exact ⟨h2, Prod.ext e1 e2⟩

/-- All calls of one run of Layer.runForkHidG2, in order. L F c: where the run began; L' F' c':
what it left. -/
structure LayRan (P : Layer.Pub) (hp : Layer.HPlan2) (g : Nat) (L : LinkCtx) (F : Fork) (c : Ctx)
    (L' : LinkCtx) (F' : Fork) (c' : Ctx) (iU3 : Nat) (fo : Forest.Heard) (o : Layer.Own)
    (F0 F1 F2 F3 : Fork) (L3 : LinkCtx) (c1 c2 c3 : Ctx) (tl1 tlA tl : HTailF2) (laid : Nat)
    (L4 L6 : LinkCtx)
    (F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25 F26 F27 F28
    F29 F30 F31 F32 F33 F34 : Fork)
    (c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28
    c29 c30 c31 c32 c33 c34 : Ctx) : Prop where
  cut : LayCut P hp g L F c iU3 fo o F0 F1 F2 F3 L3 c1 c2 c3
  closed : hp.tl.closeFuns o.funs = some tl1
  transcript : tl1.transcript L3 F3 c3 = .ok (((tlA, L4), F4), c4)
  slotCount : (F4.next == hp.used) = true
  setPlan : SubM.setPlanClaims hp.nLin F4 c4 = .ok (((), F5), c5)
  batch : t2Batch F4.next L4 F5 c5 = .ok ((((), L6), F6), c6)
  noteTheta :
    (get >>= fun s => Layer.note "the element that batches the claims" s.theta : SubM Unit) F6
      c6 = .ok (((), F7), c7)
  objects : Forest.objects o.H.fo F7 c7 = .ok (((), F8), c8)
  note1 : Layer.noteClaims "the look-up's own claims" F8 c8 = .ok (((), F9), c9)
  norms : Layer.claimsNorms P o.v o.H F9 c9 = .ok (((), F10), c10)
  note2 : Layer.noteClaims "the sums of squares" F10 c10 = .ok (((), F11), c11)
  rowBatch : Layer.claimRowBatch P.y o.H F11 c11 = .ok (((), F12), c12)
  ledger :
    (if (P.y.h.xl == 5) = true then Layer.claimsLedger5 o.v o.H
      else Layer.claimsLedger4 o.v o.H) F12 c12 = .ok (((), F13), c13)
  note3 : Layer.noteClaims "the norms' rows" F13 c13 = .ok (((), F14), c14)
  terms : Layer.claimsTerms o.v o.H F14 c14 = .ok (((), F15), c15)
  note4 : Layer.noteClaims "the second token sum-check's shown values" F15 c15 =
    .ok (((), F16), c16)
  gated : Layer.claimsGated P o.v o.hd o.hd2 F16 c16 = .ok (((), F17), c17)
  note5 : Layer.noteClaims "the gated products" F17 c17 = .ok (((), F18), c18)
  oneHot : Layer.claimsOneHot o.v F18 c18 = .ok (((), F19), c19)
  planes : Layer.claimsPlanes o.v o.H.fo F19 c19 = .ok (((), F20), c20)
  emb : ((g == 0) = true ∧
      Layer.claimEmbedding o.v o.H o.sVE F20 c20 = .ok (((), F21), c21)) ∨
    (¬ (g == 0) = true ∧ F21 = F20 ∧ c21 = c20)
  note6 : Layer.noteClaims "the planes and the embedding" F21 c21 = .ok (((), F22), c22)
  rowsBooked : (tlA.foldDrawn == 1) = true
  callsBooked : (1 + tlA.groupsRun == 2) = true
  objectsF : tlA.objectsF o.funs F22 c22 = .ok ((tl, F23), c23)
  note7 : Layer.noteClaims "the smallness test" F23 c23 = .ok (((), F24), c24)
  linRow : SubM.lin o.K.rowS F24 c24 = .ok (((), F25), c25)
  joinAdded : Forest.joinAdded o.H.fo F25 c25 = .ok (((), F26), c26)
  linA : SubM.lin (Aff.slot o.K.sA0 - o.K.fin.Alin) F26 c26 = .ok (((), F27), c27)
  linB : SubM.lin (Aff.slot o.K.sB0 - o.K.fin.Blin) F27 c27 = .ok (((), F28), c28)
  mergeLin : wsForkLin o.wo.toWsMerged F28 c28 = .ok (((), F29), c29)
  note8 : Layer.noteClaims "all claims" F29 c29 = .ok (((), F30), c30)
  freeSlot : Layer.freeSlotTest g hp.used o.wo.sFv F30 c30 = .ok (((), F31), c31)
  claimCount : (F31.nClaim == hp.nLin) = true
  held : tl.funsHeld o.funs = true
  selfTest : tl.selfTest hp.nU F31 c31 = .ok (((), F32), c32)
  coefficients : tl.coefficients F32 c32 = .ok (((), F33), c33)
  rkSelfTest : tl.rkSelfTest F33 c33 = .ok (((), F34), c34)
  laidIs : tl.equationsLaidF = some laid
  door : doorH laid L6 F34 c34 = .ok ((((), L'), F'), c')
  draws : (F'.nClaim == F'.planClaimsF) = true
  allTaken : (if F'.kapAllTakenF = true then some () else none) = some ()
  foldTaken : tl.foldAllTakenF = true
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
  v15 : c15.ch.dry = false
  v16 : c16.ch.dry = false
  v17 : c17.ch.dry = false
  v18 : c18.ch.dry = false
  v19 : c19.ch.dry = false
  v20 : c20.ch.dry = false
  v21 : c21.ch.dry = false
  v22 : c22.ch.dry = false
  v23 : c23.ch.dry = false
  v24 : c24.ch.dry = false
  v25 : c25.ch.dry = false
  v26 : c26.ch.dry = false
  v27 : c27.ch.dry = false
  v28 : c28.ch.dry = false
  v29 : c29.ch.dry = false
  v30 : c30.ch.dry = false
  v31 : c31.ch.dry = false
  v32 : c32.ch.dry = false
  v33 : c33.ch.dry = false
  v34 : c34.ch.dry = false
  vEnd : c'.ch.dry = false
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
  m15 : c'.failed = none → c15.failed = none
  m16 : c'.failed = none → c16.failed = none
  m17 : c'.failed = none → c17.failed = none
  m18 : c'.failed = none → c18.failed = none
  m19 : c'.failed = none → c19.failed = none
  m20 : c'.failed = none → c20.failed = none
  m21 : c'.failed = none → c21.failed = none
  m22 : c'.failed = none → c22.failed = none
  m23 : c'.failed = none → c23.failed = none
  m24 : c'.failed = none → c24.failed = none
  m25 : c'.failed = none → c25.failed = none
  m26 : c'.failed = none → c26.failed = none
  m27 : c'.failed = none → c27.failed = none
  m28 : c'.failed = none → c28.failed = none
  m29 : c'.failed = none → c29.failed = none
  m30 : c'.failed = none → c30.failed = none
  m31 : c'.failed = none → c31.failed = none
  m32 : c'.failed = none → c32.failed = none
  m33 : c'.failed = none → c33.failed = none
  m34 : c'.failed = none → c34.failed = none

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
/-- Layer.runForkHidG2, taken apart whole. -/
theorem layer_ran
    (hpad : ∀ (calls : Array Model.Call) (pub : Array Nat) (lid : Nat) (F G : Fork) (c c' : Ctx)
      (g : Forest.Heard), Forest.pad calls pub lid F c = .ok ((g, G), c') → Sized F → Sized G)
    (P : Layer.Pub) (hp : Layer.HPlan2) (g : Nat) {L L' : LinkCtx} {F F' : Fork} {c c' : Ctx}
    {wo : WsForkOut} (hd : c.ch.dry = false)
    (h0 : Layer.runForkHidG2 P hp g L F c = .ok (((wo, L'), F'), c')) :
    ∃ iU3 fo o F0 F1 F2 F3 L3 c1 c2 c3 tl1 tlA tl laid L4 L6 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14
    F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25 F26 F27 F28 F29 F30 F31 F32 F33 F34 c4 c5 c6 c7 c8
    c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32
    c33 c34,
      LayRan P hp g L F c L' F' c' iU3 fo o F0 F1 F2 F3 L3 c1 c2 c3 tl1 tlA tl laid L4 L6 F4 F5 F6
      F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25 F26 F27 F28 F29 F30
      F31 F32 F33 F34 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24
      c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 ∧ wo = o.wo := by
  have h : Runs (Layer.runForkHidG2 P hp g) (L, F, c) wo (L', F', c') := h0
  clear h0
  have d : View (m := LinkM) (L, F, c) := hd
  unfold Layer.runForkHidG2 at h
  peel3 h d
  · -- the first group: the claim on the embedding is added
    obtain ⟨t1, e⟩ := runs_get r1
    cases e
    obtain ⟨t2, e⟩ := mustAs_L r2
    cases e
    obtain ⟨t3, e⟩ := fork_L r3
    cases e
    obtain ⟨t4, e⟩ := linkMust_L r4
    cases e
    down_sub r5
    down_sub r6
    down_sub r7
    dsimp only at t1 t3 r5 r6 r7
    have t1' := t1.symm
    subst t1'
    have t3' := t3.symm
    subst t3'
    obtain ⟨q1, q2⟩ := runs_change r5
    have q1' : F.fillL.slots hp.ns = F5 := Option.some.inj q1
    dsimp only at q2
    subst q2
    unfold Layer.form SubM.get at r6
    obtain ⟨k1, k2⟩ := runs_lift (σ := Fork) r6
    obtain ⟨k3, k4⟩ := runs_blkGet k1
    dsimp only at k2 k4
    subst k2
    subst k4
    obtain ⟨fo, ⟨G1, e1⟩, h1, h2⟩ := HasRuns.runs_bind (m := SubM) r7
    have v1 : View (m := SubM) (G1, e1) := runs_view h1 d6
    have m1 : Clean (m := SubM) (F7, c7) → Clean (m := SubM) (G1, e1) := runs_clean h2
    unfold Layer.hearLook at h1
    obtain ⟨fo', ⟨G0, e0⟩, p1, p2⟩ := HasRuns.runs_bind (m := SubM) h1
    obtain ⟨u, ⟨G2, e2⟩, p3, p4⟩ := HasRuns.runs_bind (m := SubM) p2
    obtain ⟨p5, p6⟩ := HasRuns.runs_pure p4
    obtain ⟨p7, p8⟩ := runs_up p3
    obtain ⟨pk, p9⟩ := runs_mustAs p7
    have eG : G1 = G0 := (congrArg Prod.fst p6).trans p8
    have eE : e1 = e0 := (congrArg Prod.snd p6).trans p9
    subst p5
    subst eG
    subst eE
    have z0 : Sized F6 := q1' ▸ sized_slots _ _
    have cut := LayCut.mk (P := P) (hp := hp) (g := g) t2 t4 q1'.symm k3 p1 pk h2 r8 z0
      (hpad _ _ _ _ _ _ _ _ p1 z0)
    obtain ⟨t9, e⟩ := form_L r9
    cases e
    obtain ⟨t11, e⟩ := ask_L (f := fun F => some F.next) r11
    cases e
    have t11' := (Option.some.inj t11).symm
    dsimp only at t11'
    subst t11'
    obtain ⟨t12, e⟩ := mustAs_L r12
    cases e
    down_sub r13
    down_sub r15
    down_sub r16
    down_sub r17
    down_sub r18
    down_sub r19
    down_sub r20
    down_sub r21
    down_sub r22
    down_sub r23
    down_sub r24
    down_sub r25
    down_sub r26
    down_sub r27
    down_sub r28
    down_sub r29
    down_sub r30
    obtain ⟨t31, e⟩ := mustAs_L r31
    cases e
    obtain ⟨t32, e⟩ := mustAs_L r32
    cases e
    down r33
    down_sub r34
    down_sub r35
    down_sub r36
    down_sub r37
    down_sub r38
    down_sub r39
    down_sub r40
    down_sub r41
    obtain ⟨t42, e⟩ := fork_L r42
    cases e
    dsimp only at t42
    subst t42
    obtain ⟨t43, e⟩ := mustAs_L r43
    cases e
    obtain ⟨t44, e⟩ := linkMust_L r44
    cases e
    down r45
    down r46
    down r47
    obtain ⟨t48, e⟩ := form_L r48
    cases e
    obtain ⟨t50, e⟩ := fork_L r50
    cases e
    dsimp only at t50
    subst t50
    obtain ⟨t51, e⟩ := mustAs_L r51
    cases e
    obtain ⟨t52, e⟩ := ask_L (f := fun F => if F.kapAllTakenF then some () else none) r52
    cases e
    obtain ⟨t53, e⟩ := linkMust_L r53
    cases e
    obtain ⟨w1, e⟩ := HasRuns.runs_pure h
    cases e
    exact ⟨
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      { cut := cut,
        closed := t9, transcript := r10, slotCount := t12, setPlan := r13, batch := r14,
        noteTheta := r15, objects := r16, note1 := r17, norms := r18, note2 := r19, rowBatch := r20,
        ledger := r21, note3 := r22, terms := r23, note4 := r24, gated := r25, note5 := r26,
        oneHot := r27, planes := r28, emb := Or.inl ⟨by assumption, r29⟩, note6 := r30,
        rowsBooked := t31, callsBooked := t32, objectsF := r33, note7 := r34, linRow := r35,
        joinAdded := r36, linA := r37, linB := r38, mergeLin := r39, note8 := r40, freeSlot := r41,
        claimCount := t43, held := t44, selfTest := r45, coefficients := r46, rkSelfTest := r47,
        laidIs := t48, door := r49, draws := t51, allTaken := t52, foldTaken := t53, v4 := d10,
        v5 := d13, v6 := d14, v7 := d15, v8 := d16, v9 := d17, v10 := d18, v11 := d19, v12 := d20,
        v13 := d21, v14 := d22, v15 := d23, v16 := d24, v17 := d25, v18 := d26, v19 := d27,
        v20 := d28, v21 := d29, v22 := d30, v23 := d33, v24 := d34, v25 := d35, v26 := d36,
        v27 := d37, v28 := d38, v29 := d39, v30 := d40, v31 := d41, v32 := d45, v33 := d46,
        v34 := d47, vEnd := d49, m4 := b10, m5 := b13, m6 := b14, m7 := b15, m8 := b16, m9 := b17,
        m10 := b18, m11 := b19, m12 := b20, m13 := b21, m14 := b22, m15 := b23, m16 := b24,
        m17 := b25, m18 := b26, m19 := b27, m20 := b28, m21 := b29, m22 := b30, m23 := b33,
        m24 := b34, m25 := b35, m26 := b36, m27 := b37, m28 := b38, m29 := b39, m30 := b40,
        m31 := b41, m32 := b45, m33 := b46, m34 := b47,
        v1 := v1, v2 := d7, v3 := d8, m1 := fun k => m1 (b7 k), m2 := b7, m3 := b8 }, w1⟩
  · -- a later group
    obtain ⟨t1, e⟩ := runs_get r1
    cases e
    obtain ⟨t2, e⟩ := mustAs_L r2
    cases e
    obtain ⟨t3, e⟩ := fork_L r3
    cases e
    obtain ⟨t4, e⟩ := linkMust_L r4
    cases e
    down_sub r5
    down_sub r6
    down_sub r7
    dsimp only at t1 t3 r5 r6 r7
    have t1' := t1.symm
    subst t1'
    have t3' := t3.symm
    subst t3'
    obtain ⟨q1, q2⟩ := runs_change r5
    have q1' : F.fillL.slots hp.ns = F5 := Option.some.inj q1
    dsimp only at q2
    subst q2
    unfold Layer.form SubM.get at r6
    obtain ⟨k1, k2⟩ := runs_lift (σ := Fork) r6
    obtain ⟨k3, k4⟩ := runs_blkGet k1
    dsimp only at k2 k4
    subst k2
    subst k4
    obtain ⟨fo, ⟨G1, e1⟩, h1, h2⟩ := HasRuns.runs_bind (m := SubM) r7
    have v1 : View (m := SubM) (G1, e1) := runs_view h1 d6
    have m1 : Clean (m := SubM) (F7, c7) → Clean (m := SubM) (G1, e1) := runs_clean h2
    unfold Layer.hearLook at h1
    obtain ⟨fo', ⟨G0, e0⟩, p1, p2⟩ := HasRuns.runs_bind (m := SubM) h1
    obtain ⟨u, ⟨G2, e2⟩, p3, p4⟩ := HasRuns.runs_bind (m := SubM) p2
    obtain ⟨p5, p6⟩ := HasRuns.runs_pure p4
    obtain ⟨p7, p8⟩ := runs_up p3
    obtain ⟨pk, p9⟩ := runs_mustAs p7
    have eG : G1 = G0 := (congrArg Prod.fst p6).trans p8
    have eE : e1 = e0 := (congrArg Prod.snd p6).trans p9
    subst p5
    subst eG
    subst eE
    have z0 : Sized F6 := q1' ▸ sized_slots _ _
    have cut := LayCut.mk (P := P) (hp := hp) (g := g) t2 t4 q1'.symm k3 p1 pk h2 r8 z0
      (hpad _ _ _ _ _ _ _ _ p1 z0)
    obtain ⟨t9, e⟩ := form_L r9
    cases e
    obtain ⟨t11, e⟩ := ask_L (f := fun F => some F.next) r11
    cases e
    have t11' := (Option.some.inj t11).symm
    dsimp only at t11'
    subst t11'
    obtain ⟨t12, e⟩ := mustAs_L r12
    cases e
    down_sub r13
    down_sub r15
    down_sub r16
    down_sub r17
    down_sub r18
    down_sub r19
    down_sub r20
    down_sub r21
    down_sub r22
    down_sub r23
    down_sub r24
    down_sub r25
    down_sub r26
    down_sub r27
    down_sub r28
    obtain ⟨_, e⟩ := HasRuns.runs_pure r29
    cases e
    down_sub r30
    obtain ⟨t31, e⟩ := mustAs_L r31
    cases e
    obtain ⟨t32, e⟩ := mustAs_L r32
    cases e
    down r33
    down_sub r34
    down_sub r35
    down_sub r36
    down_sub r37
    down_sub r38
    down_sub r39
    down_sub r40
    down_sub r41
    obtain ⟨t42, e⟩ := fork_L r42
    cases e
    dsimp only at t42
    subst t42
    obtain ⟨t43, e⟩ := mustAs_L r43
    cases e
    obtain ⟨t44, e⟩ := linkMust_L r44
    cases e
    down r45
    down r46
    down r47
    obtain ⟨t48, e⟩ := form_L r48
    cases e
    obtain ⟨t50, e⟩ := fork_L r50
    cases e
    dsimp only at t50
    subst t50
    obtain ⟨t51, e⟩ := mustAs_L r51
    cases e
    obtain ⟨t52, e⟩ := ask_L (f := fun F => if F.kapAllTakenF then some () else none) r52
    cases e
    obtain ⟨t53, e⟩ := linkMust_L r53
    cases e
    obtain ⟨w1, e⟩ := HasRuns.runs_pure h
    cases e
    exact ⟨
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      { cut := cut,
        closed := t9, transcript := r10, slotCount := t12, setPlan := r13, batch := r14,
        noteTheta := r15, objects := r16, note1 := r17, norms := r18, note2 := r19, rowBatch := r20,
        ledger := r21, note3 := r22, terms := r23, note4 := r24, gated := r25, note5 := r26,
        oneHot := r27, planes := r28, emb := Or.inr ⟨by assumption, rfl, rfl⟩, note6 := r30,
        rowsBooked := t31, callsBooked := t32, objectsF := r33, note7 := r34, linRow := r35,
        joinAdded := r36, linA := r37, linB := r38, mergeLin := r39, note8 := r40, freeSlot := r41,
        claimCount := t43, held := t44, selfTest := r45, coefficients := r46, rkSelfTest := r47,
        laidIs := t48, door := r49, draws := t51, allTaken := t52, foldTaken := t53, v4 := d10,
        v5 := d13, v6 := d14, v7 := d15, v8 := d16, v9 := d17, v10 := d18, v11 := d19, v12 := d20,
        v13 := d21, v14 := d22, v15 := d23, v16 := d24, v17 := d25, v18 := d26, v19 := d27,
        v20 := d28, v21 := d29, v22 := d30, v23 := d33, v24 := d34, v25 := d35, v26 := d36,
        v27 := d37, v28 := d38, v29 := d39, v30 := d40, v31 := d41, v32 := d45, v33 := d46,
        v34 := d47, vEnd := d49, m4 := b10, m5 := b13, m6 := b14, m7 := b15, m8 := b16, m9 := b17,
        m10 := b18, m11 := b19, m12 := b20, m13 := b21, m14 := b22, m15 := b23, m16 := b24,
        m17 := b25, m18 := b26, m19 := b27, m20 := b28, m21 := b29, m22 := b30, m23 := b33,
        m24 := b34, m25 := b35, m26 := b36, m27 := b37, m28 := b38, m29 := b39, m30 := b40,
        m31 := b41, m32 := b45, m33 := b46, m34 := b47,
        v1 := v1, v2 := d7, v3 := d8, m1 := fun k => m1 (b7 k), m2 := b7, m3 := b8 }, w1⟩

end OnBytes.L5.LayerRan

#print axioms OnBytes.L5.LayerRan.layer_ran
