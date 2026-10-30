-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndHeadRan.lean: the check of the head's sub-proof (`Head.runForkHidH2`,
OnBytes/Model/Head.lean), taken apart whole, with the routines `Head.walk` and `Head.selfTests`
opened too.

Definitions and theorems with their proofs. If the check returns from the link's state L, the
sub-proof's state F and a context c that is no dry run, then every call of the three routines has
returned, the first from L, F, c, each later one from what the one before has left. The record
`HeadRan` has one field for each call, in the routines' order: a bare run for a call that may change
something; for a test or a read that leaves all as it was: what it tested, or the value in place of
a letter. It does for the head what OnBytes/Tie/Pv/Keeps/KeepsChainA2.lean does for attention and
OnBytes/Tie/Pv/Keeps/LayerRan.lean for the layers.

Main names:
  `stepMust`, `stepTest`, `stepGetAs`, `stepGet`, `stepFork`, `stepChange`, `stepSlot`, `stepAsk`,
    `stepS`: a run of «x, then f» for the kinds of call that the three routines make.
  `HeadRan`: all calls of one run, in order; every context that the run passes is no dry run (v).
  `head_ran_whole`: `Head.runForkHidH2`, taken apart whole.

Limits: one direction: from a run that returns. Nothing is said on what a call does. Nothing on the
marks of failed named tests.


-/
import OnBytes.Tie.Pv.Tail.EndFirst
import OnBytes.Tie.Pv.Tail.EndTested
import OnBytes.Tie.Pv.Tail.EndViews

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port OnBytes.Tie.Pv.Tail.Walk OnBytes.L5

section
variable {β : Type} {L : LinkCtx} {F : Fork} {c : Ctx} {r : ((β × LinkCtx) × Fork) × Ctx}

/-- A public condition, then f. -/
theorem stepMust {name : String} {b : Bool} {f : Unit → LinkM β}
    (h : ((liftM (mustAs name b) : LinkM Unit) >>= f) L F c = .ok r) :
    b = true ∧ f () L F c = .ok r := by
  obtain ⟨u, L1, F1, c1, a1, a2⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨a3, e1, e2⟩ := liftBlkL_ok _ _ _ _ _ _ _ _ a1
  obtain ⟨hb, e3⟩ := (Port.mustAs_ok _ _ _ _ _).1 a3
  rw [e1, e2, e3] at a2
  exact ⟨hb, a2⟩

/-- A condition on values, on a view, then f. -/
theorem stepTest {name : String} {b : Bool} {f : Unit → LinkM β}
    (h : ((liftM (testAs name b) : LinkM Unit) >>= f) L F c = .ok r) (d : c.ch.dry = false) :
    b = true ∧ f () L F c = .ok r := by
  obtain ⟨u, L1, F1, c1, a1, a2⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨a3, e1, e2⟩ := liftBlkL_ok _ _ _ _ _ _ _ _ a1
  obtain ⟨hb, e3⟩ := (testAs_ok _ _ _ _ _ d).1 a3
  rw [e1, e2, e3] at a2
  exact ⟨hb, a2⟩

/-- A value that must be there, then f. -/
theorem stepGetAs {α : Type} {name : String} {x : Option α} {f : α → LinkM β}
    (h : ((liftM (Head.getAs name x) : LinkM α) >>= f) L F c = .ok r) :
    ∃ a, x = some a ∧ f a L F c = .ok r := by
  obtain ⟨a, L1, F1, c1, a1, a2⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨a3, e1, e2⟩ := liftBlkL_ok _ _ _ _ _ _ _ _ a1
  obtain ⟨hx, e3⟩ := getAs_ok _ _ _ _ _ a3
  rw [e1, e2, e3] at a2
  exact ⟨a, hx, a2⟩

/-- Reading the link's state, then f. -/
theorem stepGet {f : LinkCtx → LinkM β} (h : ((get : LinkM LinkCtx) >>= f) L F c = .ok r) :
    f L L F c = .ok r := by
  obtain ⟨x, L1, F1, c1, a1, a2⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨e0, e1, e2, e3⟩ := (getL_ok _ _ _ _ _ _ _).1 a1
  rw [e0, e1, e2, e3] at a2
  exact a2

/-- Reading the sub-proof's state, then f. -/
theorem stepFork {f : Fork → LinkM β} (h : (LinkM.fork >>= f) L F c = .ok r) :
    f F L F c = .ok r := by
  obtain ⟨x, L1, F1, c1, a1, a2⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨a3, e1⟩ := (subL_ok _ _ _ _ _ _ _ _).1 a1
  obtain ⟨e0, e2, e3⟩ := (Port.ask_ok _ _ _ _ _ _).1 a3
  rw [← Option.some.inj e0, e1, e2, e3] at a2
  exact a2

/-- A step on the state that always returns, then f. -/
theorem stepChange {g : Fork → Fork} {f : Unit → LinkM β}
    (h : (LinkM.sub (SubM.change fun F => some (g F)) >>= f) L F c = .ok r) :
    f () L (g F) c = .ok r := by
  obtain ⟨u, L1, F1, c1, a1, a2⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨a3, e1⟩ := (subL_ok _ _ _ _ _ _ _ _).1 a1
  obtain ⟨H, hH, e⟩ := (OnBytes.PscRun.change_ok _ F c _).1 a3
  have e2 : F1 = H := congrArg (fun z : (Unit × Fork) × Ctx => z.1.2) e
  have e3 : c1 = c := congrArg (fun z : (Unit × Fork) × Ctx => z.2) e
  rw [e1, e2, e3, ← Option.some.inj hH] at a2
  exact a2

/-- Reading a value off the sub-proof's state, then f. -/
theorem stepAsk {α : Type} {g : Fork → Option α} {f : α → LinkM β}
    (h : ((liftM (SubM.ask g) : LinkM α) >>= f) L F c = .ok r) :
    ∃ a, g F = some a ∧ f a L F c = .ok r := by
  obtain ⟨a, L1, F1, c1, a1, a2⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨a3, e1⟩ := liftSubL_ok _ _ _ _ _ _ _ _ a1
  obtain ⟨e0, e2, e3⟩ := (Port.ask_ok _ _ _ _ _ _).1 a3
  rw [e1, e2, e3] at a2
  exact ⟨a, e0, a2⟩

/-- Reading the number of slots taken, then f. -/
theorem stepSlot {f : Nat → LinkM β} (h : ((liftM SubM.slot : LinkM Nat) >>= f) L F c = .ok r) :
    f F.next L F c = .ok r := by
  obtain ⟨a, e, a2⟩ := stepAsk (g := fun F => some F.next) h
  rw [← Option.some.inj e] at a2
  exact a2

/-- A routine of the sub-proof, on a view, then f. -/
theorem stepS {α : Type} {x : SubM α} {f : α → LinkM β} (hk : KeepsM (liftM x : LinkM α))
    (h : ((liftM x : LinkM α) >>= f) L F c = .ok r) (d : c.ch.dry = false) :
    ∃ a F1 c1, x F c = .ok ((a, F1), c1) ∧ c1.ch.dry = false ∧ f a L F1 c1 = .ok r := by
  obtain ⟨a, L1, F1, c1, a1, d1, a2⟩ := bindV hk h d
  obtain ⟨a3, e1⟩ := liftSubL_ok _ _ _ _ _ _ _ _ a1
  rw [e1] at a2
  exact ⟨a, F1, c1, a3, d1, a2⟩

end

/-- All calls of one run of `Head.runForkHidH2`, in order. L F c: where the run began; L' F' c':
what it left. -/
structure HeadRan (hS : Head.Shape) (Lh : Head.HL) (b : Head.Border) (hp : Head.HPlanH2)
    (O : Head.Owner) (cov : Head.Covered) (wsLay : WsLay) (L : LinkCtx) (F : Fork) (c : Ctx)
    (wo : WsForkOut) (L' : LinkCtx) (F' : Fork) (c' : Ctx) (iU3 : Nat) (x : Head.Heard)
    (t : Head.Tables) (Rn : Head.Run) (claim : WsClaim) (tl1 tlA tl : HTailF2) (laid : Nat)
    (L2 L4 L8 : LinkCtx)
   (F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25
    F26 F27 F28 F29 F30 F31 : Fork)
   (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26
    c27 c28 c29 c30 c31 : Ctx) : Prop where
  covered : cov.sized hS.T = true
  handed : Head.planHanded hp L.list F = true
  start : F0 = ({ trees := F.trees } : Fork).fillL
  owner : (!O.tl.ix.TX.isEmpty && O.tl.kTX.back? == some b.kxb) = true
  reads : hp.tl.ix.U.getD 2 none = some iU3
  run : Rn = { h := hS, L := Lh, b := b, hp := hp, cov := cov, x := x, t := t, iU3 := iU3 }
  hear : Head.hear hS Lh hp cov L.check.plain F0 c = .ok ((x, F1), c1)
  root : rootInH [iU3] L F1 c1 = .ok ((((), L2), F2), c2)
  tables : Head.tablesOf hS Lh hp cov x F2 c2 = .ok ((t, F3), c3)
  closed : hp.tl.closeFuns t.funs = some tl1
  transcript : tl1.transcript L2 F3 c3 = .ok (((tlA, L4), F4), c4)
  weights : Head.weightsClaim Rn wsLay F4 c4 = .ok ((claim, F5), c5)
  one : (hp.NCL == 1) = true
  merge : wsForkEnd wsLay #[claim] #[x.sV] F5 c5 = .ok ((wo, F6), c6)
  slotCount : (F6.next == hp.nMsg) = true
  setPlan : SubM.setPlanClaims hp.nLin F6 c6 = .ok (((), F7), c7)
  batch : t2Batch F6.next L4 F7 c7 = .ok ((((), L8), F8), c8)
  objects : Forest.objects Rn.x.g1 F8 c8 = .ok (((), F9), c9)
  note1 : Head.noteConstant "the look-up's claims on mask entries" F9 c9 = .ok (((), F10), c10)
  squares : Head.claimSquares Rn F10 c10 = .ok (((), F11), c11)
  note2 : Head.noteConstant "the sum of squares" F11 c11 = .ok (((), F12), c12)
  ledger : Head.claimLedger Rn F12 c12 = .ok (((), F13), c13)
  note3 : Head.noteConstant "the row ledger" F13 c13 = .ok (((), F14), c14)
  stream : Head.claimStream Rn F14 c14 = .ok (((), F15), c15)
  note4 : Head.noteConstant "the stream times the reciprocal" F15 c15 = .ok (((), F16), c16)
  join : Head.claimJoin Rn F16 c16 = .ok (((), F17), c17)
  note5 : Head.noteConstant "the look-up's join" F17 c17 = .ok (((), F18), c18)
  policy : Head.claimPolicy Rn F18 c18 = .ok (((), F19), c19)
  note6 : Head.noteConstant "the acceptance policy" F19 c19 = .ok (((), F20), c20)
  planes : Head.claimPlanes Rn F20 c20 = .ok (((), F21), c21)
  note7 : Head.noteConstant "the look-up's planes" F21 c21 = .ok (((), F22), c22)
  objectsF : tlA.objectsF Rn.t.funs F22 c22 = .ok ((tl, F23), c23)
  note8 : Head.noteConstant "the smallness test" F23 c23 = .ok (((), F24), c24)
  logits : Head.claimLogits Rn F24 c24 = .ok (((), F25), c25)
  note9 : Head.noteConstant "the logits" F25 c25 = .ok (((), F26), c26)
  mergeLin : wsForkLin wo.toWsMerged F26 c26 = .ok (((), F27), c27)
  note10 : Head.noteConstant "the merge" F27 c27 = .ok (((), F28), c28)
  freeSlot : ((List.range Rn.hp.nMsg).all fun j =>
    isZeroE (F28.LS.getD j zeroE) == (j == wo.sFv)) = true
  claimCount : (F28.nClaim == Rn.hp.nLin) = true
  rowsBooked : (tl.foldDrawn == 1) = true
  callsBooked : (1 + tl.groupsRun == 2) = true
  held : tl.funsHeld Rn.t.funs = true
  selfTest : tl.selfTest Rn.hp.nU F28 c28 = .ok (((), F29), c29)
  coefficients : tl.coefficients F29 c29 = .ok (((), F30), c30)
  rkSelfTest : tl.rkSelfTest F30 c30 = .ok (((), F31), c31)
  laidIs : tl.equationsLaidF = some laid
  door : doorH laid L8 F31 c31 = .ok ((((), L'), F'), c')
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
  vEnd : c'.ch.dry = false

/-- `Head.runForkHidH2`, taken apart whole. -/
theorem head_ran_whole (hS : Head.Shape) (Lh : Head.HL) (b : Head.Border) (hp : Head.HPlanH2)
    (O : Head.Owner) (cov : Head.Covered) (wsLay : WsLay) (L L' : LinkCtx) (F F' : Fork)
    (c c' : Ctx) (wo : WsForkOut)
    (h : Head.runForkHidH2 hS Lh b hp O cov wsLay L F c = .ok (((wo, L'), F'), c'))
    (d : c.ch.dry = false) :
   ∃ iU3 x t Rn claim tl1 tlA tl laid L2 L4 L8 F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14
    F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25 F26 F27 F28 F29 F30 F31 c1 c2 c3 c4 c5 c6 c7 c8 c9
    c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31,
     HeadRan hS Lh b hp O cov wsLay L F c wo L' F' c' iU3 x t Rn claim tl1 tlA tl laid L2 L4 L8 F0
      F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25
      F26 F27 F28 F29 F30 F31 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19
      c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 := by
  have h0 := h
  clear h
  unfold Head.runForkHidH2 at h0
  obtain ⟨t1, h1⟩ := stepMust h0
  clear h0
  have h2 := stepGet h1
  clear h1
  have h3 := stepFork h2
  clear h2
  obtain ⟨t2, h4⟩ := stepMust h3
  clear h3
  have h5 := stepChange h4
  clear h4
  obtain ⟨t3, h6⟩ := stepMust h5
  clear h5
  obtain ⟨iU3, t4, h7⟩ := stepGetAs h6
  clear h6
  obtain ⟨x, F1, c1, r1, d1, h8⟩ := stepS (by keepsM) h7 d
  clear h7
  obtain ⟨_, L2, F2, c2, r2, d2, h9⟩ := bindV (by keepsM) h8 d1
  clear h8
  obtain ⟨t, F3, c3, r3, d3, h10⟩ := stepS (by keepsM) h9 d2
  clear h9
  obtain ⟨tl1, t5, h11⟩ := stepGetAs h10
  clear h10
  obtain ⟨tlA, L4, F4, c4, r4, d4, h12⟩ := bindV (by keepsM) h11 d3
  clear h11
  obtain ⟨claim, F5, c5, r5, d5, h13⟩ := stepS (by keepsM) h12 d4
  clear h12
  obtain ⟨t6, h14⟩ := stepMust h13
  clear h13
  obtain ⟨wo1, F6, c6, r6, d6, h15⟩ := stepS (by keepsM) h14 d5
  clear h14
  have h16 := stepSlot h15
  clear h15
  obtain ⟨t7, h17⟩ := stepMust h16
  clear h16
  obtain ⟨_, F7, c7, r7, d7, h18⟩ := stepS (by keepsM) h17 d6
  clear h17
  obtain ⟨_, L8, F8, c8, r8, d8, h19⟩ := bindV (by keepsM) h18 d7
  clear h18
  obtain ⟨tl, Lw, F28, c28, hw1, d28, h20⟩ := bindV (by keepsM) h19 d8
  clear h19
  obtain ⟨_, Ls, F31, c31, hs1, d31, h21⟩ := bindV (by keepsM) h20 d28
  clear h20
  unfold Head.walk at hw1
  obtain ⟨_, F9, c9, r9, d9, hw2⟩ := stepS (by keepsM) hw1 d8
  clear hw1
  obtain ⟨_, F10, c10, r10, d10, hw3⟩ := stepS (by keepsM) hw2 d9
  clear hw2
  obtain ⟨_, F11, c11, r11, d11, hw4⟩ := stepS (by keepsM) hw3 d10
  clear hw3
  obtain ⟨_, F12, c12, r12, d12, hw5⟩ := stepS (by keepsM) hw4 d11
  clear hw4
  obtain ⟨_, F13, c13, r13, d13, hw6⟩ := stepS (by keepsM) hw5 d12
  clear hw5
  obtain ⟨_, F14, c14, r14, d14, hw7⟩ := stepS (by keepsM) hw6 d13
  clear hw6
  obtain ⟨_, F15, c15, r15, d15, hw8⟩ := stepS (by keepsM) hw7 d14
  clear hw7
  obtain ⟨_, F16, c16, r16, d16, hw9⟩ := stepS (by keepsM) hw8 d15
  clear hw8
  obtain ⟨_, F17, c17, r17, d17, hw10⟩ := stepS (by keepsM) hw9 d16
  clear hw9
  obtain ⟨_, F18, c18, r18, d18, hw11⟩ := stepS (by keepsM) hw10 d17
  clear hw10
  obtain ⟨_, F19, c19, r19, d19, hw12⟩ := stepS (by keepsM) hw11 d18
  clear hw11
  obtain ⟨_, F20, c20, r20, d20, hw13⟩ := stepS (by keepsM) hw12 d19
  clear hw12
  obtain ⟨_, F21, c21, r21, d21, hw14⟩ := stepS (by keepsM) hw13 d20
  clear hw13
  obtain ⟨_, F22, c22, r22, d22, hw15⟩ := stepS (by keepsM) hw14 d21
  clear hw14
  obtain ⟨tl', F23, c23, r23, d23, hw16⟩ := stepS (by keepsM) hw15 d22
  clear hw15
  obtain ⟨_, F24, c24, r24, d24, hw17⟩ := stepS (by keepsM) hw16 d23
  clear hw16
  obtain ⟨_, F25, c25, r25, d25, hw18⟩ := stepS (by keepsM) hw17 d24
  clear hw17
  obtain ⟨_, F26, c26, r26, d26, hw19⟩ := stepS (by keepsM) hw18 d25
  clear hw18
  obtain ⟨_, F27, c27, r27, d27, hw20⟩ := stepS (by keepsM) hw19 d26
  clear hw19
  obtain ⟨_, F28', c28', r28, -, hw21⟩ := stepS (by keepsM) hw20 d27
  clear hw20
  obtain ⟨rfl, rfl, rfl, rfl⟩ := (pureL_ok _ _ _ _ _ _ _ _).1 hw21
  unfold Head.selfTests at hs1
  have hs2 := stepFork hs1
  clear hs1
  obtain ⟨t8, hs3⟩ := stepTest hs2 d28
  clear hs2
  obtain ⟨t9, hs4⟩ := stepMust hs3
  clear hs3
  obtain ⟨t10, hs5⟩ := stepMust hs4
  clear hs4
  obtain ⟨t11, hs6⟩ := stepMust hs5
  clear hs5
  obtain ⟨t12, hs7⟩ := stepMust hs6
  clear hs6
  obtain ⟨_, F29, c29, r29, d29, hs8⟩ := stepS (by keepsM) hs7 d28
  clear hs7
  obtain ⟨_, F30, c30, r30, d30, hs9⟩ := stepS (by keepsM) hs8 d29
  clear hs8
  obtain ⟨r31, rfl⟩ := liftSubL_ok _ _ _ _ _ _ _ _ hs9
  obtain ⟨laid, t13, h22⟩ := stepGetAs h21
  clear h21
  obtain ⟨_, L9, F9', c9', r32, d32, h23⟩ := bindV (by keepsM) h22 d31
  clear h22
  have h24 := stepFork h23
  clear h23
  obtain ⟨t14, h25⟩ := stepMust h24
  clear h24
  obtain ⟨_, t15, h26⟩ :=
    stepAsk (g := fun F => if F.kapAllTakenF = true then some () else none) h25
  clear h25
  obtain ⟨t16, h27⟩ := stepMust h26
  clear h26
  obtain ⟨rfl, rfl, rfl, rfl⟩ := (pureL_ok _ _ _ _ _ _ _ _).1 h27
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _,
   { covered := t1, handed := t2, start := rfl, owner := t3, reads := t4, run := rfl, hear := r1,
      root := r2, tables := r3, closed := t5, transcript := r4, weights := r5, one := t6, merge :=
      r6, slotCount := t7, setPlan := r7, batch := r8, objects := r9, note1 := r10, squares :=
      r11, note2 := r12, ledger := r13, note3 := r14, stream := r15, note4 := r16, join := r17,
      note5 := r18, policy := r19, note6 := r20, planes := r21, note7 := r22, objectsF := r23,
      note8 := r24, logits := r25, note9 := r26, mergeLin := r27, note10 := r28, freeSlot := t8,
      claimCount := t9, rowsBooked := t10, callsBooked := t11, held := t12, selfTest := r29,
      coefficients := r30, rkSelfTest := r31, laidIs := t13, door := r32, draws := t14, allTaken
      := t15, foldTaken := t16, v1 := d1, v2 := d2, v3 := d3, v4 := d4, v5 := d5, v6 := d6, v7 :=
      d7, v8 := d8, v9 := d9, v10 := d10, v11 := d11, v12 := d12, v13 := d13, v14 := d14, v15 :=
      d15, v16 := d16, v17 := d17, v18 := d18, v19 := d19, v20 := d20, v21 := d21, v22 := d22, v23
      := d23, v24 := d24, v25 := d25, v26 := d26, v27 := d27, v28 := d28, v29 := d29, v30 := d30,
      v31 := d31, vEnd := d32 }⟩

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.head_ran_whole
