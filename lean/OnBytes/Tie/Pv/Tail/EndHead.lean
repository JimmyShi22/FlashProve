-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndHead.lean: the premise `RawRows` of the theorems on what objectsF adds
(OnBytes/Tie/Pv/Tail/EndAll.lean, EndSpread.lean), at the check of the head's sub-proof
(`Head.runForkHidH2`, OnBytes/Model/Head.lean), from the runs of the check's own calls.

Definitions, and theorems with their proofs.

Main names:
  `presL_liftSub`, `presL_liftBlk`: routines of the sub-proof and blocks, lifted into a routine that
    also calls the chain, as the texts of the checks write them.
  `peel`: a run of «x, then f», where x keeps R: f has run from a state that stands in R to the
    first.
  `head_walk_ran`: a run of `Head.walk` holds a run of objectsF; shapes and batching element are
    kept before it and after it.
  `head_selfTests_ran`: a run of `Head.selfTests` holds the runs of the routine that sets the row
    weights and of the test of the weights, from the state and in the context in which it began.
  `rawRows_head_runs`: `RawRows` as the theorems on objectsF ask it.

Limits: the premises on the plan stay: the run of addTreesF, that the plan's record has its arrays'
numbers, blocks and lengths (`RecordKept`), and that the check begins at a state with the shapes
that addTreesF left (`ShapesKept`). `Head.selfTests` must begin on a view, not in a dry run. That a
run of `Head.runForkHidH2` is made of the runs that are premises here is not shown.


-/
import OnBytes.Tie.Pv.Tail.EndWalkHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Walk
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail

variable {R : Fork → Fork → Prop}

/-- A routine of the sub-proof, lifted. -/
instance presL_liftSub {α : Type} (x : SubM α) [Pres R x] : PresL R (liftM x : LinkM α) :=
  presL_sub x

/-- The same, in the second spelling. -/
instance presL_liftSubS {α : Type} (x : SubM α) [Pres R x] : PresL R (StateT.lift x : LinkM α) :=
  presL_sub x

/-- A block, lifted twice. -/
instance presL_liftBlk [Prim R] {α : Type} (b : Blk α) : PresL R (liftM b : LinkM α) :=
  presL_sub (StateT.lift b)

/-- `Head.walk` keeps R. -/
instance presL_Model_Head_walk [Prim R] (Rn : OnBytes.Model.Head.Run) (tl : HTailF2)
    (wo : WsForkOut) : PresL R (OnBytes.Model.Head.walk Rn tl wo) := by
  unfold OnBytes.Model.Head.walk
  walkL

/-- `Head.selfTests` keeps R. -/
instance presL_Model_Head_selfTests [Prim R] (Rn : OnBytes.Model.Head.Run) (tl : HTailF2)
    (wo : WsForkOut) : PresL R (OnBytes.Model.Head.selfTests Rn tl wo) := by
  unfold OnBytes.Model.Head.selfTests
  walkL

/-- A run of «x, then f», where x keeps R: f has run from a state that stands in R to the first. -/
theorem peel {α β : Type} {x : LinkM α} {f : α → LinkM β} [hx : PresL R x] {L : LinkCtx} {F : Fork}
    {c : Ctx} {r : ((β × LinkCtx) × Fork) × Ctx} (h : (x >>= f) L F c = .ok r) :
    ∃ a L1 F1 c1, R F F1 ∧ f a L1 F1 c1 = .ok r := by
  obtain ⟨a, L1, F1, c1, h1, h2⟩ := (bindL_ok _ _ _ _ _ _).1 h
  exact ⟨a, L1, F1, c1, hx.out _ _ _ _ _ _ _ h1, h2⟩

/-- A block that is lifted twice leaves the link's and the sub-proof's state. -/
theorem liftBlkL_ok {α : Type} (b : Blk α) (L L' : LinkCtx) (F G : Fork) (c c' : Ctx) (a : α)
    (h : (liftM b : LinkM α) L F c = .ok (((a, L'), G), c')) :
    b c = .ok (a, c') ∧ L' = L ∧ G = F := by
  have h1 : LinkM.sub (StateT.lift b : SubM α) L F c = .ok (((a, L'), G), c') := h
  obtain ⟨h2, rfl⟩ := (subL_ok _ _ _ _ _ _ _ _).1 h1
  obtain ⟨x, c1, hb, e⟩ := (OnBytes.PscRun.lift_ok b F c ((a, G), c')).1 h2
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
  exact ⟨hb, rfl, rfl⟩

/-- A routine of the sub-proof that is lifted leaves the link's state. -/
theorem liftSubL_ok {α : Type} (x : SubM α) (L L' : LinkCtx) (F G : Fork) (c c' : Ctx) (a : α)
    (h : (liftM x : LinkM α) L F c = .ok (((a, L'), G), c')) :
    x F c = .ok ((a, G), c') ∧ L' = L :=
  (subL_ok x L L' F G c c' a).1 h

/-- A run of `Head.walk` holds a run of objectsF; shapes and batching element are kept before it and
after it. -/
theorem head_walk_ran (Rn : OnBytes.Model.Head.Run) (tl tl' : HTailF2) (wo : WsForkOut)
    (L L' : LinkCtx) (F G' : Fork) (c c' : Ctx)
    (h : OnBytes.Model.Head.walk Rn tl wo L F c = .ok (((tl', L'), G'), c')) :
    ∃ F7 c7 G c9, FrameKept F F7 ∧ tl.objectsF Rn.t.funs F7 c7 = .ok ((tl', G), c9) ∧
      FrameKept G G' := by
  unfold OnBytes.Model.Head.walk at h
  obtain ⟨_, _, _, _, k1, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k2, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k3, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k4, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k5, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k6, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k7, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k8, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k9, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k10, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k11, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k12, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k13, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k14, h⟩ := peel (R := FrameKept) h
  obtain ⟨tl1, L15, G, c15, ho, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨ho, -⟩ := liftSubL_ok _ _ _ _ _ _ _ _ ho
  obtain ⟨_, _, _, _, k15, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k16, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k17, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k18, h⟩ := peel (R := FrameKept) h
  obtain ⟨_, _, _, _, k19, h⟩ := peel (R := FrameKept) h
  obtain ⟨rfl, -, rfl, -⟩ := (pureL_ok _ _ _ _ _ _ _ _).1 h
  exact ⟨_, _, _, _, (((((((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans
    k7).trans k8).trans k9).trans k10).trans k11).trans k12).trans k13).trans k14), ho,
    ((((k15.trans k16).trans k17).trans k18).trans k19)⟩

/-- The test that no column that is meant to be read has the weight 0 leaves state and context. -/
theorem selfTestF_both (tl : HTailF2) (nU : Array Nat) (F G : Fork) (c c' : Ctx)
    (h : tl.selfTestF nU F c = .ok (((), G), c')) : G = F ∧ c' = c := by
  refine ⟨selfTestF_same tl nU F G c c' h, ?_⟩
  unfold HTailF2.selfTestF at h
  rw [Port.bind_ok] at h
  obtain ⟨_, F1, c1, h1, h⟩ := h
  obtain ⟨-, rfl, rfl⟩ := (Port.ask_ok _ _ _ _ _ _).1 h1
  rw [Port.bind_ok] at h
  obtain ⟨_, F2, c2, h2, h⟩ := h
  obtain ⟨-, e⟩ := (OnBytes.PscRun.must_ok _ _ _ _).1 h2
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
  simp only [Port.bind_ok, Port.lift_ok] at h
  obtain ⟨_, _, _, ⟨b1, rfl⟩, _, _, _, ⟨b2, rfl⟩, b3, rfl⟩ := h
  have e1 := Port.testAs_ctx _ _ _ _ _ b1
  subst e1
  obtain ⟨-, rfl⟩ := (Port.mustAs_ok _ _ _ _ _).1 b2
  exact Port.testAs_ctx _ _ _ _ _ b3

/-- A run of `Head.selfTests` holds the runs of the routine that sets the row weights and of the
test of the weights, from the state and in the context in which it began. -/
theorem head_selfTests_ran (Rn : OnBytes.Model.Head.Run) (tl : HTailF2) (wo : WsForkOut)
    (L L' : LinkCtx) (F G : Fork) (c c' : Ctx)
    (h : OnBytes.Model.Head.selfTests Rn tl wo L F c = .ok ((((), L'), G), c')) :
    ∃ F2, tl.coefficientsF F c = .ok (((), F2), c) ∧ tl.tileSelfTestF F2 c = .ok (((), G), c') := by
  unfold OnBytes.Model.Head.selfTests at h
  obtain ⟨F0, L1, F1, c1, h1, r1⟩ := (bindL_ok _ _ _ _ _ _).1 h
  clear h
  obtain ⟨a1, e1⟩ := (subL_ok _ _ _ _ _ _ _ _).1 h1
  clear h1
  obtain ⟨-, eF1, ec1⟩ := (Port.ask_ok _ _ _ _ _ _).1 a1
  clear a1
  subst e1 eF1 ec1
  obtain ⟨_, L2, F2, c2, h2, r2⟩ := (bindL_ok _ _ _ _ _ _).1 r1
  clear r1
  obtain ⟨b2, eL2, eF2⟩ := liftBlkL_ok _ _ _ _ _ _ _ _ h2
  clear h2
  have ec2 := Port.testAs_ctx _ _ _ _ _ b2
  clear b2
  subst eL2 eF2 ec2
  obtain ⟨_, L3, F3, c3, h3, r3⟩ := (bindL_ok _ _ _ _ _ _).1 r2
  clear r2
  obtain ⟨b3, eL3, eF3⟩ := liftBlkL_ok _ _ _ _ _ _ _ _ h3
  clear h3
  obtain ⟨-, ec3⟩ := (Port.mustAs_ok _ _ _ _ _).1 b3
  clear b3
  subst eL3 eF3 ec3
  obtain ⟨_, L4, F4, c4, h4, r4⟩ := (bindL_ok _ _ _ _ _ _).1 r3
  clear r3
  obtain ⟨b4, eL4, eF4⟩ := liftBlkL_ok _ _ _ _ _ _ _ _ h4
  clear h4
  obtain ⟨-, ec4⟩ := (Port.mustAs_ok _ _ _ _ _).1 b4
  clear b4
  subst eL4 eF4 ec4
  obtain ⟨_, L5, F5, c5, h5, r5⟩ := (bindL_ok _ _ _ _ _ _).1 r4
  clear r4
  obtain ⟨b5, eL5, eF5⟩ := liftBlkL_ok _ _ _ _ _ _ _ _ h5
  clear h5
  obtain ⟨-, ec5⟩ := (Port.mustAs_ok _ _ _ _ _).1 b5
  clear b5
  subst eL5 eF5 ec5
  obtain ⟨_, L6, F6, c6, h6, r6⟩ := (bindL_ok _ _ _ _ _ _).1 r5
  clear r5
  obtain ⟨b6, eL6, eF6⟩ := liftBlkL_ok _ _ _ _ _ _ _ _ h6
  clear h6
  obtain ⟨-, ec6⟩ := (Port.mustAs_ok _ _ _ _ _).1 b6
  clear b6
  subst eL6 eF6 ec6
  obtain ⟨_, L7, F7, c7, h7, r7⟩ := (bindL_ok _ _ _ _ _ _).1 r6
  clear r6
  obtain ⟨s7, eL7⟩ := liftSubL_ok _ _ _ _ _ _ _ _ h7
  clear h7
  obtain ⟨eF7, ec7⟩ := selfTestF_both tl _ _ _ _ _ s7
  clear s7
  subst eL7 eF7 ec7
  obtain ⟨_, L8, F8, c8, h8, r8⟩ := (bindL_ok _ _ _ _ _ _).1 r7
  clear r7
  obtain ⟨s8, eL8⟩ := liftSubL_ok _ _ _ _ _ _ _ _ h8
  clear h8
  obtain ⟨-, ec8⟩ := Port.coefficientsF_rest tl _ _ _ _ s8
  subst eL8 ec8
  obtain ⟨s9, -⟩ := liftSubL_ok _ _ _ _ _ _ _ _ r8
  exact ⟨F8, s8, s9⟩

/-- The first step of the head's check: all but the arrays is reset, and every virtual row gets its
column weights. -/
instance pres_headStart [PrimS R] :
    Pres R (SubM.change fun F => some ({ trees := F.trees } : Fork).fillL) :=
  pres_change _ fun F _ h => by
    obtain rfl := Option.some.inj h
    exact PrimS.ofShapes ((ShapesKept.of_trees (F := F) (G := ({ trees := F.trees } : Fork))
      rfl).trans (fillL_shapes _))

end OnBytes.Tie.Pv.Tail.Walk

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port OnBytes.Tie.Pv.Tail.Walk

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- `RawRows` as the theorems on objectsF ask it, at the head's check: a run of objectsF, the state
F11 at which the weights are tested, and `RawRows` in every world that reads the four kinds of
virtual row at F11 as sums of the arrays' entries. -/
theorem rawRows_head_runs (tl0 tla : HTailF2) (Fz Fa : Fork) (Tz Ta : Tail2) (nU aTX : Array Nat)
    (hb hbLine : Nat) (h : Head.Shape) (Lh : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered)
    (plain : Array E) (x : Head.Heard) (t : Head.Tables) (Rn : Head.Run) (wsLay : WsLay)
    (claim : WsClaim) (cl : Array WsClaim) (sv : Array Nat) (wo : WsForkOut) (trees : List Nat)
    (nLin used : Nat) (tl1 tlA tl : HTailF2) (L1 L2 L2' L3 L3' L4 L4' L5 L5' L6 : LinkCtx)
    (F0 F1 F2 F3 F3b F4 F4b F4c F5 F6 F8 F12 : Fork)
    (c0 c1 c1' c2 c2' c3 c3' c3b c4 c5 c5' c5b c5c c5d c5e c6 c6' c7 c7' c8 c9 c13 : Ctx)
    (hadd : tl0.addTreesF Fz Tz nU aTX hb hbLine = .ok (tla, Fa, Ta))
    (hrec : RecordKept tla hp.tl) (hk0 : ShapesKept Fa F0)
    (hfill : (SubM.change fun F => some ({ trees := F.trees } : Fork).fillL) F0 c0 =
      .ok (((), F1), c1))
    (hhear : Head.hear h Lh hp cov plain F1 c1' = .ok ((x, F2), c2))
    (hroot : rootInH trees L1 F2 c2' = .ok ((((), L2), F3), c3))
    (htab : Head.tablesOf h Lh hp cov x F3 c3' = .ok ((t, F3b), c3b))
    (hclosed : hp.tl.closeFuns Rn.t.funs = some tl1)
    (htr : tl1.transcript L2' F3b c4 = .ok (((tlA, L3), F4), c5))
    (hwc : Head.weightsClaim Rn wsLay F4 c5' = .ok ((claim, F4b), c5b))
    (hwe : wsForkEnd wsLay cl sv F4b c5c = .ok ((wo, F4c), c5d))
    (hset : SubM.setPlanClaims nLin F4c c5e = .ok (((), F5), c6))
    (hbatch : t2Batch used L3' F5 c6' = .ok ((((), L4), F6), c7))
    (hwalk : Head.walk Rn tlA wo L4' F6 c7' = .ok (((tl, L5), F8), c8))
    (hself : Head.selfTests Rn tl wo L5' F8 c9 = .ok ((((), L6), F12), c13))
    (hv : c9.ch.dry = false) :
    ∃ F7 c7a G c9a F11, tlA.objectsF Rn.t.funs F7 c7a = .ok ((tl, G), c9a) ∧
      tl.coefficientsF F8 c9 = .ok (((), F11), c9) ∧
      ∀ (W : World K) (A : Nat → Nat → Nat → K), ReadsRaw ρ tl Rn.t.funs F11 W A →
        RawRows W tlA G Rn.t.funs (ρ.val G.theta) A := by
  obtain ⟨F7, c7a, G, c9a, kb, hobj, ka⟩ := head_walk_ran Rn tlA tl wo L4' L5 F6 F8 c7' c8 hwalk
  obtain ⟨F11, hco, htile⟩ := head_selfTests_ran Rn tl wo L5' L6 F8 F12 c9 c13 hself
  have a0 := (inferInstance : Pres ShapesKept
    (SubM.change fun F => some ({ trees := F.trees } : Fork).fillL)).out _ _ _ _ _ hfill
  have a1 := (inferInstance : Pres ShapesKept (Head.hear h Lh hp cov plain)).out _ _ _ _ _ hhear
  have a2 := (inferInstance : PresL ShapesKept (rootInH trees)).out _ _ _ _ _ _ _ hroot
  have a3 := (inferInstance : Pres ShapesKept (Head.tablesOf h Lh hp cov x)).out _ _ _ _ _ htab
  have a4 := (inferInstance : PresL ShapesKept tl1.transcriptF).out _ _ _ _ _ _ _ htr
  have a5 := (inferInstance : Pres ShapesKept (Head.weightsClaim Rn wsLay)).out _ _ _ _ _ hwc
  have a6 := (inferInstance : Pres ShapesKept (wsForkEnd wsLay cl sv)).out _ _ _ _ _ hwe
  have a7 := (inferInstance : Pres ShapesKept (SubM.setPlanClaims nLin)).out _ _ _ _ _ hset
  have a8 := (inferInstance : PresL ShapesKept (t2Batch used)).out _ _ _ _ _ _ _ hbatch
  have a9 := (inferInstance : Pres ShapesKept (tlA.objectsF Rn.t.funs)).out _ _ _ _ _ hobj
  have k1 : ShapesKept Fa G :=
    ((((((((((hk0.trans a0).trans a1).trans a2).trans a3).trans a4).trans a5).trans a6).trans
      a7).trans a8).trans kb.shapes).trans a9
  have hrecA : RecordKept tla tlA :=
    (hrec.trans (closeFuns_record hclosed)).trans (transcriptF_record htr)
  exact ⟨F7, c7a, G, c9a, F11, hobj, hco, fun W A hW =>
    rawRows_kept ρ tl0 tla tlA tl Rn.t.funs Fz Fa F7 G F8 F11 F12 Tz Ta nU aTX hb hbLine
      c7a c9a c9 c9 c9 c13 W A hadd hrecA hobj k1 ka hco hv htile hW⟩

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.Walk.head_walk_ran
#print axioms OnBytes.Tie.Pv.Tail.Walk.head_selfTests_ran
#print axioms OnBytes.Tie.Pv.Tail.rawRows_head_runs
