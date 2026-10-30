-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTiedH.lean.
The output head's whole check, cut at its named routines.

`h_run_tied`: if Head.runForkHidH2 returns r from the link's state Lc, the state F and the context
c, then these routines have returned, in this order, each with its arguments written out as terms of
the check's own arguments and of what the earlier ones returned, and EACH FROM THE STATES AND THE
CONTEXT IN WHICH THE ONE BEFORE IT ENDED: Head.hear, from the state ({ trees := F.trees } :
Fork).fillL and the context c, for the plain scalars of Lc; rootInH; Head.tablesOf; closeFuns (a
function); transcriptF of the smallness test; weightsClaim; wsForkEnd; t2Batch, with the number of
planned claims set to hp.nLin in the state; Head.walk, for the record `hRun`; selfTests; doorH,
which ends in the run's own end state r.1.2 and context r.2. The run returns what wsForkEnd
returned. The lines of the run between these turn neither the states nor the context.
`h_walk_tied`: if Head.walk returns, then Forest.objects has returned from walk's own first state
and context, and behind it claimJoin, claimPlanes and objectsF have returned; objectsF returned what
walk returns. From the state that one of the four left to the state from which the next ran, and
from the last to walk's own end state, every property that the steps keep passes on (`Passes`,
OnBytes/Tie/Pv/Lookup/Ends/FoPass.lean).
`h_walk_exact`: the same with nothing left free: walk leaves the link's state as it was, and eight
routines have returned in a row, each from the state and the context in which the one before it
ended: Forest.objects, `hMid1`, claimJoin, `hMid2`, claimPlanes, a note, objectsF, `hLast`; the
first from walk's own first state and context, the last ending in walk's own end state and context.
`hMid1`, `hMid2`, `hLast`: three stretches of walk, each as one routine, in the program's own order
and words.
What each of these runs says is said by the statements on that routine.
Not tied in h_walk_tied: the contexts of claimJoin, claimPlanes and objectsF. Nothing is said of a
run that does not return.
Dropped in h_run_tied, though the run has them: that the tests between these routines passed (under
the names internal-h-covered, plan-link, internal-h-owner-TX, internal-claim-count,
internal-slot-count; behind doorH: internal-f-draws, twice, and SubM.allTaken).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTiedA

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- The record that the head's claims read. -/
def hRun (s : Head.Shape) (Y : Head.HL) (b : Head.Border) (hp : Head.HPlanH2) (cov : Head.Covered)
    (x : Head.Heard) (t : Head.Tables) (iU3 : ℕ) : Head.Run :=
  { h := s, L := Y, b := b, hp := hp, cov := cov, x := x, t := t, iU3 := iU3 }

theorem getAs_some {α : Type} {name : String} {x : Option α} {c c' : Ctx} {a : α}
    (h : Head.getAs name x c = .ok (a, c')) : x = some a := by
  unfold Head.getAs at h
  cases x with
  | none => cases h
  | some b =>
    have e : (b, c) = (a, c') := Except.ok.inj h
    rw [(Prod.mk.inj e).1]

theorem h_walk_tied (R : Head.Run) (tl tl' : HTailF2) (wo : WsForkOut) (L L' : LinkCtx)
    (F G : Fork) (c c' : Ctx) (h : Head.walk R tl wo L F c = .ok (((tl', L'), G), c')) :
    ∃ (Fo : Fork) (co : Ctx) (Fj Gj : Fork) (cj cj' : Ctx) (Fp Gp : Fork) (cp cp' : Ctx)
      (Fz Gz : Fork) (cz cz' : Ctx),
      Forest.objects R.x.g1 F c = .ok (((), Fo), co) ∧
      Head.claimJoin R Fj cj = .ok (((), Gj), cj') ∧
      Head.claimPlanes R Fp cp = .ok (((), Gp), cp') ∧
      tl.objectsF R.t.funs Fz cz = .ok ((tl', Gz), cz') ∧
      Passes Fo Fj ∧ Passes Gj Fp ∧ Passes Gp Fz ∧ Passes Gz G := by
  unfold Head.walk at h
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h1, h⟩ := h
  obtain ⟨k1, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h1
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h2, h⟩ := h
  have p2 := Passes.ofL h2 (fun I _ => by inv)
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h3, h⟩ := h
  have p3 := Passes.ofL h3 (fun I _ => by inv)
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h4, h⟩ := h
  have p4 := Passes.ofL h4 (fun I _ => by inv)
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h5, h⟩ := h
  have p5 := Passes.ofL h5 (fun I _ => by inv)
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h6, h⟩ := h
  have p6 := Passes.ofL h6 (fun I _ => by inv)
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h7, h⟩ := h
  have p7 := Passes.ofL h7 (fun I _ => by inv)
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h8, h⟩ := h
  have p8 := Passes.ofL h8 (fun I _ => by inv)
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h9, h⟩ := h
  obtain ⟨k9, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h9
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h10, h⟩ := h
  have p10 := Passes.ofL h10 (fun I _ => by inv)
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h11, h⟩ := h
  have p11 := Passes.ofL h11 (fun I _ => by inv)
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h12, h⟩ := h
  have p12 := Passes.ofL h12 (fun I _ => by inv)
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h13, h⟩ := h
  obtain ⟨k13, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h13
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h14, h⟩ := h
  have p14 := Passes.ofL h14 (fun I _ => by inv)
  rw [linkBind_ok'] at h
  obtain ⟨tl3, _, _, _, h15, h⟩ := h
  obtain ⟨k15, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h15
  have pE := Passes.ofL h (fun I _ => by inv)
  have et : tl' = tl3 := by
    refine (?_ : YieldsL _ fun a : HTailF2 => a = tl3) _ _ _ _ _ _ _ h
    repeat' first
      | exact YieldsL.pure rfl
      | (refine YieldsL.bind fun _ => ?_)
  subst et
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, k1, k9, k13, k15,
    p2.trans (p3.trans (p4.trans (p5.trans (p6.trans (p7.trans p8))))),
    p10.trans (p11.trans p12), p14, pE⟩

/-- The head's own claims between the lookup's own claims and its join. -/
def hMid1 (R : Head.Run) : SubM Unit := do
  Head.noteConstant "the look-up's claims on mask entries"
  Head.claimSquares R
  Head.noteConstant "the sum of squares"
  Head.claimLedger R
  Head.noteConstant "the row ledger"
  Head.claimStream R
  Head.noteConstant "the stream times the reciprocal"

/-- The head's own claims between the lookup's join and the claims on its planes. -/
def hMid2 (R : Head.Run) : SubM Unit := do
  Head.noteConstant "the look-up's join"
  Head.claimPolicy R
  Head.noteConstant "the acceptance policy"

/-- The head's claims behind those of the smallness test. -/
def hLast (R : Head.Run) (wo : WsForkOut) : SubM Unit := do
  Head.noteConstant "the smallness test"
  Head.claimLogits R
  Head.noteConstant "the logits"
  wsForkLin wo.toWsMerged
  Head.noteConstant "the merge"

theorem h_walk_exact (R : Head.Run) (tl tl' : HTailF2) (wo : WsForkOut) (L L' : LinkCtx)
    (F G : Fork) (c c' : Ctx) (h : Head.walk R tl wo L F c = .ok (((tl', L'), G), c')) :
    L' = L ∧ ∃ (F1 : Fork) (c1 : Ctx) (F2 : Fork) (c2 : Ctx) (F3 : Fork) (c3 : Ctx) (F4 : Fork)
      (c4 : Ctx) (F5 : Fork) (c5 : Ctx) (F6 : Fork) (c6 : Ctx) (F7 : Fork) (c7 : Ctx),
      Forest.objects R.x.g1 F c = .ok (((), F1), c1) ∧
      hMid1 R F1 c1 = .ok (((), F2), c2) ∧
      Head.claimJoin R F2 c2 = .ok (((), F3), c3) ∧
      hMid2 R F3 c3 = .ok (((), F4), c4) ∧
      Head.claimPlanes R F4 c4 = .ok (((), F5), c5) ∧
      Head.noteConstant "the look-up's planes" F5 c5 = .ok (((), F6), c6) ∧
      tl.objectsF R.t.funs F6 c6 = .ok ((tl', F7), c7) ∧
      hLast R wo F7 c7 = .ok (((), G), c') := by
  unfold Head.walk at h
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h1, h⟩ := h
  obtain ⟨k1, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h1
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h2, h⟩ := h
  obtain ⟨k2, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h2
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h3, h⟩ := h
  obtain ⟨k3, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h3
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h4, h⟩ := h
  obtain ⟨k4, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h4
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h5, h⟩ := h
  obtain ⟨k5, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h5
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h6, h⟩ := h
  obtain ⟨k6, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h6
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h7, h⟩ := h
  obtain ⟨k7, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h7
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h8, h⟩ := h
  obtain ⟨k8, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h8
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h9, h⟩ := h
  obtain ⟨k9, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h9
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h10, h⟩ := h
  obtain ⟨k10, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h10
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h11, h⟩ := h
  obtain ⟨k11, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h11
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h12, h⟩ := h
  obtain ⟨k12, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h12
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h13, h⟩ := h
  obtain ⟨k13, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h13
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h14, h⟩ := h
  obtain ⟨k14, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h14
  rw [linkBind_ok'] at h
  obtain ⟨tl3, _, _, _, h15, h⟩ := h
  obtain ⟨k15, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h15
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h16, h⟩ := h
  obtain ⟨k16, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h16
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h17, h⟩ := h
  obtain ⟨k17, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h17
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h18, h⟩ := h
  obtain ⟨k18, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h18
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h19, h⟩ := h
  obtain ⟨k19, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h19
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h20, h⟩ := h
  obtain ⟨k20, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h20
  have e := (linkPure_ok _ _ _ _ _).1 h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
  have q1 := seq_ok k2 (seq_ok k3 (seq_ok k4 (seq_ok k5 (seq_ok k6 (seq_ok k7 k8)))))
  have q2 := seq_ok k10 (seq_ok k11 k12)
  have q3 := seq_ok k16 (seq_ok k17 (seq_ok k18 (seq_ok k19 k20)))
  exact ⟨rfl, _, _, _, _, _, _, _, _, _, _, _, _, _, _, k1, q1, k9, q2, k13, k14, k15, q3⟩

theorem h_run_tied (s : Head.Shape) (Y : Head.HL) (b : Head.Border) (hp : Head.HPlanH2)
    (O : Head.Owner) (cov : Head.Covered) (wsLay : WsLay) (Lc : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((WsForkOut × LinkCtx) × Fork) × Ctx)
    (h : Head.runForkHidH2 s Y b hp O cov wsLay Lc F c = .ok r) :
    ∃ (x : Head.Heard) (t : Head.Tables) (iU3 : ℕ) (Fh : Fork) (ch : Ctx) (L9 : LinkCtx)
      (Fa : Fork) (ca : Ctx) (Ga : Fork) (ca' : Ctx) (tl1 tl2 tl3 : HTailF2) (Lt : LinkCtx)
      (Gt : Fork) (cr : Ctx) (claim : WsClaim) (Gw : Fork) (cw : Ctx) (Ge : Fork) (ce : Ctx)
      (Lb : LinkCtx) (Gb : Fork) (cb : Ctx) (Lw : LinkCtx) (Gk : Fork) (ck : Ctx) (Ls : LinkCtx)
      (Gs : Fork) (cs : Ctx) (n : ℕ),
      hp.tl.ix.U.getD 2 none = some iU3 ∧
      Head.hear s Y hp cov Lc.check.plain ({ trees := F.trees } : Fork).fillL c =
        .ok ((x, Fh), ch) ∧
      rootInH [iU3] Lc Fh ch = .ok ((((), L9), Fa), ca) ∧
      Head.tablesOf s Y hp cov x Fa ca = .ok ((t, Ga), ca') ∧
      hp.tl.closeFuns t.funs = some tl1 ∧
      tl1.transcriptF L9 Ga ca' = .ok (((tl2, Lt), Gt), cr) ∧
      Head.weightsClaim (hRun s Y b hp cov x t iU3) wsLay Gt cr = .ok ((claim, Gw), cw) ∧
      wsForkEnd wsLay #[claim] #[x.sV] Gw cw = .ok ((r.1.1.1, Ge), ce) ∧
      t2Batch Ge.next Lt { Ge with planClaimsF := hp.nLin } ce = .ok ((((), Lb), Gb), cb) ∧
      Head.walk (hRun s Y b hp cov x t iU3) tl2 r.1.1.1 Lb Gb cb = .ok (((tl3, Lw), Gk), ck) ∧
      Head.selfTests (hRun s Y b hp cov x t iU3) tl3 r.1.1.1 Lw Gk ck =
        .ok ((((), Ls), Gs), cs) ∧
      tl3.equationsLaidF = some n ∧
      doorH n Ls Gs cs = .ok ((((), r.1.1.2), r.1.2), r.2) := by
  obtain ⟨⟨⟨w, Lr⟩, Gr⟩, cq⟩ := r
  unfold Head.runForkHidH2 at h
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h1, h⟩ := h
  obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h1
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h2, h⟩ := h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := getLine h2
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h3, h⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := subLine (IdleS.ask _) h3
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h4, h⟩ := h
  obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h4
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h5, h⟩ := h
  obtain ⟨k5, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h5
  obtain ⟨_, hG5, e5⟩ := (change_ok _ _ _ _).1 k5
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e5
  obtain rfl := Option.some.inj hG5
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h6, h⟩ := h
  obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h6
  rw [linkBind_ok'] at h
  obtain ⟨iU3, _, _, _, h7, h⟩ := h
  obtain ⟨rfl, rfl, rfl, g7⟩ := blkLine (IdleB.getAs _ _) h7
  have g7 := getAs_some g7
  rw [linkBind_ok'] at h
  obtain ⟨x, _, _, _, h8, h⟩ := h
  obtain ⟨k8, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h8
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h9, h⟩ := h
  rw [linkBind_ok'] at h
  obtain ⟨t, _, _, _, h10, h⟩ := h
  obtain ⟨k10, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h10
  rw [linkBind_ok'] at h
  obtain ⟨tl1, _, _, _, h11, h⟩ := h
  obtain ⟨rfl, rfl, rfl, g11⟩ := blkLine (IdleB.getAs _ _) h11
  have g11 := getAs_some g11
  rw [linkBind_ok'] at h
  obtain ⟨tl2, _, _, _, h12, h⟩ := h
  rw [linkBind_ok'] at h
  obtain ⟨claim, _, _, _, h13, h⟩ := h
  obtain ⟨k13, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h13
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h14, h⟩ := h
  obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h14
  rw [linkBind_ok'] at h
  obtain ⟨wo, _, _, _, h15, h⟩ := h
  obtain ⟨k15, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h15
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h16, h⟩ := h
  obtain ⟨k16, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h16
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using (slot_ok _ _ _).1 k16
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h17, h⟩ := h
  obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h17
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h18, h⟩ := h
  obtain ⟨k18, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h18
  obtain ⟨_, hG18, e18⟩ := (change_ok _ _ _ _).1 k18
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e18
  obtain rfl := Option.some.inj hG18
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h19, h⟩ := h
  rw [linkBind_ok'] at h
  obtain ⟨tl3, _, _, _, h20, h⟩ := h
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h21, h⟩ := h
  rw [linkBind_ok'] at h
  obtain ⟨n, _, _, _, h22, h⟩ := h
  obtain ⟨rfl, rfl, rfl, g22⟩ := blkLine (IdleB.getAs _ _) h22
  have g22 := getAs_some g22
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h23, h⟩ := h
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h24, h⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := subLine (IdleS.ask _) h24
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h25, h⟩ := h
  obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h25
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h26, h⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := subLine (IdleS.ask _) h26
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h27, h⟩ := h
  obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h27
  have e := (linkPure_ok _ _ _ _ _).1 h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
  exact ⟨x, t, iU3, _, _, _, _, _, _, _, tl1, tl2, tl3, _, _, _, claim, _, _, _, _, _, _, _, _, _,
    _, _, _, _, n, g7, k8, h9, k10, g11, h12, k13, k15, h19, h20, h21, g22, h23⟩

end Fo
