-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTiedG.lean.
The whole check of a group of layers, cut at its named routines.

`g_run_tied`: if Layer.runForkHidG2 P hp g returns r from the link's state Lc, the state F and the
context c, then these routines have returned, in this order, each with its arguments written out as
terms of P, hp, g and of what the earlier ones returned, and EACH FROM THE STATES AND THE CONTEXT IN
WHICH THE ONE BEFORE IT ENDED: hearLook, from the state F.fillL.slots hp.ns and the context c;
hearOwn; rootInH; closeFuns (a function); transcriptF of the smallness test; t2Batch, with the
number of planned claims set to hp.nLin in the state; the note of the batching element;
Forest.objects;
`gMid`; claimsPlanes; `gEmb`; objectsF; `gLast`, behind which the state has hp.nLin claims;
`gTests`; doorH, which ends in the run's own end state r.1.2 and context r.2. The run returns the
field wo of what hearOwn returned. The lines of the run between these turn neither the states nor
the context.
`gMid`, `gEmb`, `gLast`, `gTests`: four stretches of the check, each as one routine, in the
program's own order and words (`gLedger`, `gEmb0`: the two choices in them).
What each of these runs says is said by the statements on that routine. Nothing is said of a run
that does not return.
Dropped, though the run has them: that the other tests between these routines passed (under the
names internal-g-link, internal-slot-count, internal-g-rows-booked, internal-g-calls-booked; the two
tests by LinkM.must on the arrays' sizes and on the tables held; behind doorH: internal-f-draws,
SubM.allTaken and the test by LinkM.must on the fold's draws).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTiedH

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- The norms' rows, by the number of limbs. -/
def gLedger (P : Layer.Pub) (o : Layer.Own) : SubM Unit :=
  if P.y.h.xl == 5 then Layer.claimsLedger5 o.v o.H else Layer.claimsLedger4 o.v o.H

/-- The check's own claims between the lookup's own claims and the claims on its planes. -/
def gMid (P : Layer.Pub) (o : Layer.Own) : SubM Unit := do
  Layer.noteClaims "the look-up's own claims"
  Layer.claimsNorms P o.v o.H
  Layer.noteClaims "the sums of squares"
  Layer.claimRowBatch P.y o.H
  gLedger P o
  Layer.noteClaims "the norms' rows"
  Layer.claimsTerms o.v o.H
  Layer.noteClaims "the second token sum-check's shown values"
  Layer.claimsGated P o.v o.hd o.hd2
  Layer.noteClaims "the gated products"
  Layer.claimsOneHot o.v

/-- The embedding's claim, in the first group alone. -/
def gEmb0 (g : ℕ) (o : Layer.Own) : SubM Unit :=
  if g == 0 then Layer.claimEmbedding o.v o.H o.sVE else pure ()

/-- The embedding's claim and the note behind it. -/
def gEmb (g : ℕ) (o : Layer.Own) : SubM Unit := do
  gEmb0 g o
  Layer.noteClaims "the planes and the embedding"

/-- The claims behind those of the smallness test. -/
def gLast (g : ℕ) (hp : Layer.HPlan2) (o : Layer.Own) : SubM Unit := do
  Layer.noteClaims "the smallness test"
  SubM.lin o.K.rowS
  Forest.joinAdded o.H.fo
  SubM.lin (Aff.slot o.K.sA0 - o.K.fin.Alin)
  SubM.lin (Aff.slot o.K.sB0 - o.K.fin.Blin)
  wsForkLin o.wo.toWsMerged
  Layer.noteClaims "all claims"
  Layer.freeSlotTest g hp.used o.wo.sFv

/-- The closing steps before the door. -/
def gTests (hp : Layer.HPlan2) (tl : HTailF2) : SubM Unit := do
  tl.selfTest hp.nU
  tl.coefficients
  tl.rkSelfTest

theorem g_run_tied (P : Layer.Pub) (hp : Layer.HPlan2) (g : ℕ) (Lc : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((WsForkOut × LinkCtx) × Fork) × Ctx) (h : Layer.runForkHidG2 P hp g Lc F c = .ok r) :
    ∃ (iU3 : ℕ) (fo : Forest.Heard) (Fl : Fork) (cl : Ctx) (o : Layer.Own) (Fo : Fork) (co : Ctx)
      (L8 : LinkCtx) (Fa : Fork) (ca : Ctx) (tl1 tl2 tl3 : HTailF2) (Lt : LinkCtx) (Gt : Fork)
      (cr : Ctx) (Lb : LinkCtx) (Gb : Fork) (cb : Ctx) (G1 : Fork) (c1 : Ctx) (G2 : Fork) (c2 : Ctx)
      (G3 : Fork) (c3 : Ctx) (G4 : Fork) (c4 : Ctx) (G5 : Fork) (c5 : Ctx) (G6 : Fork) (c6 : Ctx)
      (G7 : Fork) (c7 : Ctx) (G8 : Fork) (c8 : Ctx) (n : ℕ),
      hp.tl.ix.U.getD 2 none = some iU3 ∧
      Layer.hearLook P.y g (F.fillL.slots hp.ns) c = .ok ((fo, Fl), cl) ∧
      Layer.hearOwn P hp g fo Fl cl = .ok ((o, Fo), co) ∧
      rootInH [iU3] Lc Fo co = .ok ((((), L8), Fa), ca) ∧
      hp.tl.closeFuns o.funs = some tl1 ∧
      tl1.transcriptF L8 Fa ca = .ok (((tl2, Lt), Gt), cr) ∧
      t2Batch Gt.next Lt { Gt with planClaimsF := hp.nLin } cr = .ok ((((), Lb), Gb), cb) ∧
      (do Layer.note "the element that batches the claims" (← get).theta : SubM Unit) Gb cb =
        .ok (((), G1), c1) ∧
      Forest.objects o.H.fo G1 c1 = .ok (((), G2), c2) ∧
      gMid P o G2 c2 = .ok (((), G3), c3) ∧
      Layer.claimsPlanes o.v o.H.fo G3 c3 = .ok (((), G4), c4) ∧
      gEmb g o G4 c4 = .ok (((), G5), c5) ∧
      tl2.objectsF o.funs G5 c5 = .ok ((tl3, G6), c6) ∧
      gLast g hp o G6 c6 = .ok (((), G7), c7) ∧
      (G7.nClaim == hp.nLin) = true ∧
      gTests hp tl3 G7 c7 = .ok (((), G8), c8) ∧
      tl3.equationsLaidF = some n ∧
      doorH n Lb G8 c8 = .ok ((((), r.1.1.2), r.1.2), r.2) ∧ r.1.1.1 = o.wo := by
  obtain ⟨⟨⟨w, Lr⟩, Gr⟩, cq⟩ := r
  unfold Layer.runForkHidG2 at h
  simp only [] at h
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h1, h⟩ := h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := getLine h1
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h2, h⟩ := h
  obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h2
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h3, h⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := subLine (IdleS.ask _) h3
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h4, h⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := subLine (IdleS.lift (IdleB.must _ _)) h4
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h5, h⟩ := h
  obtain ⟨k5, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h5
  obtain ⟨_, hG5, e5⟩ := (change_ok _ _ _ _).1 k5
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e5
  obtain rfl := Option.some.inj hG5
  rw [linkBind_ok'] at h
  obtain ⟨iU3, _, _, _, h6, h⟩ := h
  obtain ⟨g6, rfl, rfl, rfl⟩ := formLine h6
  rw [linkBind_ok'] at h
  obtain ⟨o, _, _, _, h7, h⟩ := h
  obtain ⟨k7, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h7
  rw [bind_ok] at k7
  obtain ⟨fo, _, _, kl, ko⟩ := k7
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h8, h⟩ := h
  rw [linkBind_ok'] at h
  obtain ⟨tl1, _, _, _, h9, h⟩ := h
  obtain ⟨g9, rfl, rfl, rfl⟩ := formLine h9
  rw [linkBind_ok'] at h
  obtain ⟨tl2, _, _, _, h10, h⟩ := h
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h11, h⟩ := h
  obtain ⟨k11, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h11
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using (slot_ok _ _ _).1 k11
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h12, h⟩ := h
  obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h12
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h13, h⟩ := h
  obtain ⟨k13, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h13
  obtain ⟨_, hG13, e13⟩ := (change_ok _ _ _ _).1 k13
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e13
  obtain rfl := Option.some.inj hG13
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h14, h⟩ := h
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h15, h⟩ := h
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
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h21, h⟩ := h
  obtain ⟨k21, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h21
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h22, h⟩ := h
  obtain ⟨k22, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h22
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h23, h⟩ := h
  obtain ⟨k23, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h23
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h24, h⟩ := h
  obtain ⟨k24, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h24
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h25, h⟩ := h
  obtain ⟨k25, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h25
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h26, h⟩ := h
  obtain ⟨k26, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h26
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h27, h⟩ := h
  obtain ⟨k27, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h27
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h28, h⟩ := h
  obtain ⟨k28, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h28
  by_cases hE : (g == 0) = true
  · simp only [hE, if_true] at h
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h29, h⟩ := h
    obtain ⟨k29, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h29
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h30, h⟩ := h
    obtain ⟨k30, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h30
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h31, h⟩ := h
    obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h31
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h32, h⟩ := h
    obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h32
    rw [linkBind_ok'] at h
    obtain ⟨tl3, _, _, _, h33, h⟩ := h
    obtain ⟨k33, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h33
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h34, h⟩ := h
    obtain ⟨k34, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h34
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h35, h⟩ := h
    obtain ⟨k35, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h35
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h36, h⟩ := h
    obtain ⟨k36, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h36
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h37, h⟩ := h
    obtain ⟨k37, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h37
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h38, h⟩ := h
    obtain ⟨k38, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h38
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h39, h⟩ := h
    obtain ⟨k39, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h39
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h40, h⟩ := h
    obtain ⟨k40, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h40
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h41, h⟩ := h
    obtain ⟨k41, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h41
    rw [linkBind_ok'] at h
    obtain ⟨Fq, _, _, _, h42, h⟩ := h
    obtain ⟨k42, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h42
    obtain ⟨_, hq, eq42⟩ := (ask_ok _ _ _ _).1 k42
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using eq42
    obtain rfl := Option.some.inj hq
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h43, h⟩ := h
    obtain ⟨rfl, rfl, rfl, m43⟩ := blkLine (IdleB.mustAs _ _) h43
    have n43 := mustAs_true m43
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h44, h⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := subLine (IdleS.lift (IdleB.must _ _)) h44
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h45, h⟩ := h
    obtain ⟨k45, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h45
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h46, h⟩ := h
    obtain ⟨k46, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h46
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h47, h⟩ := h
    obtain ⟨k47, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h47
    rw [linkBind_ok'] at h
    obtain ⟨n, _, _, _, h48, h⟩ := h
    obtain ⟨g48, rfl, rfl, rfl⟩ := formLine h48
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h49, h⟩ := h
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h50, h⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := subLine (IdleS.ask _) h50
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h51, h⟩ := h
    obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h51
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h52, h⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := subLine (IdleS.ask _) h52
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h53, h⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := subLine (IdleS.lift (IdleB.must _ _)) h53
    have e := (linkPure_ok _ _ _ _ _).1 h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
    have qMid :=
      seq_ok k17 (seq_ok k18 (seq_ok k19 (seq_ok k20
          (seq_ok k21 (seq_ok k22 (seq_ok k23 (seq_ok k24 (seq_ok k25 (seq_ok k26 k27)))))))))
    have qEmb := seq_ok (ite_true_ok (y := pure ()) hE k29) k30
    have qLast :=
      seq_ok k34 (seq_ok k35 (seq_ok k36 (seq_ok k37 (seq_ok k38 (seq_ok k39 (seq_ok k40 k41))))))
    have qTests := seq_ok k45 (seq_ok k46 k47)
    exact ⟨iU3, fo, _, _, o, _, _, _, _, _, tl1, tl2, tl3, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, n, g6, kl, ko, h8, g9, h10, h14, k15, k16, qMid, k28, qEmb, k33,
      qLast, n43, qTests, g48, h49, rfl⟩
  · simp only [hE, if_false, Bool.false_eq_true] at h
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h29, h⟩ := h
    have e29 := (linkPure_ok _ _ _ _ _).1 h29
    obtain ⟨⟨⟨-, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e29
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h30, h⟩ := h
    obtain ⟨k30, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h30
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h31, h⟩ := h
    obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h31
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h32, h⟩ := h
    obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h32
    rw [linkBind_ok'] at h
    obtain ⟨tl3, _, _, _, h33, h⟩ := h
    obtain ⟨k33, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h33
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h34, h⟩ := h
    obtain ⟨k34, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h34
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h35, h⟩ := h
    obtain ⟨k35, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h35
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h36, h⟩ := h
    obtain ⟨k36, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h36
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h37, h⟩ := h
    obtain ⟨k37, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h37
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h38, h⟩ := h
    obtain ⟨k38, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h38
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h39, h⟩ := h
    obtain ⟨k39, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h39
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h40, h⟩ := h
    obtain ⟨k40, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h40
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h41, h⟩ := h
    obtain ⟨k41, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h41
    rw [linkBind_ok'] at h
    obtain ⟨Fq, _, _, _, h42, h⟩ := h
    obtain ⟨k42, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h42
    obtain ⟨_, hq, eq42⟩ := (ask_ok _ _ _ _).1 k42
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using eq42
    obtain rfl := Option.some.inj hq
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h43, h⟩ := h
    obtain ⟨rfl, rfl, rfl, m43⟩ := blkLine (IdleB.mustAs _ _) h43
    have n43 := mustAs_true m43
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h44, h⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := subLine (IdleS.lift (IdleB.must _ _)) h44
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h45, h⟩ := h
    obtain ⟨k45, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h45
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h46, h⟩ := h
    obtain ⟨k46, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h46
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h47, h⟩ := h
    obtain ⟨k47, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h47
    rw [linkBind_ok'] at h
    obtain ⟨n, _, _, _, h48, h⟩ := h
    obtain ⟨g48, rfl, rfl, rfl⟩ := formLine h48
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h49, h⟩ := h
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h50, h⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := subLine (IdleS.ask _) h50
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h51, h⟩ := h
    obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h51
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h52, h⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := subLine (IdleS.ask _) h52
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h53, h⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := subLine (IdleS.lift (IdleB.must _ _)) h53
    have e := (linkPure_ok _ _ _ _ _).1 h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
    have qMid :=
      seq_ok k17 (seq_ok k18 (seq_ok k19 (seq_ok k20
          (seq_ok k21 (seq_ok k22 (seq_ok k23 (seq_ok k24 (seq_ok k25 (seq_ok k26 k27)))))))))
    have qEmb := seq_ok (ite_false_ok (x := Layer.claimEmbedding o.v o.H o.sVE) hE
      ((pure_ok () _ _ _).2 rfl)) k30
    have qLast :=
      seq_ok k34 (seq_ok k35 (seq_ok k36 (seq_ok k37 (seq_ok k38 (seq_ok k39 (seq_ok k40 k41))))))
    have qTests := seq_ok k45 (seq_ok k46 k47)
    exact ⟨iU3, fo, _, _, o, _, _, _, _, _, tl1, tl2, tl3, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, n, g6, kl, ko, h8, g9, h10, h14, k15, k16, qMid, k28, qEmb, k33,
      qLast, n43, qTests, g48, h49, rfl⟩

end Fo
