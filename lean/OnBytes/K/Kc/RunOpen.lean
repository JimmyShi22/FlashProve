-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/K/Kc/RunOpen.lean: the whole check of the output head's sub-proof, opened: if it succeeds on
a view, every step has succeeded, each from what the step before has left; and where a step has a
function on plain data, the step is said as an equation in that function.

`Model.Head.runForkHidH2` (OnBytes/Model/Head.lean) is the routine that the program
'verify-on-bytes' runs as the last link of a request's first chain. `HeadRunFacts` lists what a run
of it on a view has done, in the routine's order:
 - the public tests at its beginning;
 - `heard`: all messages up to the commitment to the reads, as `flatHear` at the view's rounds
   (OnBytes/K/Kc/FlatHear.lean);
 - `root`: the chain has received the commitment to the reads (a run of `Model.rootInH`);
 - `tables`: the tables of reads, as `flatTables` (OnBytes/K/Kc/QuietHead.lean);
 - `transcript`: the messages of the smallness test (a run of `Model.HTailF2.transcript`);
 - `weights`: the claim on the committed weights, as `flatWeightsClaim`;
 - `merge`: the merge's messages, as `flatForkEnd` at the view's rounds
   (OnBytes/K/Kc/QuietLink.lean);
 - `batch`: the draw of the element that batches all claims (a run of `Model.t2Batch`);
 - `walk`: all claims added, as `flatWalk`; `tests`: the check's own tests, as `flatSelfTests`;
 - `door`: the one equation handed to the chain (a run of `Model.doorH`);
 - the public tests at its end.
The four steps that call the chain (`root`, `transcript`, `batch`, `door`) stand as runs: they read
and change the chain's statement, which the functions of this directory do not see.

All the states between the steps are letters of `HeadRunFacts`. In the theorem they stand under
"there are"; each is tied at both ends: it is what one step leaves and what the next starts from,
and the first and the last are the run's own. How a context is tied to the one before: over a step
that stands as a run, by that run; over a quiet step, by `Blk.SameButNotes`; over the two steps that
read rounds (`heard`, `merge`), by the equation on the rounds as plain data AND by `Left`
(OnBytes/K/Kc/Laws.lean): the statement, the book, the record of a failed test and the opened
columns are as before, and the view's rounds themselves are the former ones with items taken and
rounds closed. Every context from which a step starts is that of a run on a view: for those behind
a quiet step this follows from `Blk.SameButNotes`; for the others it is a field. Over the four steps
that stand as runs nothing is said here of the record of a failed test: that D bears none does not
go back to the contexts before these steps by these facts.

TWO NAMED HYPOTHESES of `run_open`. `TailQuiet` (OnBytes/K/Kc/QuietLink.lean), which
OnBytes/K/Kc/TailQuiet.lean proves. `FrameKeepsView`: three of the steps that call the chain, run on
a view, leave a run on a view; OnBytes/K/Kc/Door.lean proves it of one of the three and has
`run_open_view`, the same theorem under what is then left. The two others are not proved in this
directory.

Main definitions: `RunsL`, `FrameKeepsView`, `HeadRunFacts`. Main theorem: `run_open`.

Not claimed. One direction alone. Nothing on the dry run. Nothing on soundness. The program does not
import this file.
-/
import OnBytes.K.Kc.PadProved
import OnBytes.K.Kc.QuietLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Kc

open OnBytes.Model (Fork SubM LinkM LinkCtx)

/-! ## A run of a routine that holds the record of its link -/

/-- The routine X, from the link's record L, the state F and the context C, succeeds with the value
a and leaves L', G and D. -/
def RunsL {α : Type} (X : LinkM α) (L : LinkCtx) (F : Fork) (C : Ctx) (a : α) (L' : LinkCtx)
    (G : Fork) (D : Ctx) : Prop :=
  ((X L) F).Yields C ((a, L'), G) D

section Steps

variable {α β : Type} {L L' : LinkCtx} {F G : Fork} {C D : Ctx} {b : β}

theorem stepL {X : LinkM α} {K : α → LinkM β} (H : RunsL (X >>= K) L F C b L' G D) :
    ∃ a L1 F1 C1, RunsL X L F C a L1 F1 C1 ∧ RunsL (K a) L1 F1 C1 b L' G D := by
  have H' : (((X L >>= fun p => K p.1 p.2 : SubM (β × LinkCtx))) F).Yields C ((b, L'), G) D := H
  obtain ⟨⟨a, L1⟩, F1, C1, h1, h2⟩ := (sub_bind _ _ _ _ _ _ _).mp H'
  exact ⟨a, L1, F1, C1, h1, h2⟩

theorem runsL_liftS {x : SubM α} {a : α} (H : RunsL (liftM x : LinkM α) L F C a L' G D) :
    (x F).Yields C (a, G) D ∧ L' = L := by
  have H' : (((x >>= fun y => pure (y, L) : SubM (α × LinkCtx))) F).Yields C ((a, L'), G) D := H
  obtain ⟨y, F1, C1, h1, h2⟩ := (sub_bind _ _ _ _ _ _ _).mp H'
  obtain ⟨e1, e2, e3⟩ := (sub_pure _ _ _ _ _ _).mp h2
  cases e1
  subst e2
  subst e3
  exact ⟨h1, rfl⟩

theorem stepS {x : SubM α} {K : α → LinkM β}
    (H : RunsL ((liftM x : LinkM α) >>= K) L F C b L' G D) :
    ∃ a F1 C1, (x F).Yields C (a, F1) C1 ∧ RunsL (K a) L F1 C1 b L' G D := by
  obtain ⟨a, L1, F1, C1, h1, h2⟩ := stepL H
  obtain ⟨k1, rfl⟩ := runsL_liftS h1
  exact ⟨a, F1, C1, k1, h2⟩

theorem stepSub {x : SubM α} {K : α → LinkM β} (H : RunsL (LinkM.sub x >>= K) L F C b L' G D) :
    ∃ a F1 C1, (x F).Yields C (a, F1) C1 ∧ RunsL (K a) L F1 C1 b L' G D :=
  stepS (x := x) H

theorem stepB {x : Blk α} {K : α → LinkM β}
    (H : RunsL ((liftM x : LinkM α) >>= K) L F C b L' G D) :
    ∃ a C1, x.Yields C a C1 ∧ RunsL (K a) L F C1 b L' G D := by
  obtain ⟨a, F1, C1, h1, h2⟩ := stepS (x := (StateT.lift x : SubM α)) H
  obtain ⟨k1, rfl⟩ := (sub_lift _ _ _ _ _ _).mp h1
  exact ⟨a, C1, k1, h2⟩

theorem stepGet {K : LinkCtx → LinkM β} (H : RunsL ((get : LinkM LinkCtx) >>= K) L F C b L' G D) :
    RunsL (K L) L F C b L' G D := by
  obtain ⟨a, L1, F1, C1, h1, h2⟩ := stepL H
  have h1' : ((pure (L, L) : SubM (LinkCtx × LinkCtx)) F).Yields C ((a, L1), F1) C1 := h1
  obtain ⟨e1, e2, e3⟩ := (sub_pure _ _ _ _ _ _).mp h1'
  cases e1
  subst e2
  subst e3
  exact h2

theorem stepFork {K : Fork → LinkM β} (H : RunsL (LinkM.fork >>= K) L F C b L' G D) :
    RunsL (K F) L F C b L' G D := by
  obtain ⟨a, F1, C1, h1, h2⟩ := stepSub (x := SubM.ask fun F => some F) H
  obtain ⟨e1, e2, e3⟩ := (sub_ask _ _ _ _ _ _).mp h1
  cases e1
  subst e2
  subst e3
  exact h2

theorem runsL_pure {a c : α} (H : RunsL (pure a : LinkM α) L F C c L' G D) :
    c = a ∧ L' = L ∧ G = F ∧ D = C := by
  have H' : ((pure (a, L) : SubM (α × LinkCtx)) F).Yields C ((c, L'), G) D := H
  obtain ⟨e1, e2, e3⟩ := (sub_pure _ _ _ _ _ _).mp H'
  cases e1
  exact ⟨rfl, rfl, e2, e3⟩

end Steps

/-- A value that `Model.Head.getAs` returns was there, and the call changes nothing. -/
theorem getAs_inv {α : Type} (n : String) (x : Option α) (c c' : Ctx) (a : α)
    (h : (Model.Head.getAs n x).Yields c a c') : x = some a ∧ c' = c := by
  cases x with
  | none => cases h
  | some y =>
    obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).mp h
    exact ⟨rfl, rfl⟩

/-! ## The facts -/

/-- THE NAMED HYPOTHESIS: three steps that call the chain, run on a view, leave a run on a view. -/
structure FrameKeepsView : Prop where
  root : ∀ (trees : List Nat) (L L' : LinkCtx) (F G : Fork) (C D : Ctx) (u : Unit),
    C.ch.dry = false → RunsL (Model.rootInH trees) L F C u L' G D → D.ch.dry = false
  transcript : ∀ (tl tl' : Model.HTailF2) (L L' : LinkCtx) (F G : Fork) (C D : Ctx),
    C.ch.dry = false → RunsL tl.transcript L F C tl' L' G D → D.ch.dry = false
  batch : ∀ (used : Nat) (L L' : LinkCtx) (F G : Fork) (C D : Ctx) (u : Unit),
    C.ch.dry = false → RunsL (Model.t2Batch used) L F C u L' G D → D.ch.dry = false

/-- The record of the run that the routine builds. -/
def runOf (h : Model.Head.Shape) (L : Model.Head.HL) (b : Model.Head.Border)
    (hp : Model.Head.HPlanH2) (cov : Model.Head.Covered) (x : Model.Head.Heard)
    (t : Model.Head.Tables) (iU3 : Nat) : Model.Head.Run :=
  { h := h, L := L, b := b, hp := hp, cov := cov, x := x, t := t, iU3 := iU3 }

/-- The state from which the routine starts its work: the caller's arrays with their weights set up,
no slot, no claim. -/
def fresh (F : Fork) : Fork := ({ trees := F.trees } : Fork).fillL

/-- What a run of the head's check on a view has done. -/
structure HeadRunFacts (h : Model.Head.Shape) (L : Model.Head.HL) (b : Model.Head.Border)
    (hp : Model.Head.HPlanH2) (O : Model.Head.Owner) (cov : Model.Head.Covered) (lay : Model.WsLay)
    (Lc Lc' : LinkCtx) (F G : Fork) (C D : Ctx) (wo : Model.WsForkOut)
    (iU3 : Nat) (x : Model.Head.Heard) (t : Model.Head.Tables) (tl0 tl1 tl2 : Model.HTailF2)
    (claim : Model.WsClaim) (nE : Nat) (Lt Lt' Lw Lw' Ls : LinkCtx)
    (Fh Ft Ft' Fc Fc' Fm Fw Fw' Fs : Fork) (Ch Ct Ct' Cc Cc' Cm Cw Cw' Cs : Ctx) : Prop where
  covered : cov.sized h.T = true
  handed : Model.Head.planHanded hp Lc.list F = true
  owner : (!O.tl.ix.TX.isEmpty && O.tl.kTX.back? == some b.kxb) = true
  tree : hp.tl.ix.U.getD 2 none = some iU3
  heard : flatHear h L hp cov Lc.check.plain (fresh F) (tape C) = some (x, Fh, tape Ch)
  root : RunsL (Model.rootInH [iU3]) Lc Fh Ch () Lt Ft Ct
  tables : flatTables h L hp cov x Ft = some (t, Ft')
  tablesCtx : Blk.SameButNotes Ct Ct'
  closed : hp.tl.closeFuns t.funs = some tl0
  transcript : RunsL tl0.transcript Lt Ft' Ct' tl1 Lt' Fc Cc
  weights : flatWeightsClaim (runOf h L b hp cov x t iU3) lay Fc = some (claim, Fc')
  weightsCtx : Blk.SameButNotes Cc Cc'
  one : (hp.NCL == 1) = true
  merge : flatForkEnd lay #[claim] #[x.sV] Fc' (tape Cc') = some (wo, Fm, tape Cm)
  slots : (Fm.next == hp.nMsg) = true
  batch : RunsL (Model.t2Batch Fm.next) Lt' { Fm with planClaimsF := hp.nLin } Cm () Lw Fw Cw
  walk : flatWalk (runOf h L b hp cov x t iU3) tl1 wo Lw Fw = some ((tl2, Lw'), Fw')
  walkCtx : Blk.SameButNotes Cw Cw'
  tests : flatSelfTests (runOf h L b hp cov x t iU3) tl2 wo Lw' Fw' = some (((), Ls), Fs)
  testsCtx : Blk.SameButNotes Cw' Cs
  laid : tl2.equationsLaidF = some nE
  door : RunsL (Model.doorH nE) Ls Fs Cs () Lc' G D
  claimsAll : (G.nClaim == G.planClaimsF) = true
  taken : G.kapAllTakenF = true
  fold : tl2.foldAllTakenF = true
  heardLeft : Left C Ch
  mergeLeft : Left Cc' Cm
  viewRoot : Ct.ch.dry = false
  viewTranscript : Cc.ch.dry = false
  viewBatch : Cw.ch.dry = false
  viewTests : Cs.ch.dry = false

/-- The statement, as a definition of its own name. -/
def LawRun : Prop :=
  ∀ (h : Model.Head.Shape) (L : Model.Head.HL) (b : Model.Head.Border) (hp : Model.Head.HPlanH2)
    (O : Model.Head.Owner) (cov : Model.Head.Covered) (lay : Model.WsLay) (Lc Lc' : LinkCtx)
    (F G : Fork) (C D : Ctx) (wo : Model.WsForkOut), C.ch.dry = false →
    RunsL (Model.Head.runForkHidH2 h L b hp O cov lay) Lc F C wo Lc' G D →
    ∃ iU3 x t tl0 tl1 tl2 claim nE Lt Lt' Lw Lw' Ls Fh Ft Ft' Fc Fc' Fm Fw Fw' Fs
      Ch Ct Ct' Cc Cc' Cm Cw Cw' Cs,
      HeadRunFacts h L b hp O cov lay Lc Lc' F G C D wo iU3 x t tl0 tl1 tl2 claim nE
        Lt Lt' Lw Lw' Ls Fh Ft Ft' Fc Fc' Fm Fw Fw' Fs Ch Ct Ct' Cc Cc' Cm Cw Cw' Cs

theorem dry_of_same {c d : Ctx} (s : Blk.SameButNotes c d) (hd : c.ch.dry = false) :
    d.ch.dry = false := by
  rw [s.ch]
  exact hd

/-- **The whole check of the head's sub-proof, opened.** -/
theorem run_open (V : FrameKeepsView) (T : TailQuiet) : LawRun := by
  intro h L b hp O cov lay Lc Lc' F G C D wo hd H
  unfold Model.Head.runForkHidH2 at H
  obtain ⟨_, C1, s1, H1⟩ := stepB H
  obtain ⟨hcov, e1⟩ := mustAs_inv _ _ _ _ _ s1
  subst e1
  have H2 := stepGet H1
  have H3 := stepFork H2
  obtain ⟨_, C2, s2, H4⟩ := stepB H3
  obtain ⟨hpl, e2⟩ := mustAs_inv _ _ _ _ _ s2
  subst e2
  obtain ⟨_, Fz, C3, s3, H5⟩ := stepSub H4
  obtain ⟨e3, e3'⟩ := (sub_change _ _ _ _ _).mp s3
  subst e3'
  have eFz : fresh F = Fz := Option.some.inj e3
  subst eFz
  obtain ⟨_, C4, s4, H6⟩ := stepB H5
  obtain ⟨hown, e4⟩ := mustAs_inv _ _ _ _ _ s4
  subst e4
  obtain ⟨iU3, C5, s5, H7⟩ := stepB H6
  obtain ⟨hU, e5⟩ := getAs_inv _ _ _ _ _ s5
  subst e5
  obtain ⟨x, Fh, Ch, sx, H8⟩ := stepS H7
  obtain ⟨ex, dh⟩ := lawHear h L hp cov _ _ _ _ _ _ hd sx
  obtain ⟨_, Lt, Ft, Ct, s7, H9⟩ := stepL H8
  have dt := V.root _ _ _ _ _ _ _ _ dh.dry s7
  obtain ⟨t, Ft', Ct', st, H10⟩ := stepS H9
  obtain ⟨lt1, lt2⟩ := lawTables h L hp cov x Ft Ft' Ct t dt
  have et := lt1.mp ⟨Ct', st⟩
  have ct := lt2 Ct' st
  have dt' := dry_of_same ct dt
  obtain ⟨tl0, C9, s9, H11⟩ := stepB H10
  obtain ⟨hcl, e9⟩ := getAs_inv _ _ _ _ _ s9
  subst e9
  obtain ⟨tl1, Lt', Fc, Cc, s10, H12⟩ := stepL H11
  have dc := V.transcript _ _ _ _ _ _ _ _ dt' s10
  obtain ⟨claim, Fc', Cc', sc, H13⟩ := stepS H12
  obtain ⟨lc1, lc2⟩ := lawWeightsClaim (runOf h L b hp cov x t iU3) lay Fc Fc' Cc claim dc
  have ec := lc1.mp ⟨Cc', sc⟩
  have cc := lc2 Cc' sc
  have dc' := dry_of_same cc dc
  obtain ⟨_, C12, s12, H14⟩ := stepB H13
  obtain ⟨hncl, e12⟩ := mustAs_inv _ _ _ _ _ s12
  subst e12
  obtain ⟨wo', Fm, Cm, sm, H15⟩ := stepS H14
  obtain ⟨em, dm⟩ := lawForkEnd lay #[claim] #[x.sV] _ _ _ _ _ dc' sm
  obtain ⟨slot, F14, C14, s14, H16⟩ := stepS H15
  obtain ⟨e14, f14, c14⟩ := (sub_ask _ _ _ _ _ _).mp s14
  subst f14
  subst c14
  have eslot : F14.next = slot := Option.some.inj e14
  subst eslot
  obtain ⟨_, C15, s15, H17⟩ := stepB H16
  obtain ⟨hslot, e15⟩ := mustAs_inv _ _ _ _ _ s15
  subst e15
  obtain ⟨_, Fp, Cp, s16, H18⟩ := stepS H17
  obtain ⟨e16, c16⟩ := (sub_change _ _ _ _ _).mp s16
  subst c16
  have eFp : { F14 with planClaimsF := hp.nLin } = Fp := Option.some.inj e16
  subst eFp
  obtain ⟨_, Lw, Fw, Cw, s17, H19⟩ := stepL H18
  have dw := V.batch _ _ _ _ _ _ _ _ dm.dry s17
  obtain ⟨tl2, Lw', Fw', Cw', sw, H20⟩ := stepL H19
  obtain ⟨lw1, lw2⟩ := lawWalk T (runOf h L b hp cov x t iU3) tl1 wo' Lw Fw Fw' Cw (tl2, Lw') dw
  have ew := lw1.mp ⟨Cw', sw⟩
  have cw := lw2 Cw' sw
  have dw' := dry_of_same cw dw
  obtain ⟨u19, Ls, Fs, Cs, s19, H21⟩ := stepL H20
  obtain ⟨ls1, ls2⟩ :=
    lawSelfTests T (runOf h L b hp cov x t iU3) tl2 wo' Lw' Fw' Fs Cw' (u19, Ls) dw'
  have es := ls1.mp ⟨Cs, s19⟩
  have cs := ls2 Cs s19
  obtain ⟨nE, C20, s20, H22⟩ := stepB H21
  obtain ⟨hE, e20⟩ := getAs_inv _ _ _ _ _ s20
  subst e20
  obtain ⟨_, Ld, Fd, Cd, s21, H23⟩ := stepL H22
  have H24 := stepFork H23
  obtain ⟨_, C22, s22, H25⟩ := stepB H24
  obtain ⟨hnc, e22⟩ := mustAs_inv _ _ _ _ _ s22
  subst e22
  obtain ⟨u23, F23, C23, s23, H26⟩ := stepS H25
  obtain ⟨e23, f23, c23⟩ := (sub_ask _ _ _ _ _ _).mp s23
  subst f23
  subst c23
  obtain ⟨_, C24, s24, H27⟩ := stepB H26
  obtain ⟨hfa, e24⟩ := mustAs_inv _ _ _ _ _ s24
  subst e24
  obtain ⟨w1, w2, w3, w4⟩ := runsL_pure H27
  subst w1
  subst w2
  subst w3
  subst w4
  have htk : G.kapAllTakenF = true := by
    have e23' : (if G.kapAllTakenF = true then some () else none) = some u23 := e23
    by_cases hk : G.kapAllTakenF = true
    · exact hk
    · rw [if_neg hk] at e23'
      cases e23'
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, ⟨hcov, hpl, hown, hU, ex, s7, et, ct, hcl, s10, ec, cc, hncl, em, hslot, s17, ew, cw, es, cs,
      hE, s21, hnc, htk, hfa, dh, dm, dt, dc, dw, dry_of_same cs dw'⟩⟩

end OnBytes.K.Kc

#print axioms OnBytes.K.Kc.run_open
