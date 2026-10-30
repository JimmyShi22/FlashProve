-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/K/Kc/Door.lean: the two last steps of a sub-proof's check that meet the chain, opened: the
draw of the element that batches all claims, and the step that hands the one equation on.

 - `flatBatch`: `Model.t2Batch` (OnBytes/Model/Trees.lean) as a function on the link's record, the
   ledger and the rounds: it reads one round, of which nothing is left to take, and takes the one
   element drawn as the batching element. Its law `lawBatch` has the form of
   OnBytes/K/Kc/Laws.lean. With it one field of the named hypothesis `FrameKeepsView`
   (OnBytes/K/Kc/RunOpen.lean) is proved: `batch_keeps`; `run_open_view` is that file's theorem
   under the two fields that are left, with `TailQuiet` discharged.
 - `Model.doorH` is cut in two. `doorEq` is its text up to the equation: tests of the order of the
   steps, the terms on the listed arrays, the coefficients on the mask row and the constant
   (`Model.Fork.settle`). `doorSend` is the rest: the number of batched rows is held against the
   plan's entry, the chain takes the equation (`Model.ChainCheck.close`), the link is marked as
   done. `doorH_split`: the routine IS the one after the other.
 - `doorEq` is quiet (OnBytes/K/Kc/Quiet.lean), so `flatDoor`, the same routine from an empty
   context, is a function on the link's record and the ledger alone: THE ONE EQUATION THAT GOES OUT
   OF A SUB-PROOF, as plain data (`DoorOut`).
 - `run_door`: at a run of the head's whole check, the entry whose rows the door counts IS the entry
   under which the batching element's round was closed.
 - `door_open`: what a run of `Model.doorH` on a view has done: `flatDoor` has returned the
   equation; the plan's entry of the round closed last counts as many rows as claims were added and
   equations laid; the chain's call has run on that very equation; what is left of the link's record
   and of the ledger.

Not claimed. What the chain's call does with the equation. Nothing on the dry run. Nothing on
soundness. The program does not import this file.
-/
import OnBytes.K.Kc.RunOpen
import OnBytes.K.Kc.TailQuiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Kc

open OnBytes.Model (Fork SubM LinkM LinkCtx)

variable {α β γ σ : Type}

/-! ## The draw of the batching element -/

/-- If the first of two steps returns, the two are the second from what the first has left. -/
theorem Fl.bind_eq {x : Fl α} {f : α → Fl β} {F G : Fork} {t u : Tape} {a : α}
    (h : x F t = some (a, G, u)) : (x >>= f) F t = f a G u := by
  show Fl.andThen x f F t = _
  unfold Fl.andThen
  rw [h]

/-- `Model.t2Batch` on the link's record, the ledger and the rounds. -/
def flatBatch (used : Nat) (L : LinkCtx) : Fl (Unit × LinkCtx) := do
  let x ← Fl.ask fun F => some (F.ns, F.planClaimsF)
  Fl.must (L.list.planned && used == x.1)
  Fl.must (L.list.link && !L.handed && L.moments == L.check.momentsOf L.link)
  Fl.change fun F => some (Model.t2FillL F L.list)
  let drawn ← Fl.onTape (closeOne Model.RoundName.batSigma.name 0)
  Fl.change (·.batchBy drawn)
  Fl.must (x.2 != 0)
  Fl.change fun F => some { F with kapMapF := Array.replicate F.planClaimsF false }
  pure ((), { L with list := { L.list with used := used }, handed := true })

/-- **The draw of the batching element.** -/
theorem lawBatch (used : Nat) (L L' : LinkCtx) (F G : Fork) (C D : Ctx) (u : Unit)
    (hd : C.ch.dry = false) (H : RunsL (Model.t2Batch used) L F C u L' G D) :
    flatBatch used L F (tape C) = some (((), L'), G, tape D) ∧ Left C D ∧
      ∃ e, D.ch.last = some e ∧ e.name = Model.RoundName.batSigma.name ∧ e.drawNZ = 0 ∧
        D.ch.askedRows = false := by
  unfold Model.t2Batch at H
  unfold LinkM.mustAs at H
  have H1 := stepGet H
  obtain ⟨x, F1, C1, s1, H2⟩ := stepSub H1
  obtain ⟨ns, pc⟩ := x
  obtain ⟨_, F2, C2, s2, H3⟩ := stepSub H2
  obtain ⟨_, F3, C3, s3, H4⟩ := stepSub H3
  obtain ⟨_, F4, C4, s4, H5⟩ := stepSub H4
  obtain ⟨drawn, F5, C5, s5, H6⟩ := stepSub H5
  obtain ⟨_, F6, C6, s6, H7⟩ := stepSub H6
  obtain ⟨_, F7, C7, s7, H8⟩ := stepSub H7
  obtain ⟨_, F8, C8, s8, H9⟩ := stepSub H8
  have H9' : ((pure (PUnit.unit, { L with list := { L.list with used := used }, handed := true }) :
      SubM (PUnit × LinkCtx)) F8).Yields C8 ((u, L'), G) D := H9
  obtain ⟨w1, w2, w3⟩ := (sub_pure _ _ _ _ _ _).mp H9'
  obtain ⟨a1, d1⟩ := Sim.ask (fun F => some (F.ns, F.planClaimsF)) F F1 C C1 (ns, pc) hd s1
  obtain ⟨a2, d2⟩ := Sim.mustAs _ _ F1 F2 C1 C2 _ d1.dry s2
  obtain ⟨a3, d3⟩ := Sim.mustAs _ _ F2 F3 C2 C3 _ d2.dry s3
  obtain ⟨a4, d4⟩ := Sim.change _ F3 F4 C3 C4 _ d3.dry s4
  obtain ⟨a5, d5⟩ := Sim.lift simB_trBatchOpen F4 F5 C4 C5 drawn d4.dry s5
  obtain ⟨a6, d6⟩ := Sim.change _ F5 F6 C5 C6 _ d5.dry s6
  obtain ⟨a7, d7⟩ := Sim.mustAs _ _ F6 F7 C6 C7 _ d6.dry s7
  obtain ⟨a8, d8⟩ := Sim.change _ F7 F8 C7 C8 _ d7.dry s8
  obtain ⟨b5, _⟩ := (sub_lift _ _ _ _ _ _).mp s5
  obtain ⟨_, e5, _, _, _, cl⟩ := trBatchOpen_closed _ _ _ d4.dry b5
  have c6 : C6 = C5 := ((sub_change _ _ _ _ _).mp s6).2
  have c7 : C7 = C6 := (mustAs_inv _ _ _ _ _ ((sub_lift _ _ _ _ _ _).mp s7).1).2
  have c8 : C8 = C7 := ((sub_change _ _ _ _ _).mp s8).2
  have cD : D = C5 := w3.trans (c8.trans (c7.trans c6))
  subst w2
  refine ⟨?_, by
    rw [w3]
    exact d1.trans (d2.trans (d3.trans (d4.trans (d5.trans (d6.trans (d7.trans d8)))))),
    e5, by rw [cD]; exact cl.last, cl.named, cl.notZero, by rw [cD]; exact cl.asked⟩
  subst w3
  have eL : L' = { L with list := { L.list with used := used }, handed := true } :=
    congrArg Prod.snd w1
  subst eL
  unfold flatBatch
  refine (Fl.bind_eq a1).trans ?_
  refine (Fl.bind_eq a2).trans ?_
  refine (Fl.bind_eq a3).trans ?_
  refine (Fl.bind_eq a4).trans ?_
  refine (Fl.bind_eq a5).trans ?_
  refine (Fl.bind_eq a6).trans ?_
  refine (Fl.bind_eq a7).trans ?_
  refine (Fl.bind_eq a8).trans ?_
  rfl

/-- One field of `FrameKeepsView`. -/
theorem batch_keeps (used : Nat) (L L' : LinkCtx) (F G : Fork) (C D : Ctx) (u : Unit)
    (hd : C.ch.dry = false) (H : RunsL (Model.t2Batch used) L F C u L' G D) : D.ch.dry = false :=
  (lawBatch used L L' F G C D u hd H).2.1.dry

/-- `FrameKeepsView` from its two other fields. -/
theorem frameKeeps_of
    (root : ∀ (trees : List Nat) (L L' : LinkCtx) (F G : Fork) (C D : Ctx) (u : Unit),
      C.ch.dry = false → RunsL (Model.rootInH trees) L F C u L' G D → D.ch.dry = false)
    (transcript : ∀ (tl tl' : Model.HTailF2) (L L' : LinkCtx) (F G : Fork) (C D : Ctx),
      C.ch.dry = false → RunsL tl.transcript L F C tl' L' G D → D.ch.dry = false) :
    FrameKeepsView :=
  ⟨root, transcript, batch_keeps⟩

/-- **The whole check of the head's sub-proof, opened**, under what is left of the named hypotheses:
that the two steps which receive commitments, run on a view, leave a run on a view. -/
theorem run_open_view
    (root : ∀ (trees : List Nat) (L L' : LinkCtx) (F G : Fork) (C D : Ctx) (u : Unit),
      C.ch.dry = false → RunsL (Model.rootInH trees) L F C u L' G D → D.ch.dry = false)
    (transcript : ∀ (tl tl' : Model.HTailF2) (L L' : LinkCtx) (F G : Fork) (C D : Ctx),
      C.ch.dry = false → RunsL tl.transcript L F C tl' L' G D → D.ch.dry = false) : LawRun :=
  run_open (frameKeeps_of root transcript) tailQuiet

/-! ## The step that hands the one equation on -/

/-- The one equation in which a sub-proof ends, before it goes to the chain; and the number of
claims that were added. -/
structure DoorOut where
  /-- the weights on the committed arrays -/
  terms : Array ReqTerm
  /-- the coefficients on the first entries of the link's mask row -/
  onMasks : Array E
  /-- the constant; the chain is given its negative as the target -/
  constant : E
  /-- the number of claims that were added -/
  claims : Nat

section Door

open OnBytes.Model (doorTerms laidAs)

/-- The text of `Model.doorH` up to the equation. -/
def doorEq : LinkM DoorOut := do
  let L ← get
  LinkM.mustAs "internal-t2-order" (L.list.link && !L.list.walked && !L.done)
  LinkM.sub (SubM.change fun F => some { F with doorShutF := true })
  LinkM.mustAs "internal-t2-order" L.handed
  let F ← LinkM.fork
  LinkM.mustAs "internal-f-door" (F.planClaimsF != 0 && F.nClaim == F.planClaimsF)
  LinkM.sub SubM.allTaken
  LinkM.testAs "internal-f-door" ((F.trees.extract L.list.nt.size F.trees.size).all fun X =>
    X.rows.all fun r => r.L.all isZeroE)
  LinkM.mustAs "plan-link" (L.arrayOf.size == L.list.nt.size)
  LinkM.must (decide (L.list.nt.size ≤ F.trees.size))
  let mut terms : Array ReqTerm := #[]
  for ti in List.range L.list.nt.size do
    let (born, array) := L.arrayOf.getD ti (0, "")
    let X := F.trees.getD ti {}
    LinkM.must (laidAs L.check born array X.R X.K)
    terms := terms ++ (← LinkM.sub (doorTerms born array X))
  let mc ← LinkM.sub (SubM.settle L.list.used)
  pure { terms := terms, onMasks := mc.1, constant := mc.2, claims := F.nClaim }

/-- The rest of it. -/
def doorSend (equationsLaid : Nat) (e : DoorOut) : LinkM Unit := do
  LinkM.sub (SubM.batchRows (e.claims + equationsLaid))
  LinkM.call fun c =>
    c.close { terms := e.terms, onMasks := e.onMasks, target := subE zeroE e.constant }
  modify fun L => { L with list := { L.list with walked := true }, done := true }

end Door

/-- **The routine is the one after the other.** -/
theorem doorH_split (equationsLaid : Nat) :
    Model.doorH equationsLaid = doorEq >>= doorSend equationsLaid := by
  unfold Model.doorH doorEq doorSend
  simp only [bind_assoc, pure_bind]
  <;> rfl

theorem quietL_forInL (f : γ → σ → LinkM (ForInStep σ)) (hf : ∀ x s, QuietL (f x s)) :
    ∀ (l : List γ) (s : σ), QuietL (forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    infer_instance
  | x :: l, s => by
    rw [List.forIn_cons]
    refine qbL (hf x s) fun r => ?_
    cases r with
    | done b => exact quietL_pure b
    | yield b => exact quietL_forInL f hf l b

instance quietL_doorEq : QuietL doorEq := by
  unfold doorEq
  repeat' first
    | infer_instance
    | refine qbL ?_ ?_
    | intro _
    | refine quietL_forInL _ ?_ _ _
    | split

/-- The one equation that goes out of a sub-proof, on the link's record and the ledger alone. -/
def flatDoor (L : LinkCtx) : Fork → Option ((DoorOut × LinkCtx) × Fork) := still (doorEq L)

/-- What a run of `Model.doorH` on a view has done. -/
structure DoorFacts (equationsLaid : Nat) (L L' : LinkCtx) (F G : Fork) (C D : Ctx) (e : DoorOut)
    (L1 : LinkCtx) (C1 : Ctx) (entry : Fmt.Entry) (check : Model.ChainCheck) : Prop where
  equation : flatDoor L F = some ((e, L1), G)
  ctx : Blk.SameButNotes C C1
  last : C1.ch.last = some entry
  rows : entry.rows = e.claims + equationsLaid
  link : (L1.link == L1.check.link) = true
  chain : (L1.check.close
      { terms := e.terms, onMasks := e.onMasks, target := subE zeroE e.constant }).Yields
    { C1 with ch := { C1.ch with askedRows := true } } check D
  record : L' = { L1 with
    check := check, list := { L1.list with walked := true }, done := true }

/-- **The step that hands the one equation on, opened.** -/
theorem door_open (equationsLaid : Nat) (L L' : LinkCtx) (F G : Fork) (C D : Ctx) (u : Unit)
    (hd : C.ch.dry = false) (H : RunsL (Model.doorH equationsLaid) L F C u L' G D) :
    ∃ e L1 C1 entry check, DoorFacts equationsLaid L L' F G C D e L1 C1 entry check := by
  rw [doorH_split] at H
  obtain ⟨e, L1, F1, C1, h1, H1⟩ := stepL H
  haveI := quietL_doorEq.quiet L
  obtain ⟨l1, l2⟩ := lawStill (doorEq L) F F1 C (e, L1) hd
  have eq1 := l1.mp ⟨C1, h1⟩
  have c1 := l2 C1 h1
  have d1 := dry_of_same c1 hd
  unfold doorSend at H1
  obtain ⟨_, F2, C2, s2, H2⟩ := stepSub H1
  obtain ⟨b2, f2⟩ := (sub_lift _ _ _ _ _ _).mp s2
  subst f2
  obtain ⟨entry, q1, q2, q3⟩ := Slice.requireRows_inv _ _ _ d1 b2
  subst q3
  obtain ⟨_, L3, F3, C3, s3, H3⟩ := stepL H2
  have s3' : ((SubM.must (L1.link == L1.check.link) >>= fun _ =>
      (liftM (L1.check.close
        { terms := e.terms, onMasks := e.onMasks, target := subE zeroE e.constant }) :
        SubM Model.ChainCheck) >>= fun check =>
      (pure ((), { L1 with check := check }) : SubM (Unit × LinkCtx))) F2).Yields _
      (((), L3), F3) C3 := s3
  obtain ⟨_, F4, C4, t1, t2⟩ := (sub_bind _ _ _ _ _ _ _).mp s3'
  obtain ⟨m1, m2, m3⟩ := (sub_must _ _ _ _ _).mp t1
  subst m2
  subst m3
  obtain ⟨check, F5, C5, t3, t4⟩ := (sub_bind _ _ _ _ _ _ _).mp t2
  obtain ⟨k1, k2⟩ := (sub_lift _ _ _ _ _ _).mp t3
  subst k2
  obtain ⟨w1, w2, w3⟩ := (sub_pure _ _ _ _ _ _).mp t4
  subst w2
  subst w3
  have eL3 : L3 = { L1 with check := check } := congrArg Prod.snd w1
  subst eL3
  have H3' : ((pure (PUnit.unit,
      { ({ L1 with check := check } : LinkCtx) with
        list := { L1.list with walked := true }, done := true }) :
      SubM (PUnit × LinkCtx)) F3).Yields C3 ((u, L'), G) D := H3
  obtain ⟨v1, v2, v3⟩ := (sub_pure _ _ _ _ _ _).mp H3'
  subst v2
  subst v3
  exact ⟨e, L1, C1, entry, check, ⟨eq1, c1, q1, q2, m1, k1, congrArg Prod.snd v1⟩⟩

/-- **The entry whose rows the door counts is the batching round's.** From the facts of a run of the
head's whole check: the draw of the batching element as an equation in its flat function; the door's
facts; and the plan's entry whose number of rows is held against the number of claims and equations
is the entry under which the batching element's round was closed. -/
theorem run_door {h : Model.Head.Shape} {L : Model.Head.HL} {b : Model.Head.Border}
    {hp : Model.Head.HPlanH2} {O : Model.Head.Owner} {cov : Model.Head.Covered} {lay : Model.WsLay}
    {Lc Lc' : LinkCtx} {F G : Fork} {C D : Ctx} {wo : Model.WsForkOut}
    {iU3 : Nat} {x : Model.Head.Heard} {t : Model.Head.Tables} {tl0 tl1 tl2 : Model.HTailF2}
    {claim : Model.WsClaim} {nE : Nat} {Lt Lt' Lw Lw' Ls : LinkCtx}
    {Fh Ft Ft' Fc Fc' Fm Fw Fw' Fs : Fork} {Ch Ct Ct' Cc Cc' Cm Cw Cw' Cs : Ctx}
    (H : HeadRunFacts h L b hp O cov lay Lc Lc' F G C D wo iU3 x t tl0 tl1 tl2 claim nE
      Lt Lt' Lw Lw' Ls Fh Ft Ft' Fc Fc' Fm Fw Fw' Fs Ch Ct Ct' Cc Cc' Cm Cw Cw' Cs) :
    flatBatch Fm.next Lt' { Fm with planClaimsF := hp.nLin } (tape Cm) =
        some (((), Lw), Fw, tape Cw) ∧ Left Cm Cw ∧
      ∃ e L1 C1 entry check, DoorFacts nE Ls Lc' Fs G Cs D e L1 C1 entry check ∧
        Cw.ch.last = some entry ∧ entry.name = Model.RoundName.batSigma.name ∧
        entry.drawNZ = 0 := by
  obtain ⟨fb, lb, e0, l0, n0, z0, _⟩ := lawBatch _ _ _ _ _ _ _ _ H.mergeLeft.dry H.batch
  obtain ⟨e, L1, C1, entry, check, dr⟩ := door_open _ _ _ _ _ _ _ _ H.viewTests H.door
  have k : C1.ch.last = Cw.ch.last := by
    rw [dr.ctx.ch, H.testsCtx.ch, H.walkCtx.ch]
  have ee : entry = e0 := Option.some.inj ((dr.last.symm.trans k).trans l0)
  subst ee
  exact ⟨fb, lb, e, L1, C1, entry, check, dr, l0, n0, z0⟩

end OnBytes.K.Kc

#print axioms OnBytes.K.Kc.run_door
#print axioms OnBytes.K.Kc.lawBatch
#print axioms OnBytes.K.Kc.run_open_view
#print axioms OnBytes.K.Kc.doorH_split
#print axioms OnBytes.K.Kc.door_open
