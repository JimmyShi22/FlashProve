-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Keeps/DoorRan.lean: doorH (OnBytes/Model/Trees.lean), the call with which every
link's routine closes its link, cut in front of its one call on the channel, and taken apart down to
the batching and the fold of the link's group.

doorH tests the link's state, makes the link's one equation out of the sub-proof's state, and hands
it to ChainCheck.close, which takes the rounds of the link's closing. What stands in front of that
call takes no round. OnBytes/Tie/Pv/Keeps/KeepsClose.lean takes ChainCheck.close apart. This file
brings a success of doorH to a success of ChainCheck.close and to that file's records.

Main names:
  Door.doorPre n: the text of doorH n up to the call of ChainCheck.close; it returns the equation.
  Door.doorH_eq: doorH n is doorPre n, then the call, then the mark that the link is walked and
    done.
  Still.same_doorPre, Still.same_row, Still.same_addRow: doorPre, the making of the equation's row
    and its adding to the group take no round and begin none (OnBytes/Tie/Pv/Keeps/StillKit.lean).
  Stays x, doorPre_stays: doorPre leaves the link's own state as it was. DoorRan n L F c L' F' c' eq
    Lm Fm y chk: doorPre has succeeded from L, F, c with the equation eq and left Lm, Fm, y; Lm is
    L; y is no dry run; the open message and the rounds left at y are those at c; the present link
    is the check's; ChainCheck.close of Lm.check at eq has succeeded from y with chk and left c'; F'
    is Fm, and L' is Lm with the check chk, walked and done.
  door_ran: from a success of doorH on a view: there are such eq, Lm, Fm, y, chk.
  door_parts: and with them the records ChainCloseParts and CloseParts: the equation's row, its
    adding to the group, batVerify from a context k3, foldVerify; at k3 the open message and the
    rounds left are those at c.

Limits: one direction: from the call's success, on a view. What the equation is, is not said.
doorPre repeats the port's text: that it is that text is doorH_eq.
-/
import OnBytes.Tie.Pv.Keeps.StillModel
import OnBytes.Tie.Pv.Keeps.KeepsLoop
import OnBytes.Tie.Pv.Keeps.KeepsClose

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.L5.Door
open OnBytes OnBytes.Model

/-- The text of doorH up to the call of ChainCheck.close. -/
def doorPre (equationsLaid : Nat) : LinkM ReqEquation := do
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
  let (onMasks, constant) ← LinkM.sub (SubM.settle L.list.used)
  LinkM.sub (SubM.batchRows (F.nClaim + equationsLaid))
  pure { terms := terms, onMasks := onMasks, target := subE zeroE constant }

theorem doorH_eq (n : Nat) : doorH n = (do
    let eq ← doorPre n
    LinkM.call fun c => c.close eq
    modify fun L => { L with list := { L.list with walked := true }, done := true }) := by
  unfold doorH doorPre
  simp only [bind_assoc, pure_bind]

end OnBytes.L5.Door

namespace OnBytes.L5

keeps_walk OnBytes.L5.Door.doorPre

end OnBytes.L5

namespace OnBytes.Tie.Pv.Keeps.Still
open OnBytes OnBytes.Model OnBytes.L5 OnBytes.L5.Door

keeps_walk OnBytes.L5.Door.doorPre

/-- doorPre takes no round and begins none. -/
theorem same_doorPre {n : Nat} {L : LinkCtx} {F : Fork} {c : Ctx} {eq : ReqEquation}
    {L' : LinkCtx} {G : Fork} {c' : Ctx} (h : doorPre n L F c = .ok (((eq, L'), G), c')) :
    Same c c' := same_link inferInstance h

/-- Making the equation's row takes no round and begins none. -/
theorem same_row {R : ReqRows} {f : ReqFrame} {eq : ReqEquation} {c : Ctx} {rw : Row} {c' : Ctx}
    (h : R.row f eq c = .ok (rw, c')) : Same c c' := same_blk inferInstance h

/-- Adding a row to a group takes no round and begins none. -/
theorem same_addRow {g : Nat} {rw : Row} {c c' : Ctx} (h : Blk.addRow g rw c = .ok ((), c')) :
    Same c c' := same_blk inferInstance h

end OnBytes.Tie.Pv.Keeps.Still

namespace OnBytes.L5
open OnBytes OnBytes.Model OnBytes.L5.Door

/-! ## doorPre leaves the link's own state -/

/-- Wherever the routine succeeds, the link's own state is as it was. -/
def Stays {α : Type} (x : LinkM α) : Prop :=
  ∀ (s : HasRuns.St LinkM) (a : α) (s' : HasRuns.St LinkM), Runs x s a s' → s'.1 = s.1

theorem Stays.pure {α : Type} (a : α) : Stays (pure a : LinkM α) := fun _ _ _ h =>
  congrArg Prod.fst (HasRuns.runs_pure h).2

theorem Stays.bind {α β : Type} {x : LinkM α} {f : α → LinkM β} (hx : Stays x)
    (hf : ∀ a, Stays (f a)) : Stays (x >>= f) := fun s b s' h => by
  obtain ⟨a, s1, h1, h2⟩ := HasRuns.runs_bind h
  exact (hf a _ _ _ h2).trans (hx _ _ _ h1)

theorem Stays.sub {α : Type} (x : SubM α) : Stays (LinkM.sub x) := fun _ _ _ h => (runs_sub h).2

theorem Stays.get : Stays (get : LinkM LinkCtx) := fun _ _ _ h =>
  congrArg Prod.fst (runs_get h).2

theorem Stays.forInL {γ β : Type} (f : γ → β → LinkM (ForInStep β)) (hf : ∀ a b, Stays (f a b)) :
    ∀ (l : List γ) (b : β), Stays (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact Stays.pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine Stays.bind (hf a b) fun r => ?_
    cases r with
    | done b' => exact Stays.pure b'
    | yield b' => exact Stays.forInL f hf l b'

theorem doorPre_stays (n : Nat) : Stays (doorPre n) := by
  unfold doorPre
  repeat' first
    | exact Stays.pure _
    | exact Stays.get
    | exact Stays.sub _
    | refine Stays.forInL _ (fun _ _ => ?_) _ _
    | refine Stays.bind ?_ fun _ => ?_
    | split

/-- doorH, cut in front of its one call on the channel. -/
structure DoorRan (n : Nat) (L : LinkCtx) (F : Fork) (c : Ctx) (L' : LinkCtx) (F' : Fork)
    (c' : Ctx) (eq : ReqEquation) (Lm : LinkCtx) (Fm : Fork) (y : Ctx) (chk : ChainCheck) :
    Prop where
  pre : doorPre n L F c = .ok (((eq, Lm), Fm), y)
  stays : Lm = L
  view : y.ch.dry = false
  cur : y.ch.cur = c.ch.cur
  left : y.ch.left = c.ch.left
  atLink : (Lm.link == Lm.check.link) = true
  close : Lm.check.close eq y = .ok (chk, c')
  fork : F' = Fm
  link : L' = { Lm with check := chk, list := { Lm.list with walked := true }, done := true }

theorem door_ran (n : Nat) {L L' : LinkCtx} {F F' : Fork} {c c' : Ctx} (hd : c.ch.dry = false)
    (h : doorH n L F c = .ok ((((), L'), F'), c')) :
    ∃ eq Lm Fm y chk, DoorRan n L F c L' F' c' eq Lm Fm y chk := by
  rw [doorH_eq] at h
  have hr : Runs (do
      let eq ← doorPre n
      LinkM.call fun c => c.close eq
      modify fun L => { L with list := { L.list with walked := true }, done := true } :
        LinkM Unit) (L, F, c) () (L', F', c') := h
  obtain ⟨eq, ⟨Lm, Fm, y⟩, r1, d1, k1⟩ := step hr hd
  obtain ⟨u, ⟨L2, F2, y2⟩, r2, k2⟩ := HasRuns.runs_bind k1
  have e2 := runs_modify k2
  -- the call, by its text
  have r2' : Runs (m := SubM) (do
      SubM.must (Lm.link == Lm.check.link)
      let check ← (liftM (Lm.check.close eq) : SubM ChainCheck)
      pure ((), { Lm with check := check })) (Fm, y) (u, L2) (F2, y2) := r2
  obtain ⟨_, ⟨F3, y3⟩, q1, q2⟩ := HasRuns.runs_bind r2'
  obtain ⟨q1', f1⟩ := runs_lift (σ := Fork) (x := Blk.must (Lm.link == Lm.check.link)) q1
  obtain ⟨hb, ey⟩ := runs_must q1'
  obtain ⟨chk, ⟨F4, y4⟩, q3, q4⟩ := HasRuns.runs_bind q2
  obtain ⟨q3', f3⟩ := runs_up (σ := Fork) (x := Lm.check.close eq) q3
  obtain ⟨e4, e5⟩ := HasRuns.runs_pure q4
  have s := Tie.Pv.Keeps.Still.same_doorPre r1
  have hF3 : F3 = Fm := f1
  have hy3 : y3 = y := ey
  have hF4 : F4 = F3 := f3
  have hL2 : L2 = { Lm with check := chk } := congrArg Prod.snd e4
  have h24 : (F2, y2) = (F4, y4) := e5
  have hF2 : F2 = F4 := congrArg Prod.fst h24
  have hy2 : y2 = y4 := congrArg Prod.snd h24
  have hL' : L' = { L2 with list := { L2.list with walked := true }, done := true } :=
    congrArg Prod.fst e2
  have hFc : (F', c') = (F2, y2) := congrArg Prod.snd e2
  have hF' : F' = F2 := congrArg Prod.fst hFc
  have hc' : c' = y2 := congrArg Prod.snd hFc
  subst hy3 hF3 hF4 hF2 hy2 hL2 hF' hc'
  exact ⟨eq, Lm, _, _, chk, r1, doorPre_stays n _ _ _ r1, d1, s.cur, s.left, hb, q3', rfl, hL'⟩

/-- doorH down to the batching and the fold of the link's group: the records of
OnBytes/Tie/Pv/Keeps/KeepsClose.lean at the check and the equation of DoorRan; and at the context k3
from which batVerify runs the open message and the rounds left are those at c. -/
theorem door_parts (n : Nat) {L L' : LinkCtx} {F F' : Fork} {c c' : Ctx} (hd : c.ch.dry = false)
    (h : doorH n L F c = .ok ((((), L'), F'), c')) :
    ∃ eq Lm Fm y chk rw fr k2 k3 Lk G row layout rows k4 k6 k7,
      DoorRan n L F c L' F' c' eq Lm Fm y chk ∧
      Close.ChainCloseParts Lm.check eq c' y chk c' rw fr k2 k3 ∧
      Close.CloseParts Lm.check.frame c' k3 fr c' Lk G row layout rows k4 k6 k7 ∧
      k3.ch.cur = c.ch.cur ∧ k3.ch.left = c.ch.left := by
  obtain ⟨eq, Lm, Fm, y, chk, D⟩ := door_ran n hd h
  obtain ⟨rw, fr, k2, k3, Lk, G, row, layout, rows, k4, k6, k7, P, Q, _⟩ :=
    Close.chain_close_parts Lm.check eq (cEnd := c') D.view id D.close
  have s1 := Tie.Pv.Keeps.Still.same_row P.row
  have s2 := Tie.Pv.Keeps.Still.same_addRow P.added
  exact ⟨eq, Lm, Fm, y, chk, rw, fr, k2, k3, Lk, G, row, layout, rows, k4, k6, k7, D, P, Q,
    s2.cur.trans (s1.cur.trans D.cur), s2.left.trans (s1.left.trans D.left)⟩

end OnBytes.L5

#print axioms OnBytes.L5.Door.doorH_eq
#print axioms OnBytes.L5.door_ran
#print axioms OnBytes.L5.door_parts
#print axioms OnBytes.L5.doorPre_stays
