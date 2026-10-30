-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Switch/LocClean.lean: behind a run of the program's code switch between two groups of
a request's chain, on a view, no message is open.

OnBytes/Tie/Pv/Switch/LocView.lean speaks of the rounds not yet taken (`Chan.pending`: the open
round, if there is one, then the rounds not begun). The block that follows wants more: that its
first round is a whole round of the view. The closing of the round LOC leaves no message open
(`PscRun.close_view`, OnBytes/Tie/Pv/Psc/PscView.lean). Behind it the switch reads opened columns
and admits its claims. The library's law on the reading (`Blk.Frame`, OnBytes/Iop/OpenLaws.lean)
names `pending`, not the open round. Here: these calls leave the open round as it was. Statements
and proofs.

Main names:
  `takeColumns_cur`, `countOpening_cur`, `openTreesInto_cur`, `readOpened_cur`,
    `singleRowsRead_cur`: on a view each of these calls leaves `c.ch.cur` as it was.
  `LocRan.clean`: behind the run: a view, no message open (`PscRun.Clean c'`).
  `LocRan.took`: if no message is open before the run either: `PscRun.Took c [r₁, r₂] c'`, with what
    the two rounds hold (as in `LocRan.view_rows`, OnBytes/Tie/Pv/Switch/LocAnswers.lean).
Limits: on a view alone; one direction: from a run's record.

-/
import OnBytes.Tie.Pv.Switch.LocAnswers
import OnBytes.Tie.Pv.Psc.PscView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Switch
open OnBytes OnBytes.Slice

theorem takeColumns_cur (t : Tree) (xs : Array Nat) (cols : Array (Array F)) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : (Blk.takeColumns t xs).Yields c cols c') :
    c'.ch.cur = c.ch.cur := by
  rw [Blk.yields_iff] at h
  unfold Blk.takeColumns at h
  simp only [hd, Bool.false_eq_true, if_false] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  · cases h

theorem countOpening_cur (t : Nat) (c c' : Ctx) (h : (Blk.countOpening t).Yields c () c') :
    c'.ch = c.ch := by
  unfold Blk.countOpening at h
  obtain ⟨S, c1, h1, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨rfl, rfl⟩ := (Blk.yields_statement _ _ _).1 h1
  obtain ⟨B, c2, h2, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨rfl, rfl⟩ := (Blk.yields_theBook _ _ _).1 h2
  obtain ⟨tree, c3, h3, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := (Blk.yields_get _ _ _ _).1 h3
  dsimp only at h
  obtain ⟨_, c4, h4, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := (Blk.yields_must _ _ _).1 h4
  obtain ⟨_, c5, h5, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := (Blk.yields_must _ _ _).1 h5
  rw [Blk.yields_setBook] at h
  subst h
  rfl

theorem openTreesInto_cur (B : TreeBook) (pos : Positions) :
    ∀ (ts : List Nat) (acc : Array (Nat × Array Nat × Array (Array F)))
      (all : List (Nat × Array Nat × Array (Array F))) (c c' : Ctx),
    c.ch.dry = false → (Blk.openTreesInto B pos ts acc).Yields c all c' → c'.ch.cur = c.ch.cur
  | [], acc, all, c, c', _, h => by
    unfold Blk.openTreesInto at h
    obtain ⟨-, rfl⟩ := (Blk.yields_pure _ _ _ _).1 h
    rfl
  | t :: ts, acc, all, c, c', hd, h => by
    unfold Blk.openTreesInto at h
    obtain ⟨_, c1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    have e1 := countOpening_cur t c c1 h1
    have d1 : c1.ch.dry = false := by rw [e1]; exact hd
    obtain ⟨tree, c2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 k1
    obtain ⟨_, e2⟩ := (Blk.yields_get _ _ _ _).1 h2
    subst e2
    obtain ⟨_, c3, h3, k3⟩ := (Blk.yields_bind _ _ _ _ _).1 k2
    obtain ⟨_, e3⟩ := (Blk.yields_must _ _ _).1 h3
    subst e3
    obtain ⟨cols, c4, h4, k4⟩ := (Blk.yields_bind _ _ _ _ _).1 k3
    have e4 := takeColumns_cur _ _ _ _ _ d1 h4
    have d4 : c4.ch.dry = false := ((Blk.takeColumns_inv _ _ _ _ _ d1 h4).2.2.1.dry).trans d1
    rw [openTreesInto_cur B pos ts _ all c4 c' d4 k4, e4, e1]

theorem readOpened_cur (ids : Array Nat) (pos : Positions) (out : Array (Array Column))
    (c c' : Ctx) (hd : c.ch.dry = false) (h : (Blk.readOpened ids pos).Yields c out c') :
    c'.ch.cur = c.ch.cur := by
  unfold Blk.readOpened at h
  obtain ⟨S, c1, h1, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨rfl, rfl⟩ := (Blk.yields_statement _ _ _).1 h1
  obtain ⟨B, c2, h2, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨rfl, rfl⟩ := (Blk.yields_theBook _ _ _).1 h2
  obtain ⟨places, c3, h3, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := (Blk.yields_get _ _ _ _).1 h3
  dsimp only at h
  obtain ⟨_, c4, h4, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := (Blk.yields_must _ _ _).1 h4
  obtain ⟨cols, c5, h5, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := (Blk.yields_get _ _ _ _).1 h
  exact openTreesInto_cur _ _ _ _ _ _ _ hd h5

theorem singleRowsRead_cur (s : SingleRows) (pos : Positions) (y : Array E) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : (singleRowsRead s pos).Yields c y c') : c'.ch.cur = c.ch.cur := by
  obtain ⟨opened, h1, _⟩ := singleRowsRead_inv s pos y c c' h
  exact readOpened_cur _ _ _ _ _ hd h1

/-- Behind the run no message is open. -/
theorem LocRan.clean {old : SingleRows} {T : SwitchTarget} {gp : Nat} {others : Array OracleNotice}
    {out : Switched} {c c' : Ctx} {D : LocTaken} (R : LocRan old T gp others out c c' D)
    (hd : c.ch.dry = false) : PscRun.Clean c' := by
  have d0 : D.c0.ch.dry = false := by rw [R.received]; exact hd
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, s5, _⟩ :=
    Blk.close_inv _ _ _ _ _ _ d0 R.seedRound
  obtain ⟨_, _, _, dA⟩ := sampleSteps_view _ _ _ _ _ s5 R.answers
  obtain ⟨_, _, _, _, _, _, _, _, hB, _⟩ :=
    PscRun.close_view _ _ _ _ _ _ dA ((Blk.yields_iff _ _ _ _).1 R.locRound)
  have fC := singleRowsRead_frame _ _ _ _ _ hB.1 R.read
  have dD : D.cD.ch.dry = false := by rw [R.notes.ch, fC.dry]; exact hB.1
  have e : c'.ch = D.cC.ch := by
    rw [switchAdmit_ch _ _ _ _ _ _ _ dD R.admitted, R.notes.ch]
  refine ⟨by rw [e, fC.dry]; exact hB.1, ?_⟩
  rw [e, singleRowsRead_cur _ _ _ _ _ hB.1 R.read]
  exact hB.2

/-- THE TWO ROUNDS, WHOLE: if no message is open before the run, the run has taken two whole rounds
of the view. -/
theorem LocRan.took {old : SingleRows} {T : SwitchTarget} {gp : Nat} {others : Array OracleNotice}
    {out : Switched} {c c' : Ctx} {D : LocTaken} (R : LocRan old T gp others out c c' D)
    (hc : PscRun.Clean c) :
    ∃ (r₁ r₂ : Fmt.RoundView) (rowss : List (Array Row)), PscRun.Took c [r₁, r₂] c' ∧
      r₁.vals = [] ∧ r₁.drawn = D.dS ∧
      Admitted D.c0.st D.seeds ((todoOf D.c0.st D.ids).zip D.shapes) rowss D.c1 D.cA ∧
      r₂.vals = (rowss.flatMap targets).map (fun x => Fmt.ItemValue.answer x.triple) ∧
      r₂.drawn = D.dL := by
  obtain ⟨r₁, r₂, rowss, h1, h2, h3, h4, h5, h6, _⟩ := R.view_rows hc.1
  have hc' := R.clean hc.1
  have p : c.ch.pending = c.ch.left := by simp [Chan.pending, hc.2]
  have p' : c'.ch.pending = c'.ch.left := by simp [Chan.pending, hc'.2]
  rw [p, p'] at h1
  exact ⟨r₁, r₂, rowss, ⟨hc, hc', h1⟩, h2, h3, h4, h5, h6⟩

end OnBytes.Tie.Pv.Switch

#print axioms OnBytes.Tie.Pv.Switch.LocRan.clean
#print axioms OnBytes.Tie.Pv.Switch.LocRan.took
