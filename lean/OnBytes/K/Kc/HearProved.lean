-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/K/Kc/HearProved.lean: the flat function `flatHear` (OnBytes/K/Kc/FlatHear.lean) returns what
the program's routine returns, in every run on a view in which that succeeds: the whole receiving
side of the output head's check, GIVEN the same of the lookup's messages.

The statements, each a definition of its own name: `LawPad` (the lookup's messages,
`Model.Forest.pad`) and `LawHear` (`Model.Head.hear`). `Sim` is explained in
OnBytes/K/Kc/Laws.lean: all states are letters of the statement, tied at both ends. `LawPad` is a
hypothesis of this file's main theorem, which this file does not prove.

Further rules, beside those of OnBytes/K/Kc/Kit.lean: `Sim.ite` (a choice on a public condition),
`Sim.mustAs`, `Sim.testAs` (a named condition; in a run on a view a condition on values that passes
was true), `Sim.held`, `Sim.getAs`, `Sim.after_note` (a call that keeps an intermediate value leaves
the rounds as they were).

Main theorem: `lawHear_of`: `LawPad` → `LawHear`.

Not claimed. One direction alone, as in OnBytes/K/Kc/Laws.lean. Nothing on the dry run. Nothing on
soundness. The program does not import this file.
-/
import OnBytes.K.Kc.FlatHear
import OnBytes.K.Kc.Proved

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Kc

open OnBytes.Model (Fork SubM Aff Psc Tsc Level RoundForm)

variable {α β : Type}

/-- The lookup's messages. -/
def LawPad : Prop :=
  ∀ (calls : Array Model.Call) (pub : Array Nat) (lid : Nat),
    Sim (Model.Forest.pad calls pub lid) (lkPad calls pub lid)

/-- The whole receiving side of the head's check. -/
def LawHear : Prop :=
  ∀ (h : Model.Head.Shape) (L : Model.Head.HL) (hp : Model.Head.HPlanH2) (cov : Model.Head.Covered)
    (plain : Array E), Sim (Model.Head.hear h L hp cov plain) (flatHear h L hp cov plain)

/-! ## Further rules -/

theorem Sim.ite {c : Prop} {inst : Decidable c} {X Y : SubM α} {f g : Fl α} (h1 : Sim X f)
    (h2 : Sim Y g) : Sim (@_root_.ite _ c inst X Y) (@_root_.ite _ c inst f g) := by
  cases inst with
  | isTrue hc => exact h1
  | isFalse hc => exact h2

theorem Sim.mustAs (n : String) (b : Bool) :
    Sim (monadLift (Model.mustAs n b) : SubM Unit) (Fl.must b) := by
  intro F G C D u hd r
  have r' : ((StateT.lift (Model.mustAs n b) : SubM Unit) F).Yields C (u, G) D := r
  obtain ⟨r1, rfl⟩ := (sub_lift _ _ _ _ _ _).mp r'
  obtain ⟨rfl, rfl⟩ := mustAs_inv _ _ _ _ _ r1
  exact ⟨rfl, Left.refl hd⟩

/-- In a run on a view: a condition on values under a name that passes was true, and it changes
nothing. -/
theorem testAs_inv (n : String) (b : Bool) (c c' : Ctx) (u : Unit) (hd : c.ch.dry = false)
    (h : (Model.testAs n b).Yields c u c') : b = true ∧ c' = c := by
  unfold Model.testAs at h
  obtain ⟨d, c1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).mp h
  obtain ⟨e1, e2⟩ := (Slice.yields_isDry _ _ _).mp h1
  subst e2
  rw [hd] at e1
  subst e1
  cases b with
  | false => cases k1
  | true =>
    obtain ⟨_, e3⟩ := (Blk.yields_pure _ _ _ _).mp k1
    exact ⟨rfl, e3⟩

theorem Sim.testAs (n : String) (b : Bool) :
    Sim (monadLift (Model.testAs n b) : SubM Unit) (Fl.must b) := by
  intro F G C D u hd r
  have r' : ((StateT.lift (Model.testAs n b) : SubM Unit) F).Yields C (u, G) D := r
  obtain ⟨r1, rfl⟩ := (sub_lift _ _ _ _ _ _).mp r'
  obtain ⟨rfl, rfl⟩ := testAs_inv _ _ _ _ _ hd r1
  exact ⟨rfl, Left.refl hd⟩

theorem Sim.held (x : Except String α) :
    Sim (monadLift (Model.Head.held x) : SubM α) (Fl.need x.toOption) := by
  intro F G C D a hd r
  have r' : ((StateT.lift (Model.Head.held x) : SubM α) F).Yields C (a, G) D := r
  obtain ⟨r1, rfl⟩ := (sub_lift _ _ _ _ _ _).mp r'
  cases x with
  | error s => cases r1
  | ok y =>
    obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).mp r1
    exact ⟨rfl, Left.refl hd⟩

theorem Sim.getAs (n : String) (x : Option α) :
    Sim (monadLift (Model.Head.getAs n x) : SubM α) (Fl.need x) := by
  intro F G C D a hd r
  have r' : ((StateT.lift (Model.Head.getAs n x) : SubM α) F).Yields C (a, G) D := r
  obtain ⟨r1, rfl⟩ := (sub_lift _ _ _ _ _ _).mp r'
  cases x with
  | none => cases r1
  | some y =>
    obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).mp r1
    exact ⟨rfl, Left.refl hd⟩

theorem Sim.after_note (w : String) (v : E) {K : Unit → SubM β} {f : Fl β} (h : Sim (K ()) f) :
    Sim (Model.Head.noteH w v >>= K) f := by
  intro F G C D b hd r
  obtain ⟨u, F1, C1, r1, r2⟩ := (sub_bind _ _ _ _ _ _ _).mp r
  obtain ⟨y1, rfl⟩ := (sub_lift _ _ _ _ _ _).mp r1
  have s := Blk.yields_note _ _ _ _ y1
  have d1 := Left.of_same hd s
  obtain ⟨e2, d2⟩ := h _ G C1 D b d1.dry r2
  have t : tape C1 = tape C := by
    unfold tape
    rw [s.ch]
  rw [t] at e2
  exact ⟨e2, d1.trans d2⟩

theorem sim_slot : Sim SubM.slot Fl.slot := Sim.ask _

theorem sim_owe (what : String) : Sim (SubM.owe what) (Fl.owe what) := Sim.take _

theorem sim_slots (n : Nat) : Sim (SubM.slots n) (Fl.slots n) := Sim.change _

/-! ## The head -/

theorem sim_replyToken (plain : Array E) (V : Nat) :
    Sim (Model.Head.replyToken plain V) (flatReplyToken plain V) := by
  unfold Model.Head.replyToken flatReplyToken
  refine Sim.bind (Sim.mustAs _ _) fun _ => ?_
  refine Sim.bind (Sim.testAs _ _) fun _ => ?_
  exact Sim.pure _

theorem sim_mergedPoint (h : Model.Head.Shape) (g1 : Model.Forest.Heard) :
    Sim (Model.Head.mergedPoint h g1) (flatMergedPoint h g1) := by
  unfold Model.Head.mergedPoint flatMergedPoint
  refine Sim.bind (Sim.held _) fun Zl => ?_
  refine Sim.bind (Sim.testAs _ _) fun _ => ?_
  exact Sim.pure _

/-- **The whole receiving side of the head's check**, given the law of the lookup's messages. -/
theorem lawHear_of (hpad : LawPad) : LawHear := by
  intro h L hp cov plain
  unfold Model.Head.hear flatHear
  refine Sim.bind (sim_replyToken _ _) fun yTok => ?_
  refine Sim.bind (sim_slots _) fun _ => ?_
  refine Sim.bind (hpad _ _ _) fun g1 => ?_
  refine Sim.bind (sim_mergedPoint h g1) fun Zl => ?_
  refine Sim.bind (sim_point _ _) fun PV => ?_
  refine Sim.bind (lawSquares h PV) fun x => ?_
  obtain ⟨sW, gp, wpl⟩ := x
  refine Sim.bind (lawProducts h PV) fun x => ?_
  obtain ⟨sPv, omV, tV⟩ := x
  refine Sim.bind (Sim.getAs _ _) fun qN => ?_
  refine Sim.bind (Sim.getAs _ _) fun qH => ?_
  refine Sim.bind (lawStream h _) fun tN => ?_
  refine Sim.bind (lawLogits h _ _) fun x => ?_
  obtain ⟨tH, rs⟩ := x
  refine Sim.after_note _ _ ?_
  refine Sim.after_note _ _ ?_
  refine Sim.after_note _ _ ?_
  refine Sim.after_note _ _ ?_
  refine Sim.after_note _ _ ?_
  refine Sim.after_note _ _ ?_
  refine Sim.after_note _ _ ?_
  refine Sim.after_note _ _ ?_
  refine Sim.after_note _ _ ?_
  refine Sim.after_note _ _ ?_
  refine Sim.after_note _ _ ?_
  refine Sim.after_note _ _ ?_
  exact Sim.pure _

end OnBytes.K.Kc

#print axioms OnBytes.K.Kc.lawHear_of
