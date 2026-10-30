-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/FitCalc.lean: a property of entries that every routine of the planner keeps: the
general laws.

A routine of the planner (Planning, OnBytes/Params/Planner.lean) runs on a plan that is being
written. KeepsAt s Q m m' x R says: wherever x ends well from a state with the setting s, with m
roots open, all of whose entries have the property Q, the setting is still s, m' roots are open, all
entries of the new state have Q, and the value that x returns has R. Keeps s Q x R is that with no
root open before and behind. No list of rounds is written out and no price is read: for a property
of single entries that does not hang on the bytes and answers which the prover has sent since the
last round. (For what does, see Runs, OnBytes/Params/PlanningLaws.lean.)

Main names:
  AllQ Q p: every entry of the plan p has Q.
  KeepsAt s Q m m' x R; Keeps s Q x R := KeepsAt s Q 0 0 x R. The laws are stated for KeepsAt and
    serve both.
  keeps_pure, keeps_bind, keeps_mono, keeps_setting, keeps_scope, keeps_needs, keeps_must,
    keeps_refuse, keeps_ite, keeps_modify (for a change of the state that leaves setting and
    rounds), keeps_scalars, keeps_answers, keeps_roots (n roots more are open), keeps_push,
    keeps_closeNone, keeps_close (Q is asked at the open roots; none is open behind), keeps_times,
    keeps_forEach.
  finish_all, finishHeld_all: so every entry of a finished plan has Q.
  Small e: the instance for which the laws were made: the entry's name is in order (NameOk), it
    counts at most two roots, logN ≤ 64, and its four numbers of draws are far below what 2 ^ 48
    blocks of a hash chain's answer hold (small_blocks, FitBlocks.lean in this folder). SetCap s:
    what the laws on the planner's routines (FitSmall.lean in this folder) ask of the setting.
Limits: of a routine that refuses nothing is said. Nothing is said of the scope. Nothing on any
routine that plans a block.
The program does not import this file.

-/
import OnBytes.Params.PlanningLaws
import Fmt.ParamsReadLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

/-- Every entry of the plan that is being written has Q. -/
def AllQ (Q : Fmt.Entry → Prop) (p : PlanState) : Prop := ∀ r ∈ p.rounds.toList, Q r.entry

/-- Wherever x ends well from a state with the setting s and m open roots whose entries have Q: the
setting stays, m' roots are open, the entries have Q, the value has R. -/
def KeepsAt (s : Setting) (Q : Fmt.Entry → Prop) (m m' : Nat) {α : Type} (x : Planning α)
    (R : α → Prop := fun _ => True) : Prop :=
  ∀ (p q : PlanState) (a : α), p.set = s → p.openRoots = m → AllQ Q p → x p = .ok (a, q) →
    q.set = s ∧ q.openRoots = m' ∧ AllQ Q q ∧ R a

/-- No root is open before and behind. -/
abbrev Keeps (s : Setting) (Q : Fmt.Entry → Prop) {α : Type} (x : Planning α)
    (R : α → Prop := fun _ => True) : Prop := KeepsAt s Q 0 0 x R

section
variable {s : Setting} {Q : Fmt.Entry → Prop} {m : Nat}

theorem keeps_pure {α : Type} {R : α → Prop} {a : α} (h : R a) :
    KeepsAt s Q m m (pure a : Planning α) R := by
  intro p q a' hs hm hq e
  have e' : (Except.ok (a, p) : Except String (α × PlanState)) = .ok (a', q) := e
  cases e'
  exact ⟨hs, hm, hq, h⟩

theorem keeps_bind {α β : Type} {x : Planning α} {f : α → Planning β} {R : α → Prop}
    {R' : β → Prop} {m1 m2 : Nat} (h1 : KeepsAt s Q m m1 x R)
    (h2 : ∀ a, R a → KeepsAt s Q m1 m2 (f a) R') : KeepsAt s Q m m2 (x >>= f) R' := by
  intro p q b hs hm hq e
  obtain ⟨a, p1, e1, e2⟩ := bind_ends e
  obtain ⟨s1, o1, q1, r1⟩ := h1 p p1 a hs hm hq e1
  exact h2 a r1 p1 q b s1 o1 q1 e2

/-- A weaker word on the value. -/
theorem keeps_mono {α : Type} {x : Planning α} {R R' : α → Prop} {m' : Nat}
    (h : KeepsAt s Q m m' x R) (hR : ∀ a, R a → R' a) : KeepsAt s Q m m' x R' :=
  fun p q a hs hm hq e =>
    let ⟨h1, h2, h3, h4⟩ := h p q a hs hm hq e
    ⟨h1, h2, h3, hR a h4⟩

/-- No word on the value. -/
theorem KeepsAt.any {α : Type} {x : Planning α} {R : α → Prop} {m' : Nat}
    (h : KeepsAt s Q m m' x R) : KeepsAt s Q m m' x := keeps_mono h fun _ _ => trivial

theorem keeps_setting : KeepsAt s Q m m theSetting (· = s) := by
  intro p q a hs hm hq e
  have e' : (Except.ok (p.set, p) : Except String (Setting × PlanState)) = .ok (a, q) := e
  cases e'
  exact ⟨hs, hm, hq, hs⟩

theorem keeps_scope : KeepsAt s Q m m theScope := by
  intro p q a hs hm hq e
  have e' : (Except.ok (p.scope, p) : Except String (Scope × PlanState)) = .ok (a, q) := e
  cases e'
  exact ⟨hs, hm, hq, trivial⟩

theorem keeps_refuse {α : Type} {R : α → Prop} {m' : Nat} (why : String) :
    KeepsAt s Q m m' (refusePlan why : Planning α) R := by
  intro p q a _ _ _ e
  cases e

/-- A test: behind it the test is true. -/
theorem keeps_needs (t : Bool) (why : String) :
    KeepsAt s Q m m (needs t why) (fun _ => t = true) := by
  unfold needs
  cases t
  · exact keeps_refuse why
  · exact keeps_pure rfl

theorem keeps_must {α : Type} (x : Option α) (why : String) :
    KeepsAt s Q m m (must x why) (fun a => x = some a) := by
  unfold must
  cases x with
  | none => exact keeps_refuse why
  | some a => exact keeps_pure rfl

theorem keeps_ite {α : Type} {R : α → Prop} {m' : Nat} {c : Prop} [Decidable c]
    {x y : Planning α} (h1 : c → KeepsAt s Q m m' x R) (h2 : ¬ c → KeepsAt s Q m m' y R) :
    KeepsAt s Q m m' (if c then x else y) R := by
  split
  · exact h1 ‹_›
  · exact h2 ‹_›

/-- A change of the state that leaves the setting and the rounds, and brings the open roots from m
to m'. -/
theorem keeps_modify {m' : Nat} (f : PlanState → PlanState) (h1 : ∀ p, (f p).set = p.set)
    (h2 : ∀ p, (f p).rounds = p.rounds) (h3 : ∀ p, p.openRoots = m → (f p).openRoots = m') :
    KeepsAt s Q m m' (modify f : Planning PUnit) := by
  intro p q a hs hm hq e
  have e' : (Except.ok (PUnit.unit, f p) : Except String (PUnit × PlanState)) = .ok (a, q) := e
  cases e'
  refine ⟨(h1 p).trans hs, h3 p hm, ?_, trivial⟩
  intro r hr
  rw [h2 p] at hr
  exact hq r hr

theorem keeps_scalars (n : Nat) : KeepsAt s Q m m (planScalars n) :=
  keeps_modify _ (fun _ => rfl) (fun _ => rfl) fun _ h => h

theorem keeps_answers (n : Nat) : KeepsAt s Q m m (planAnswers n) :=
  keeps_modify _ (fun _ => rfl) (fun _ => rfl) fun _ h => h

/-- n roots more are open. -/
theorem keeps_roots (n : Nat) : KeepsAt s Q m (m + n) (planRoots n) :=
  keeps_modify _ (fun _ => rfl) (fun _ => rfl) fun p h => by
    show p.openRoots + n = m + n
    rw [h]

/-- One round more, whose entry has Q. -/
theorem allQ_push {p : PlanState} {r : PlanRound} (hq : AllQ Q p) (hr : Q r.entry)
    (f : PlanState) (hf : f.rounds = p.rounds.push r) : AllQ Q f := by
  intro x hx
  rw [hf, Array.toList_push, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact hq x hx
  · exact hr

theorem keeps_push (r : PlanRound) (hr : Q r.entry) :
    KeepsAt s Q m m (modify fun p => { p with rounds := p.rounds.push r } : Planning PUnit) := by
  intro p q a hs hm hq e
  have e' : (Except.ok (PUnit.unit, ({ p with rounds := p.rounds.push r } : PlanState)) :
      Except String (PUnit × PlanState)) = .ok (a, q) := e
  cases e'
  exact ⟨hs, hm, allQ_push hq hr _ rfl, trivial⟩

/-- A silent round: Q at its entry, whatever bytes and answers are open. It is refused where a root
is open. -/
theorem keeps_closeNone (name : String)
    (h : ∀ msg answers, Q { name, msg := msg, answers := answers }) :
    KeepsAt s Q m 0 (closeNone name) := by
  intro p q a hs _ hq e
  unfold closeNone at e
  split at e
  · cases e
  · rename_i h0
    cases e
    refine ⟨hs, ?_, allQ_push hq (h _ _) _ rfl, trivial⟩
    show p.openRoots = 0
    simpa using h0

/-- A round with a verifier's message: Q at its entry with the open roots, whatever work, bytes and
answers. Behind it no root is open. -/
theorem keeps_close (name : String) (why : ErrorKind) (error : Bound) (d : Draws)
    (h : ∀ work msg answers, Q
      { name, work := work, msg := msg, roots := m, answers := answers, drawE := d.drawE,
        drawNZ := d.drawNZ, poss := d.poss, logN := d.logN, trits := d.trits, rows := d.rows }) :
    KeepsAt s Q m 0 (close name why error d) := by
  intro p q a hs hm hq e
  rw [close_run] at e
  split at e
  · cases e
  · cases e
    subst hm
    exact ⟨hs, rfl, allQ_push hq (h _ _ _) _ rfl, trivial⟩

theorem keeps_times {x : Planning Unit} (h : KeepsAt s Q m m x) :
    ∀ n, KeepsAt s Q m m (times n x)
  | 0 => keeps_pure trivial
  | n + 1 => keeps_bind h fun _ _ => keeps_times h n

theorem keeps_forEach {α : Type} {f : α → Planning Unit} :
    ∀ l : List α, (∀ a ∈ l, KeepsAt s Q m m (f a)) → KeepsAt s Q m m (forEach l f)
  | [], _ => keeps_pure trivial
  | a :: t, h => keeps_bind (h a List.mem_cons_self) fun _ _ =>
      keeps_forEach t fun b hb => h b (List.mem_cons_of_mem _ hb)

/-- Every entry of a finished plan has Q. -/
theorem finish_all {c : Scope} {x : Planning Unit} {P : Planned} (h : Keeps s Q x)
    (e : finish s c x = .ok P) : ∀ r ∈ P.rounds, Q r.entry := by
  unfold finish at e
  split at e
  · cases e
  · rename_i u p hx
    split at e
    · cases e
    · cases e
      exact (h { set := s, scope := c } p u rfl rfl (fun r hr => by simp at hr) hx).2.2.1

theorem finishHeld_all {c : Scope} {x : Planning Unit} {P : Planned} (h : Keeps s Q x)
    (e : finishHeld s c x = .ok P) : ∀ r ∈ P.rounds, Q r.entry := by
  unfold finishHeld at e
  cases hf : finish s c x with
  | error w =>
    rw [hf] at e
    cases e
  | ok P' =>
    rw [hf] at e
    have e' : (if P'.holds = true then (pure P' : Except String Planned) else throw notAdmitted) =
        .ok P := e
    split at e'
    · cases e'
      exact finish_all h hf
    · cases e'

end

/-- The name is within the format's rule, and is not the name of the item that follows a plan in a
chain's parameter bytes. -/
def NameOk (n : String) : Prop := Fmt.nameFit n = true ∧ n ≠ Fmt.configName

/-- The name is in order; at most two roots; logN ≤ 64; few draws. -/
def Small (e : Fmt.Entry) : Prop :=
  NameOk e.name ∧ e.roots ≤ 2 ∧ e.logN ≤ 64 ∧ e.poss ≤ 2 ^ 40 ∧ e.drawE ≤ 2 ^ 40 ∧
    e.drawNZ ≤ 2 ^ 40 ∧ e.trits ≤ 2 ^ 45

/-- What is asked of the setting. The last field holds at every setting (PositionsCap.lean in this
folder): it is no condition on s, and stands here so that this file imports no law on the search for
a number of positions. -/
structure SetCap (s : Setting) : Prop where
  samples : s.samples ≤ 4
  p : s.p < 2 ^ 64
  target : s.target ≤ 256
  inst : clog2 s.instances ≤ 20
  pos : ∀ c agree extra, scopePositions s c agree extra ≤ 2 ^ 32

end OnBytes.Params

#print axioms OnBytes.Params.keeps_bind
#print axioms OnBytes.Params.keeps_close
#print axioms OnBytes.Params.finishHeld_all
