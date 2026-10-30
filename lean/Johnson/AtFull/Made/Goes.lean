-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/Goes.lean: a routine of the planner that returns from nothing open to nothing
open, whatever rounds the plan already holds; how such routines compose; and a test with code that
shows it of a routine that reads no round. General laws: no written value, no evaluation. A law
file; no running text imports it.

Definitions.
  `idle s R`: the plan with the setting s, a request's own scope, the rounds R and nothing open.
  `Goes s y a`: from `idle s R`, at every R, the routine y returns a and leaves `idle s R'` for some
    R'.
  `goesB s y a`: the test: from `idle s #[]` y returns a, under a request's own scope, nothing open.
    It looks at no round.
Statements.
  `Goes.pure`, `Goes.bind`: composition. `Goes.isOk`: so y ends well from the empty plan.
  `goes_of`: FrP y (Johnson/AtFull/Rows/FrameP.lean) and a yes of the test give `Goes s y a`.

Limits. Nothing says which rounds are added. Nothing on soundness.
-/
import Johnson.AtFull.Rows.FrameP
import OnBytes.Params.PlanningLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.Desc.LinkJoin (FrP under)

/-- The plan with the rounds R and nothing open, under a request's own scope. -/
def idle (s : Setting) (R : Array PlanRound) : PlanState :=
  { set := s, scope := .request, rounds := R }

/-- From nothing open to nothing open, whatever rounds the plan holds. -/
def Goes (s : Setting) {α : Type} (y : Planning α) (a : α) : Prop :=
  ∀ R, ∃ R', y (idle s R) = .ok (a, idle s R')

theorem Goes.pure (s : Setting) {α : Type} (a : α) : Goes s (Pure.pure a : Planning α) a :=
  fun R => ⟨R, rfl⟩

theorem Goes.bind {s : Setting} {α β : Type} {y : Planning α} {f : α → Planning β} {a : α}
    {b : β} (h1 : Goes s y a) (h2 : Goes s (f a) b) : Goes s (y >>= f) b := by
  intro R
  obtain ⟨R1, e1⟩ := h1 R
  obtain ⟨R2, e2⟩ := h2 R1
  exact ⟨R2, by rw [bind_run, e1]; exact e2⟩

theorem Goes.isOk {s : Setting} {α : Type} {y : Planning α} {a : α} (h : Goes s y a) :
    (y { set := s, scope := .request }).isOk = true := by
  obtain ⟨R', e⟩ := h #[]
  have e' : y { set := s, scope := .request } = .ok (a, idle s R') := e
  rw [e']
  rfl

/-- The test. -/
def goesB (s : Setting) {α : Type} [DecidableEq α] (y : Planning α) (a : α) : Bool :=
  match y (idle s #[]) with
  | .ok (a', q) => decide (a' = a) && decide (q.scope = .request) && q.openBytes == 0 &&
      q.openRoots == 0 && q.openAnswers == 0
  | .error _ => false

/-- **A yes of the test, at a routine that reads no round.** -/
theorem goes_of {s : Setting} {α : Type} [DecidableEq α] {y : Planning α} {a : α} (hy : FrP y)
    (h : goesB s y a = true) : Goes s y a := by
  intro R
  unfold goesB at h
  cases e : y (idle s #[]) with
  | error w =>
    rw [e] at h
    cases h
  | ok v =>
    obtain ⟨a', q⟩ := v
    rw [e] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨rfl, hc⟩, hb⟩, hr⟩, ha⟩ := h
    obtain ⟨hs, hR⟩ := hy (idle s #[]) a' q e
    refine ⟨R ++ q.rounds, ?_⟩
    have e1 : under R (idle s #[]) = idle s R := by
      simp only [under, idle, Array.append_empty]
    have e2 : under R q = idle s (R ++ q.rounds) := by
      obtain ⟨q1, q2, q3, q4, q5, q6⟩ := q
      have hs' : q1 = s := hs
      have hc' : q2 = .request := hc
      have hb' : q4 = 0 := hb
      have hr' : q5 = 0 := hr
      have ha' : q6 = 0 := ha
      subst hs' hc' hb' hr' ha'
      rfl
    have g := hR R
    rw [e1, e2] at g
    exact g

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.Goes.pure
#print axioms Johnson.AtFull.Made.Goes.bind
#print axioms Johnson.AtFull.Made.Goes.isOk
#print axioms Johnson.AtFull.Made.goes_of
