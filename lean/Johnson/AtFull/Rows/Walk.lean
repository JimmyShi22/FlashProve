-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/Walk.lean: THE LAW OF COMPOSITION FOR THE NOTING ROUTINES: a run
of x >>= f from no call and no round is a run of x, and then a run of f a FROM NO CALL AND NO ROUND
at the small state at which x ended; the calls and the rounds are laid one behind the other.
Definitions and theorems. A law file; no running text imports it.
  `SmallSt`        the plan's state but for the setting and the rounds: the scope and three
                   counters.
  `RunsN s σ x a cs rs σ'`   x, from no call and no round at σ, returns a, has noted cs, has written
                             rs, ends at σ'.
  `RunsN.bind`    the law. Only the continuation is asked to read no round (`Fr`, FrameN.lean).
  `noted_of_runs`   from a run that begins and ends at counters 0 to `Johnson.G.noted`'s value.
  `endOf`, `callsAt`, `roundsAt` with code: where a closed piece ends, what it has noted and
  written.
  `runs_of_end`  a closed fact «endOf s σ x = some σ'» gives a run.
Limits. No closed fact is here. Nothing on (k1) | (k2) of callsFrom, nothing on packFrom. Nothing on
soundness or on hiding.
-/
import Johnson.AtFull.Rows.FrameN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

/-- The plan's state but for the setting and the rounds. -/
structure SmallSt where
  scope : Scope
  bytes : Nat
  roots : Nat
  answers : Nat
  deriving DecidableEq, Repr

/-- The plan at a setting, a small state and rounds. -/
def SmallSt.plan (s : Setting) (σ : SmallSt) (rs : Array PlanRound := #[]) : PlanState :=
  { set := s, scope := σ.scope, rounds := rs, openBytes := σ.bytes, openRoots := σ.roots,
    openAnswers := σ.answers }

/-- The small state of a plan. -/
def smallOf (q : PlanState) : SmallSt := ⟨q.scope, q.openBytes, q.openRoots, q.openAnswers⟩

/-- x, from no call and no round at σ, returns a, has noted cs, has written rs, and ends at σ'. -/
def RunsN {α : Type} (s : Setting) (σ : SmallSt) (x : N α) (a : α) (cs : Array Call)
    (rs : Array PlanRound) (σ' : SmallSt) : Prop :=
  (x.run #[]).run (σ.plan s) = .ok ((a, cs), σ'.plan s rs)

theorem under_plan (s : Setting) (σ : SmallSt) (R rs : Array PlanRound) :
    under R (σ.plan s rs) = σ.plan s (R ++ rs) := rfl

/-- **The law of composition.** -/
theorem RunsN.bind {α β : Type} {s : Setting} {σ σ₁ σ₂ : SmallSt} {x : N α} {f : α → N β} {a : α}
    {b : β}
    {cs cs' : Array Call} {rs rs' : Array PlanRound}
    (h1 : RunsN s σ x a cs rs σ₁) (hf : Fr (f a)) (h2 : RunsN s σ₁ (f a) b cs' rs' σ₂) :
    RunsN s σ (x >>= f) b (cs ++ cs') (rs ++ rs') σ₂ := by
  unfold RunsN at *
  have g := (hf #[] (σ₁.plan s) b cs' (σ₂.plan s rs') h2).2 cs rs
  rw [under_plan, under_plan, Array.append_empty, Array.append_empty] at g
  rw [StateT.run_bind, StateT.run_bind, h1]
  exact g

/-- From a run that begins and ends at counters 0 to `noted`'s value. -/
theorem noted_of_runs {s : Setting} {scope sc' : Scope} {x : N Unit} {cs : Array Call}
    {rs : Array PlanRound} (h : RunsN s ⟨scope, 0, 0, 0⟩ x () cs rs ⟨sc', 0, 0, 0⟩) :
    noted s scope x = .ok (cs.toList, ⟨s, rs.toList⟩) := by
  have h0 : (x.run #[]).run { set := s, scope := scope } =
      .ok (((), cs), (⟨sc', 0, 0, 0⟩ : SmallSt).plan s rs) := h
  have e : ((do let _ ← x.run #[]) : Planning Unit).run { set := s, scope := scope } =
      .ok ((), (⟨sc', 0, 0, 0⟩ : SmallSt).plan s rs) := by
    show ((x.run #[] >>= fun _ => pure ()) : Planning Unit).run _ = _
    rw [StateT.run_bind, h0]
    rfl
  have hfin : finish s scope (do let _ ← x.run #[]) = .ok ⟨s, rs.toList⟩ := by
    unfold finish
    have e' : ((do let _ ← x.run #[]) : Planning Unit) { set := s, scope := scope } =
      .ok ((), (⟨sc', 0, 0, 0⟩ : SmallSt).plan s rs) := e
    rw [e']
    rfl
  unfold noted
  rw [hfin]
  have h0' : (x.run #[]) { set := s, scope := scope } =
      .ok (((), cs), (⟨sc', 0, 0, 0⟩ : SmallSt).plan s rs) := h0
  show ((x.run #[]) { set := s, scope := scope } >>= fun r =>
    (pure (r.1.2.toList, (⟨s, rs.toList⟩ : Planned)) : Except String _)) = _
  rw [h0']
  rfl

/-- What a piece returns from no call and no round at σ: its calls and its plan. -/
def outAt (s : Setting) (σ : SmallSt) (x : N Unit) : Option (Array Call × PlanState) :=
  match (x.run #[]).run (σ.plan s) with
  | .ok ((_, cs), q) => some (cs, q)
  | .error _ => none

/-- Where a piece ends. -/
def endOf (s : Setting) (σ : SmallSt) (x : N Unit) : Option SmallSt :=
  (outAt s σ x).map fun r => smallOf r.2
/-- What it has noted; nothing where it refuses. -/
def callsAt (s : Setting) (σ : SmallSt) (x : N Unit) : Array Call :=
  ((outAt s σ x).map (·.1)).getD #[]
/-- What it has written; nothing where it refuses. -/
def roundsAt (s : Setting) (σ : SmallSt) (x : N Unit) : Array PlanRound :=
  ((outAt s σ x).map (·.2.rounds)).getD #[]

/-- A closed fact on where a piece ends gives a run. -/
theorem runs_of_end {s : Setting} {σ σ' : SmallSt} {x : N Unit} (hx : Fr x)
    (h : endOf s σ x = some σ') : RunsN s σ x () (callsAt s σ x) (roundsAt s σ x) σ' := by
  unfold endOf at h
  unfold RunsN callsAt roundsAt
  unfold outAt at *
  cases e : (x.run #[]).run (σ.plan s) with
  | error m =>
    rw [e] at h
    cases h
  | ok r =>
    obtain ⟨⟨u, cs⟩, q⟩ := r
    rw [e] at h
    have hs : q.set = s := (hx _ _ _ _ _ e).1
    have hq : smallOf q = σ' := Option.some.inj h
    subst hq
    subst hs
    rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.RunsN.bind
#print axioms VerifiableInference.Desc.LinkJoin.noted_of_runs
#print axioms VerifiableInference.Desc.LinkJoin.runs_of_end
