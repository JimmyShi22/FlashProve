-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/CallFrame.lean: two steps of the planner that stand round the draw of the matrix
of a smallness test leave a plan in writing in an idle state.

A schedule of a chain can be written as a list of calls of the planner's named routines. The
theorems on single calls (OnBytes/Tie/Pv/Tail/CallRng.lean) start from an idle state: the setting, a
request's scope, no open message (Idle, OnBytes/Tie/Pv/Tail/Plan.lean). To use them along a list,
each call must be known to hand such a state on. This file says it of the sending of oracle messages
with a round of its own for the answers (planSend o roots true), and of the step that sets the
scope. Definitions, statements and proofs.

Main names:
  `Reads x`: the routine x only reads: where it ends well the state is as it was.
  `reads_errors`: the routine that adds up the sample errors only reads.
  `close_shuts`, `none_shuts`: a round that is closed leaves no open message, keeps setting and
    scope, and adds one round of the given name.
  `send_idle`: from an idle state planSend o roots true ends well only in an idle state, and adds
    two rounds, named SEND seed and SEND answer.
  `Shut st p`: as Idle, in whatever scope. `scope_idle`: from such a state the step that sets the
    scope to a request's gives an idle state and adds no round.

Limits: of the two rounds of a sending only the names are said: not their entries' numbers, not
their bounds. With the last argument false planSend leaves the answers' bytes open, and the state
is not idle.
-/
import OnBytes.Tie.Pv.Tail.Plan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open OnBytes OnBytes.Params

/-- The routine only reads: where it ends well the state is as it was. -/
def Reads {α : Type} (x : Planning α) : Prop := ∀ p a m, x p = .ok (a, m) → m = p

theorem Reads.pure {α : Type} (a : α) : Reads (pure a : Planning α) := fun _ _ _ h =>
  ((Prod.mk.inj (Except.ok.inj h)).2).symm

theorem Reads.bind {α β : Type} {x : Planning α} {f : α → Planning β} (hx : Reads x)
    (hf : ∀ a, Reads (f a)) : Reads (x >>= f) := fun p b q h => by
  obtain ⟨a, m, h1, h2⟩ := plan_bind h
  rw [hf a m b q h2, hx p a m h1]

theorem reads_setting : Reads theSetting := fun _ _ _ h =>
  ((Prod.mk.inj (Except.ok.inj h)).2).symm

theorem reads_needs (c : Bool) (why : String) : Reads (needs c why) := fun _ _ _ h =>
  (needs_ok h).2.symm

theorem reads_analysis (g : GroupSize) : Reads (planAnalysis g) :=
  Reads.bind reads_setting fun _ => Reads.bind (reads_needs _ _) fun _ => Reads.pure _

theorem reads_list : ∀ gs : List GroupSize, Reads (listOfGroups gs)
  | [] => Reads.pure 1
  | g :: gs => Reads.bind (reads_analysis g) fun _ => Reads.bind (reads_list gs) fun _ =>
      Reads.pure _

/-- The routine that adds up the sample errors only reads. -/
theorem reads_errors (s : Setting) : ∀ (o : List SampleSize) (e : Bound), Reads (sampleErrors s o e)
  | [], e => Reads.pure e
  | x :: xs, _ => Reads.bind (reads_list x.groups) fun _ => reads_errors s xs _

/-- A round with a verifier's message leaves no open message, keeps setting and scope, and adds one
round of the given name. -/
theorem close_shuts {name : String} {why : ErrorKind} {e : Bound} {d : Draws} {p q : PlanState}
    (h : close name why e d p = .ok ((), q)) :
    q.set = p.set ∧ q.scope = p.scope ∧ q.openBytes = 0 ∧ q.openRoots = 0 ∧ q.openAnswers = 0 ∧
      ∃ R : PlanRound, q.rounds = p.rounds.push R ∧ R.entry.name = name := by
  unfold close at h
  simp only at h
  split at h
  · split at h
    · cases h
    · obtain rfl := (Prod.mk.inj (Except.ok.inj h)).2
      exact ⟨rfl, rfl, rfl, rfl, rfl, _, rfl, rfl⟩
  · split at h
    · cases h
    · obtain rfl := (Prod.mk.inj (Except.ok.inj h)).2
      exact ⟨rfl, rfl, rfl, rfl, rfl, _, rfl, rfl⟩

/-- A round in which the verifier says nothing: the same. -/
theorem none_shuts {name : String} {p q : PlanState} (h : closeNone name p = .ok ((), q)) :
    q.set = p.set ∧ q.scope = p.scope ∧ q.openBytes = 0 ∧ q.openRoots = 0 ∧ q.openAnswers = 0 ∧
      ∃ R : PlanRound, q.rounds = p.rounds.push R ∧ R.entry.name = name := by
  unfold closeNone at h
  split at h
  · cases h
  · rename_i hr
    obtain rfl := (Prod.mk.inj (Except.ok.inj h)).2
    refine ⟨rfl, rfl, rfl, ?_, rfl, _, rfl, rfl⟩
    simpa using hr

/-- The sending of oracle messages, with a round of its own for the answers. -/
theorem send_idle (st : Setting) (o : List SampleSize) (roots : Nat) (p q : PlanState)
    (hp : Idle st p) (h : planSend o roots true p = .ok ((), q)) :
    Idle st q ∧ ∃ R1 R2 : PlanRound, q.rounds = (p.rounds.push R1).push R2 ∧
      R1.entry.name = "SEND seed" ∧ R2.entry.name = "SEND answer" := by
  have h' : (theSetting >>= fun s => planRoots roots >>= fun _ =>
      sampleErrors s o (Bound.ofWord 0) >>= fun e =>
      close "SEND seed" .sample e
        { drawE := s.samples * (o.foldl (fun c x => max c x.cubeBits) 0 + 1),
          drawNZ := s.samples, priced := .callersWord } >>= fun _ =>
      planAnswers (s.samples * o.length) >>= fun _ =>
      (if (true : Bool) = true then closeNone "SEND answer" else pure ())) p = .ok ((), q) := h
  obtain ⟨s, m1, g1, k1⟩ := plan_bind h'
  obtain ⟨rfl, rfl⟩ : p.set = s ∧ p = m1 := Prod.mk.inj (Except.ok.inj g1)
  obtain ⟨_, m2, g2, k2⟩ := plan_bind k1
  obtain rfl : { p with openBytes := p.openBytes + 32 * roots,
                        openRoots := p.openRoots + roots } = m2 :=
    (Prod.mk.inj (Except.ok.inj g2)).2
  obtain ⟨e, m3, g3, k3⟩ := plan_bind k2
  obtain rfl := reads_errors _ _ _ _ _ _ g3
  obtain ⟨_, m4, g4, k4⟩ := plan_bind k3
  obtain ⟨a1, a2, a3, a4, a5, R1, r1, n1⟩ := close_shuts g4
  obtain ⟨_, m5, g5, k5⟩ := plan_bind k4
  obtain rfl : { m4 with openBytes := m4.openBytes + 24 * (p.set.samples * o.length),
                         openAnswers := m4.openAnswers + p.set.samples * o.length } = m5 :=
    (Prod.mk.inj (Except.ok.inj g5)).2
  rw [if_pos rfl] at k5
  obtain ⟨b1, b2, b3, b4, b5, R2, r2, n2⟩ := none_shuts k5
  refine ⟨⟨?_, ?_, b3, b4, b5⟩, R1, R2, ?_, n1, n2⟩
  · rw [b1]
    show m4.set = st
    rw [a1]
    exact hp.set
  · rw [b2]
    show m4.scope = .request
    rw [a2]
    exact hp.scope
  · rw [r2]
    show m4.rounds.push R2 = _
    rw [r1]

/-- The setting st and no open message, in whatever scope. -/
structure Shut (st : Setting) (p : PlanState) : Prop where
  set : p.set = st
  bytes : p.openBytes = 0
  roots : p.openRoots = 0
  answers : p.openAnswers = 0

theorem Idle.shut {st : Setting} {p : PlanState} (h : Idle st p) : Shut st p :=
  ⟨h.set, h.bytes, h.roots, h.answers⟩

/-- The step that sets the scope to a request's. -/
theorem scope_idle (st : Setting) (p q : PlanState) (hp : Shut st p)
    (h : (modify fun p => { p with scope := .request } : Planning Unit) p = .ok ((), q)) :
    Idle st q ∧ q.rounds = p.rounds := by
  obtain rfl : { p with scope := .request } = q := (Prod.mk.inj (Except.ok.inj h)).2
  exact ⟨⟨hp.set, rfl, hp.bytes, hp.roots, hp.answers⟩, rfl⟩

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.reads_errors
#print axioms OnBytes.Tie.Pv.Tail.send_idle
#print axioms OnBytes.Tie.Pv.Tail.scope_idle
