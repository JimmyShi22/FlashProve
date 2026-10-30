-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ground/Mid.lean: a chain's state together with what is still to come, and one step on
the next rounds.

This file holds definitions only; no theorem is stated. They are general in a chain's own named
values L, and stand on Johnson/Desc/Ground/Calls.lean alone.

Main names:
  Mid L: the state (DState L) with the plan's entries and the view's rounds that are still to come.
  fits e r: the round r draws as many elements, positions and matrix entries as the entry e says.
    It compares three counts. It does not look at what the round's message holds, at the values
    drawn, or at the entry's other numbers.
  Mid.step m k f: the step f on the next k rounds. It refuses unless k rounds and k entries are
    left and each of these rounds fits its entry; else it hands f the state and these k rounds, and
    drops k rounds and k entries. So steps that follow each other take the rounds and the entries
    in order, without a gap and without an overlap.
  answersMax sent: the largest number of answers that a shape among the messages of a sending
    states; 0 for no message.

What is assumed. Nothing is assumed of the entries and the rounds: that the entries are a plan's,
and the rounds a view's, is the caller's matter.

What is not claimed. That a fold of such steps uses up all rounds or all entries: nothing here asks
what is left at the end. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.Ground.Calls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.Plain
open OnBytes OnBytes.Params

variable {L : Type}

/-- The state with what is still to come. -/
structure Mid (L : Type) where
  d : DState L
  entries : List Fmt.Entry
  rounds : List Fmt.RoundView

/-- The round draws as many elements, positions and matrix entries as the plan's entry says. -/
def fits (e : Fmt.Entry) (r : Fmt.RoundView) : Bool :=
  r.drawn.elems.length == e.drawE && r.drawn.poss.length == e.poss &&
    r.drawn.trits.length == e.trits

/-- One step on the next k rounds, each of which fits its entry of the plan; as many entries go with
them. -/
def Mid.step (m : Mid L) (k : Nat) (f : DState L → List Fmt.RoundView → Option (DState L)) :
    Option (Mid L) :=
  if decide (k ≤ m.rounds.length) && decide (k ≤ m.entries.length) &&
      ((m.entries.take k).zip (m.rounds.take k)).all (fun x => fits x.1 x.2) then
    (f m.d (m.rounds.take k)).map fun d' =>
      { d := d', entries := m.entries.drop k, rounds := m.rounds.drop k }
  else none

/-- The largest number of answers among the messages of a sending. -/
def answersMax (sent : Array OracleNotice) : Nat := sent.foldl (fun a n => max a n.shape.answers) 0

end Desc.Plain
