-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ScalarsLaw.lean: the planner's count of scalars, off a routine's plain list of
rounds. Two definitions, two theorems.

Why. `scalarsOf s x` (OnBytes/Params/Gate.lean) runs the routine x on an empty plan and adds up,
over the rounds that the run leaves, what the prover sends beside roots and answers. Lean's kernel
does not get through that at the key file's lookups ("deep recursion detected", 632 s). By the
laws on `Runs` (OnBytes/Params/PlanningLaws.lean) the rounds that a run leaves are those of a
plain list.

What is said. `scalarsOn s l`: the count's text over the plain list l. `scalarsOf_of_runs`: where x
runs as l from nothing open to nothing open, in a request's scope, AND ITS RUN ON THE EMPTY PLAN
RETURNS, `scalarsOf s x = .ok (scalarsOn s l)`. `lookupScalars_of_returns`: so for the key file's
lookups: the list is `lookupList`'s (OnBytes/Params/PlanListsSum.lean), by `runs_lookup` and
`runs_forEach`.

Limits. That the run returns is a premise. General in the sizes. Nothing on soundness.
-/
import OnBytes.Params.PlanListsSum
import OnBytes.Plan.RangesGate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params

/-- The count's text over a plain list of rounds, with nothing left open. -/
def scalarsOn (s : Setting) (l : List RoundSpec) : Nat :=
  ((l.map (·.round s .request)).foldl
    (fun n r => n + (r.entry.msg - 32 * r.entry.roots - 24 * r.entry.answers)) 0 +
    (0 - 32 * 0 - 24 * 0)) / 24

/-- **Where the run returns, the count is the plain list's.** -/
theorem scalarsOf_of_runs {s : Setting} {x : Planning Unit} {l : List RoundSpec}
    (hx : Runs s .request 0 0 0 x () l 0 0 0)
    (h : (x { set := s }).toOption.isSome = true) : scalarsOf s x = .ok (scalarsOn s l) := by
  unfold scalarsOf scalarsOn
  cases hr : x { set := s } with
  | error e =>
    rw [hr] at h
    cases h
  | ok up =>
    obtain ⟨u, p⟩ := up
    obtain ⟨_, _, _, q, b, r, a, _⟩ := hx _ p u rfl rfl rfl rfl rfl hr
    have q' : p.rounds.toList = l.map (·.round s .request) := by simpa using q
    simp only [b, r, a, ← Array.foldl_toList, q']

/-- The plain list of the key file's lookups. -/
def lookupsList (z : Plan.KeySized) : List RoundSpec :=
  ((Plan.lookupSizes z.ranges.x z.ranges.matrix).map (lookupList z.set)).flatten

theorem lookupScalars_of_returns (z : Plan.KeySized)
    (h : ((forEach (Plan.lookupSizes z.ranges.x z.ranges.matrix) planLookup)
      { set := z.set }).toOption.isSome = true) :
    Plan.lookupScalars z = .ok (scalarsOn z.set (lookupsList z)) :=
  scalarsOf_of_runs (runs_forEach (fun x => runs_lookup x) _) h

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.scalarsOf_of_runs
#print axioms Johnson.AtFull.Made.lookupScalars_of_returns
