-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SecondOpensTaken.lean: WHAT THE FIRST ROUND OF POSITIONS OF A SECOND CHAIN OPENS IS TAKEN
  OVER,
EVERY TREE OF IT, BY THE MAKE OF `secondOpens` (Johnson/G/RoundsOfPlan.lean).

Why. The law of the request's own proximity test promises of its first switch that every tree which
  it
opens was sent in front of the test's stretch. The list of these trees is a letter of the test's
  place;
at the last chain the planner's road fills it with the head of `secondOpens`: the first chain's
  trees
that hold the input, then those of W, then the shared chain's tree of Omega: each by `takenAt`.
  `secondOpens_head`        the head, written out
  `secondOpens_head_taken`  **every member of the head has a source "taken c n", c = 0 or 1**
Limits. A fact of make on one function. That a place's list is this head is the caller's.
Nothing on soundness.

-/
import Johnson.G.RoundsOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G.OfPlan
open OnBytes OnBytes.Params

theorem secondOpens_head (S : LinShape) (input : Sent → Bool) (t0 t1 ts : List (Sent × Nat)) :
    (secondOpens S input t0 t1 ts).head? =
      some ((t0.filter fun t => input t.1).map (takenAt 0) ++
        (t0.filter fun t => t.1.tag == .w).map (takenAt 0) ++
        (t1.filter fun t => t.1.tag == .omega && t.1.cls == S.omegaLeafClass).map (takenAt 1)) :=
  rfl

/-- **Every tree that the first round of positions of a second chain opens is taken over.** -/
theorem secondOpens_head_taken (S : LinShape) (input : Sent → Bool) (t0 t1 ts : List (Sent × Nat))
    (l : List Told) (h : (secondOpens S input t0 t1 ts).head? = some l) :
    ∀ o ∈ l, ∃ c n, o.2 = .taken c n ∧ c ≤ 1 := by
  rw [secondOpens_head] at h
  have e := Option.some.inj h
  subst e
  intro o ho
  rcases List.mem_append.1 ho with ho | ho
  · rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨t, _, rfl⟩ := List.mem_map.1 ho
      exact ⟨0, t.2, rfl, by decide⟩
    · obtain ⟨t, _, rfl⟩ := List.mem_map.1 ho
      exact ⟨0, t.2, rfl, by decide⟩
  · obtain ⟨t, _, rfl⟩ := List.mem_map.1 ho
    exact ⟨1, t.2, rfl, by decide⟩

end Johnson.G.OfPlan

#print axioms Johnson.G.OfPlan.secondOpens_head_taken
