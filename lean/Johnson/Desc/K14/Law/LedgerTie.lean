-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerTie.lean: K1's TIE AT THE PLAN's THREE SHAPES (G_u's, Omega's, the
split's), FROM K1's CONDITION AT THE SHARED CHAIN's TWO SENDINGS: the statement that
Johnson/Desc/K14/Law/LedgerTieOwed.lean names as owed (TiesOfCondOwed), proved.
HOW. Three calls of cond_tie (Johnson/Desc/K1/Law/Port6.lean), at place 0 of "send o_u" and at the
places 0 and 1 of "send o_omega". That the places are there, that the messages there are sampled
and which shapes they bear: places, sampled, u0, o0, o1, shapeAt_of
(Johnson/Desc/K14/Law/PlanShapes.lean). A sending's codes are the plan's by rfl.
What is not claimed. That the condition holds at a plan. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerTieOwed
import Johnson.Desc.K14.Law.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K1 (condPort Tie cond_tie shapesOf shapeAt sampledAt)

/-- **The three ties.** -/
theorem tiesOfCond : TiesOfCondOwed := by
  intro Q sentU rad2 rad5 hU hok h2 h5
  obtain ⟨pU, pO, pS⟩ := places Q sentU
  obtain ⟨sU, sO, sS⟩ := sampled Q sentU hok
  refine ⟨?_, ?_, fun hs => ?_⟩
  · have t := cond_tie _ rad2 h2 ⟨0, pU hU⟩ (sU hU (pU hU))
    rw [shapeAt_of (k := ⟨0, pU hU⟩) (u0 Q "o_u and the first mask" hU)] at t
    exact t
  · have t := cond_tie _ rad5 h5 ⟨0, pO⟩ (sO pO)
    rw [shapeAt_of (k := ⟨0, pO⟩) (o0 Q "o_omega and o_sp")] at t
    exact t
  · have t := cond_tie _ rad5 h5 ⟨1, pS hs⟩ (sS (pS hs))
    rw [shapeAt_of (k := ⟨1, pS hs⟩) (o1 Q "o_omega and o_sp" (pS hs))] at t
    exact t

end Desc.K14.Law
