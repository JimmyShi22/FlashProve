-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Plans/PlansLaw.lean: WHAT ONE Bool ON A PLAN's ENTRIES AND A WRITTEN LIST GIVES. A
definition
and a law; nothing is evaluated.
  `sameB P es`: the plan's entries are es, and no member of es bears the name `Fmt.recordName`.
  **`of_sameB`**: `sameB P es = true → P.rounds = es ∧ P.entries.length - P.rounds.length = 0`
    (`Fmt.Plan.rounds`, Fmt/Rules4.lean, leaves the entries of that name out of a plan's entries).
Limits. General: no value is treated. One direction. Nothing on soundness. On hiding nothing.

-/
import Fmt.Rules4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Plans

/-- The plan's entries are es, and none of them bears the name that a plan's rounds leave out. -/
def sameB (P : Fmt.Plan) (es : List Fmt.Entry) : Bool :=
  decide (P.entries = es) && es.all fun e => e.name != Fmt.recordName

/-- **A yes: the plan's rounds are es, and its entries are no more than its rounds.** -/
theorem of_sameB {P : Fmt.Plan} {es : List Fmt.Entry} (h : sameB P es = true) :
    P.rounds = es ∧ P.entries.length - P.rounds.length = 0 := by
  unfold sameB at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  have hr : P.rounds = es := by
    unfold Fmt.Plan.rounds
    rw [h.1]
    exact List.filter_eq_self.2 fun a ha => List.all_eq_true.1 h.2 a ha
  exact ⟨hr, by rw [hr, h.1, Nat.sub_self]⟩

end Johnson.AtFull.Plans

#print axioms Johnson.AtFull.Plans.of_sameB
