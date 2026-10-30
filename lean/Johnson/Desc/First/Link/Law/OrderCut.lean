-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/OrderCut.lean: THE ORDER OF A SEGMENT'S RUNS, IN THE DRIVER'S FILES'
OWN TERMS: `stated` (Johnson/Desc/First/Driver/Chain.lean): the entries of an order that some block
states; `cutAway` (Johnson/Desc/First/Driver/OrderTally.lean): the others. Theorems, at any list of
blocks and any order: nothing here speaks of what the driver lays. It imports OrderTally.lean and
Johnson/Desc/First/Link/Law/Order.lean.

What is said.
  `cutAway_nil_iff`: nothing is cut away just if every run that the order names is stated by the
    block that it names. `stated_eq_iff`: and just then the stated part of the order is the order
    itself.
  `orderOk_nothing_cut`, `orderAfterOk_nothing_cut`: **where Block's own test says yes to an order,
    nothing of THAT order is cut away.**

Limits. On names and numbers of runs alone. At no real seat is anything evaluated here. Nothing on
soundness.

-/
import Johnson.Desc.First.Driver.OrderTally
import Johnson.Desc.First.Link.Law.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Shape
open First (stated cutAway)

variable {S Cl : Type}

theorem cutAway_nil_iff {B : Type} (names : B → List String) (bs : List B)
    (order : List (Nat × String)) :
    cutAway names bs order = [] ↔ ∀ o ∈ order, ∃ b, bs[o.1]? = some b ∧ o.2 ∈ names b := by
  unfold cutAway
  rw [List.filter_eq_nil_iff]
  refine forall_congr' fun o => imp_congr_right fun _ => ?_
  simp only [Bool.not_eq_true', Bool.not_eq_false, Option.any_eq_true, List.contains_iff_mem]

theorem stated_eq_iff {B : Type} (names : B → List String) (bs : List B)
    (order : List (Nat × String)) :
    stated names bs order = order ↔ cutAway names bs order = [] := by
  rw [cutAway_nil_iff]
  unfold stated
  rw [List.filter_eq_self]
  refine forall_congr' fun o => imp_congr_right fun _ => ?_
  rw [Option.any_eq_true]
  simp only [List.contains_iff_mem]

/-- **WHERE BLOCK'S TEST SAYS YES TO AN ORDER, NOTHING OF THAT ORDER IS CUT AWAY.** -/
theorem orderOk_nothing_cut {bs : List (Block S Cl)} {order : List (Nat × String)}
    (h : orderOk bs order = true) : cutAway (·.claims.map (·.1)) bs order = [] :=
  (cutAway_nil_iff _ bs order).2 (orderOk_covers h)

theorem orderAfterOk_nothing_cut {bs : List (Block S Cl)} {order : List (Nat × String)}
    (h : orderAfterOk bs order = true) : cutAway (·.after.map (·.1)) bs order = [] :=
  (cutAway_nil_iff _ bs order).2 (orderAfterOk_covers h)

end VerifiableInference.Desc.Shape

#print axioms VerifiableInference.Desc.Shape.cutAway_nil_iff
#print axioms VerifiableInference.Desc.Shape.stated_eq_iff
#print axioms VerifiableInference.Desc.Shape.orderOk_nothing_cut
#print axioms VerifiableInference.Desc.Shape.orderAfterOk_nothing_cut
