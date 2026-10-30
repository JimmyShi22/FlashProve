-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5WrittenTrue.lean: kind K5 (an attention segment's own rounds): THE KIND's CLOSED TESTS AT THE WRITTEN VALUES (K5WrittenPlans.lean: seatsAllW g · shapesAllW g; K5TieWitness.lean: tieWW g) SAY YES AT ALL TWELVE GROUPS.

Compiled with the whole library.

(Where this and lean/THEOREM.md differ, the page holds.)

Why. The three are what other theorems spend to pay the kind's named conditions seatsPlan · shapesPlan · sent · tie wherever the two comparisons with the written values accept. Lean's kernel decides them in the forms made for it (K5PlansFTrue.lean · K5TieFTrue.lean); the forms are one with these under two equations without a letter (K5WrittenIsFull.lean: pseatsW_is · pseatsAllW_is). A joining: nothing is evaluated here.

Main names:
  **`seatsAllW_true`**, **`shapesAllW_true`**, **`tieWW_true`**: at every g below 12.
Is it empty here? Sentences without a premise, and equations.
Limits. They speak of the written values.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5PlansFTrue
import Johnson.Desc.First.Att.Door.Law.K5TieFTrue
import Johnson.Desc.First.Att.Door.Law.K5WrittenIsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door

theorem seatsAllW_true {g : ℕ} (hg : g < 12) : seatsAllW g = true := (seatsAllW_eq pseatsW_is g).trans (seatsAllF_true hg)

theorem shapesAllW_true {g : ℕ} (hg : g < 12) : shapesAllW g = true := (shapesAllW_eq pseatsW_is g).trans (shapesAllF_true hg)

theorem tieWW_true {g : ℕ} (hg : g < 12) : tieWW g = true := (tieWW_eq pseatsAllW_is g).trans (tieF_true hg)

end H2K5.Door

#print axioms H2K5.Door.seatsAllW_true
#print axioms H2K5.Door.shapesAllW_true
#print axioms H2K5.Door.tieWW_true
