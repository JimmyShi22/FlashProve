-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Plans/PlansSix.lean: THE CLOSED FACTS ON THE PLANNER's THREE WRITTEN PLANS FOR THE
PROOF FILE
THAT THE DECLARED ROUNDS' AND THE TOLD TREES' VALUES AT THE WRITTEN PARTS ASK: each plan's rounds
are
the dry runs' written list's entries, and its entries are no more than its rounds. Joins; nothing is
evaluated here.
  `E0` lies as `H2K5.Row.E0` (Johnson/Desc/First/Att/Row/K5FrontE0.lean).
  **`E1`** : `proofThree.B.plan.plan.rounds = dryProofFull.2.1.map (·.1.entry)` · **`E2`** : the
  like at
    C and .2.2 · **`O0` | `O1` | `O2`** : `proofThree.A | B | C.plan.plan.entries.length -
    proofThree.A | B | C.plan.plan.rounds.length = 0`.
  O0: the first plan's entries are its rounds: both are the dry runs' first list's entries
    (`priced_is`, `same_written` by the walker's law, `dry_is`, `E0`): no new decision.
Limits. The full size alone. All lists are WRITTEN values. Nothing on soundness. On hiding nothing.

-/
import Johnson.AtFull.Plans.PlansSameB
import Johnson.AtFull.Plans.PlansSameC
import Johnson.Desc.First.Att.Row.K5FrontE0

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Plans
open VerifiableInference.Number.ByRuns (proofThree)
open Johnson.G (dryProofFull)
open H2K5.Row (priced_is dry_is sameRuns_sound same_written)

theorem E1 : proofThree.B.plan.plan.rounds = dryProofFull.2.1.map (·.1.entry) := (of_sameB same_B).1

theorem O1 : proofThree.B.plan.plan.entries.length - proofThree.B.plan.plan.rounds.length = 0 :=
  (of_sameB same_B).2

theorem E2 : proofThree.C.plan.plan.rounds = dryProofFull.2.2.map (·.1.entry) := (of_sameB same_C).1

theorem O2 : proofThree.C.plan.plan.entries.length - proofThree.C.plan.plan.rounds.length = 0 :=
  (of_sameB same_C).2

/-- The first plan's entries are its rounds. -/
theorem entries0 : proofThree.A.plan.plan.entries = proofThree.A.plan.plan.rounds :=
  priced_is.trans ((sameRuns_sound _ _ _ same_written).trans (dry_is.symm.trans H2K5.Row.E0.symm))

theorem O0 : proofThree.A.plan.plan.entries.length - proofThree.A.plan.plan.rounds.length = 0 := by
  rw [entries0, Nat.sub_self]

end Johnson.AtFull.Plans

#print axioms Johnson.AtFull.Plans.E1
#print axioms Johnson.AtFull.Plans.O1
#print axioms Johnson.AtFull.Plans.E2
#print axioms Johnson.AtFull.Plans.O2
#print axioms Johnson.AtFull.Plans.entries0
#print axioms Johnson.AtFull.Plans.O0
