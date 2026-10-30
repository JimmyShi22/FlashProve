-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/KeyLaterListed.lean: two routines of the planner, at the typed sizes of a key
of full size (`keyFull`, Johnson/Goal/PlanValues/KeySizedReturns.lean), return the second and the
third of the key file's written priced plans (Johnson/G/PricedKeyLit.lean), field by field: 68 and
30 rounds.

Lean's kernel evaluates each call whole and holds the answer against the written plan: the setting,
and all seven fields of every round (`rideAt`, Johnson/Desc/Ok/NumberPrices/ByRuns.lean). The two
equations are closed: they have no premise, and they name no public file, no digest and no hash.

Statements.
  `ride_shared`, `ride_second`: the two tests say yes.
  `shared_written`: `sharedPlan keyFull.set keyFull.codes keyFull.once` returns the second written
    plan. `second_written`: `secondPlan keyFull.set keyFull.once` returns the third.
By evaluations in Lean's kernel (`decide +kernel`): `ride_shared`, `ride_second`.

What of OnBytes/Model/ is used: nothing by name.

Limits. Four changed plans at which the tests say no are in
Johnson/Goal/Numbers/KeyPlansWritten.lean. Nothing says that an
error bounds a count. Nothing on soundness.
-/
import Johnson.Goal.PlanValues.KeySizedReturns
import Johnson.Desc.Ok.NumberPrices.KeyAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.Number
open OnBytes OnBytes.Params Lk6.AtPlan Johnson.G

set_option maxRecDepth 1000000 in
theorem ride_shared :
    rideAt 200 (sharedPlan keyFull.set keyFull.codes keyFull.once) keyThree.B = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem ride_second : rideAt 200 (secondPlan keyFull.set keyFull.once) keyThree.C = true := by
  decide +kernel

/-- **The planner's second routine, at the typed sizes, returns the second written plan.** -/
theorem shared_written :
    sharedPlan keyFull.set keyFull.codes keyFull.once = .ok keyThree.B.plan :=
  rideAt_eq ride_shared

/-- **Its third routine returns the third written plan.** -/
theorem second_written : secondPlan keyFull.set keyFull.once = .ok keyThree.C.plan :=
  rideAt_eq ride_second

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.ride_shared
#print axioms VerifiableInference.Number.ByRuns.ride_second
#print axioms VerifiableInference.Number.ByRuns.shared_written
#print axioms VerifiableInference.Number.ByRuns.second_written
