-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/KeyFirstListed.lean: where the planner's first routine for a key file returns
at the typed sizes of a key of full size, it returns the first of the key file's written priced
plans (Johnson/G/PricedKeyLit.lean), field by field: 18852 rounds.

How. The routine itself (`Plan.oneTimePlan`, OnBytes/Plan/KeyOneTime.lean) is not evaluated. By
`oneTimePlan_rounds` (OnBytes/Plan/PlanListsKey.lean), a plan that it returns has the setting of the
sizes, and its rounds are those of a plain list (`oneTimeList`), each made into a round by
`RoundSpec.round` (OnBytes/Params/PlanningLaws.lean). Lean's kernel evaluates that list at `keyFull`
(Johnson/Goal/PlanValues/KeySizedReturns.lean) and holds it against the written plan in one walk:
the setting, and all seven fields of every round (`rideB`,
Johnson/Desc/Ok/NumberPrices/ByRuns.lean).

Definitions.
  `firstListed`: the setting of `keyFull` with the rounds of `oneTimeList keyFull`.
Statements.
  `ride_first_list`: the test says yes. `first_listed`: so `firstListed` is the first written plan:
    a closed equation.
  `first_written`: if `Plan.oneTimePlan keyFull` returns P, then P is the first written plan.
  `ride_first_bent`: against the first written plan with one error doubled the test says no.
By evaluations in Lean's kernel (`decide +kernel`): `ride_first_list`, `ride_first_bent`.

What of OnBytes/Model/ is used: nothing by name.

Limits. That `Plan.oneTimePlan keyFull` returns is not shown. Nothing says that an error bounds a
count. Nothing on soundness.
-/
import Johnson.Goal.PlanValues.KeySizedReturns
import Johnson.Desc.Ok.NumberPrices.KeyAtWrittenTeeth
import OnBytes.Plan.PlanListsKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.Number
open OnBytes OnBytes.Params Lk6.AtPlan Johnson.G

/-- The setting of the typed sizes with the rounds of the list of the one-time chain's plan. -/
def firstListed : Planned :=
  ⟨keyFull.set, (Plan.oneTimeList keyFull).map (·.round keyFull.set .once)⟩

set_option maxRecDepth 1000000 in
theorem ride_first_list : rideB 30000 firstListed keyThree.A = true := by decide +kernel

/-- **The listed plan is the first written plan.** -/
theorem first_listed : firstListed = keyThree.A.plan := ride_eq ride_first_list

/-- **Where the planner's first routine returns at the typed sizes, it returns the first written
plan.** -/
theorem first_written {P : Planned} (h : Plan.oneTimePlan keyFull = .ok P) :
    P = keyThree.A.plan := by
  have I := Plan.oneTimePlan_rounds h
  have e : P = firstListed := by
    obtain ⟨s, rs⟩ := P
    have e1 : s = keyFull.set := I.set
    have e2 : rs = (Plan.oneTimeList keyFull).map (·.round keyFull.set .once) := I.rounds
    rw [e1, e2]
    rfl
  exact e.trans first_listed

set_option maxRecDepth 1000000 in
/-- Against the first written plan with one error doubled the test says no. -/
theorem ride_first_bent :
    rideB 30000 firstListed
      ⟨pricedKeySetFull, scaleAt 1 twice pricedKeyRecsFull0, pricedKeyRunsFull0⟩ = false := by
  decide +kernel

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.ride_first_list
#print axioms VerifiableInference.Number.ByRuns.first_listed
#print axioms VerifiableInference.Number.ByRuns.first_written
#print axioms VerifiableInference.Number.ByRuns.ride_first_bent
