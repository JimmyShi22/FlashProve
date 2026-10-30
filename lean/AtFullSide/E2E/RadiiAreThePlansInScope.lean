-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`AtFullSide/E2E/RadiiAreThePlansInScope.lean`: the statements of `E2E/RadiiAreThePlans.lean`, `E2E/PackRadiiAreThePlans.lean` and
`E2E/StagesAtOrBeyondHalfTheDistance.lean` for public files in scope, with no premise beside the scope and the planner's return.

Those statements carry one premise without free variables, `H2K.Sizes.LayoutGroupsAre`. Here it is supplied by
`Johnson.AtFull.LayoutRead.layoutGroupsAre` (`AtFullSide/LayoutRead/GroupsPaid.lean`). Each theorem is one call. Throughout, `Z` is
in scope and `p` is a plan that the verifier's planner returns at `Z`.

What this file proves.
* `nine_under_the_scope_alone`: the plan's nine proximity tests are `typedNine`.
* `radii_are_the_plans_under_the_scope_alone`: the plan's nine tests and the nine tests written out in the library have the same
  stages with the same radii, and the radius that `radOf` looks up in a written test is the planner's.
* `pack_radii_are_the_plans_under_the_scope_alone`: every radius of the full-size list `Johnson.G.packFullLit` is the planner's at a
  group, with the message's code, of one of the plan's nine tests.
* `plan_stages_at_or_beyond_half_the_distance_under_the_scope_alone`: at every stage of the plan's nine tests, at the planner's own
  radius `e`, the stage's distance `d` satisfies `d ≤ 2 * e`.

What this file does not say.
* All limits stated in the three files apply.
* The file lies in the side library `AtFullSide/` because `GroupsPaid.lean` does.
-/
import E2E.PackRadiiAreThePlans
import E2E.StagesAtOrBeyondHalfTheDistance
import AtFullSide.LayoutRead.GroupsPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Bridge.AtPlan
open OnBytes
open Johnson.AtFull.LayoutRead (layoutGroupsAre)

variable {Z : VerifierAndGoals.PublicFiles} (scope : VerifierAndGoals.InScope Z = true) {p : Model.Verify.Planned}
  (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p)
include scope hp

/-- In scope the planner's nine tests are `typedNine`. -/
theorem nine_under_the_scope_alone : Johnson.Bridge.nineTests p.chains.made.sized = typedNine :=
  nine_in_scope layoutGroupsAre scope hp

/-- **In scope the written tests' stages and radii are the plan's.** -/
theorem radii_are_the_plans_under_the_scope_alone :
    ∀ x ∈ (Johnson.Bridge.nineTests p.chains.made.sized).zip order,
      Johnson.Bridge.stagesBy Johnson.Bridge.Rad.planner x.1.1 x.1.2 = (H2K.Pub.testNo Johnson.Bridge.testsFull x.2).stages ∧
      ∀ y ∈ x.1.2, H2K.Pub.radOf (H2K.Pub.testNo Johnson.Bridge.testsFull x.2) (Johnson.Top.H.stageOf y.g y.t) =
        Johnson.Top.H.radiusOf x.1.1 y.g :=
  radii_are_the_plans layoutGroupsAre scope hp

/-- **In scope every radius of the full-size list of sendings is the planner's at a group of the plan's nine tests with the message's code.** -/
theorem pack_radii_are_the_plans_under_the_scope_alone :
    ∀ x ∈ Johnson.G.packFullLit, ∀ y ∈ x.2, ∃ t ∈ Johnson.Bridge.nineTests p.chains.made.sized, ∃ z ∈ t.2,
      (if y.1.mainRows != 0 then Johnson.G.sameCode x.1.base[y.1.code]? z.g.main
        else Johnson.G.sameCode x.1.mask[y.1.maskCode]? z.g.mask) = true ∧ Johnson.G.radiusIn t.1 y.1 z.g = y.2 :=
  pack_radii_are_the_plans layoutGroupsAre scope hp

/-- **In scope every stage of the plan's nine tests, at the planner's own radius, is at or beyond half its distance.** -/
theorem plan_stages_at_or_beyond_half_the_distance_under_the_scope_alone :
    ∀ t ∈ Johnson.Bridge.nineTests p.chains.made.sized, ∀ y ∈ t.2,
      (Johnson.Top.H.stageOf y.g y.t).d ≤ 2 * Johnson.Top.H.radiusOf t.1 y.g :=
  plan_stages_at_or_beyond_half_the_distance layoutGroupsAre scope hp

end Johnson.Bridge.AtPlan

#print axioms Johnson.Bridge.AtPlan.nine_under_the_scope_alone
#print axioms Johnson.Bridge.AtPlan.radii_are_the_plans_under_the_scope_alone
#print axioms Johnson.Bridge.AtPlan.pack_radii_are_the_plans_under_the_scope_alone
#print axioms Johnson.Bridge.AtPlan.plan_stages_at_or_beyond_half_the_distance_under_the_scope_alone
