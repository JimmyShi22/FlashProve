-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`E2E/StagesAtOrBeyondHalfTheDistance.lean`: at the full size, at every stage of the nine proximity tests the decoding
radius lies within the Johnson bound and at or beyond half the stage's distance.

The list `Johnson.Bridge.testsFull`, written out in the library, has nine proximity tests with 43 stages in all. The
rows of a stage lie in two Reed-Solomon codes: the main rows' code, of distance `Sg.dC`, and the mask rows' code,
repeated to the same length, of distance `Sg.dZ`. The stage's distance `Sg.d` (`OnBytes/Slice/Numbers.lean`) is the
smaller of the two. `e` is the stage's decoding radius.

What this file proves.
* `stage_at_or_beyond_half_the_distance`: at all 43 stages `d ≤ 2 * e`. `main_code_at_or_beyond_half_the_distance`: at
  all 43 stages `dC ≤ 2 * e`.
* `below_and_in_johnson`, `in_johnson_of`: at all 43 stages `e < d`, and the library's Johnson condition
  `Cb.InJohnson` holds at the length `2 ^ C.a`, the stage's distance `d` and the radius `e`.
* `count`: nine tests, 43 stages. `at_or_beyond_can_fail_at_a_stage`: the test is not vacuous: at the radius 0 it
  returns false at the first stage of the first test.
* `typed_at_or_beyond_half_the_distance`: `d ≤ 2 * e` at every stage of `typedNine` (`E2E/RadiiAreThePlans.lean`), at
  the planner's own radii.
* `plan_stages_at_or_beyond_half_the_distance`: under the premise without free variables `H2K.Sizes.LayoutGroupsAre` (see
  `E2E/RadiiAreThePlans.lean`), for all public files `Z` in scope and every plan that the verifier's planner returns
  at `Z`: at every stage of each of the plan's nine tests, `(stageOf y.g y.t).d ≤ 2 * radiusOf t.1 y.g`.
* All but `in_johnson_of` and the last are evaluated by Lean's kernel.

What this file does not say.
* These are numbers alone. Which rule or theorem bounds a round's soundness error is not touched. The library's error
  counts at a stage (`Sg.StageJ.counts`, `OnBytes/Slice/ManyHoldsJoh.lean`) are stated under a hypothesis on codes,
  `Cb.BCHKS46At`; whoever joins these numbers to an error bound must name it. The library proves it
  (`Cb.Gl.bchks46At`, `Cb/Bridge/GlCodesProved.lean`) over files under `ThirdParty/` adapted from
  ArkLib and Mathlib: see `lean/LIMITS.md`, L15. The other fields of `StageJ` are not shown at the 43 stages here.
* The distance is the stage's, and the main rows' code's. Of the mask rows' code taken alone nothing is said here.
* Only the stages of the nine tests are treated. Not here: the committed table (`E2E/SampleAndJohnsonInScope.lean`),
  the sampled messages of sendings (`Johnson/G/PackLitArms.lean`, at a literal list), the groups of the proof file's
  links as they are closed, and the batching.
* "Distance" is the library's number for a Reed-Solomon code: length less dimension plus 1; for the repeated mask
  code, that number times the number of repeats. That it is the code's minimum distance, and no more than it, is not
  proved here.
* The statement in scope goes one way: from a planner that returns. It imports `E2E/RadiiAreThePlans.lean`, and all
  limits stated there apply.
-/
import E2E.RadiiAreThePlans
import OnBytes.Slice.Numbers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Bridge.AtPlan
open OnBytes OnBytes.Params OnBytes.Slice
open Johnson.Bridge (testsFull nineTests)
open Johnson.Top.H (stageOf radiusOf)

/-- **At every stage of the nine tests the radius is at least half the stage's distance.** -/
theorem stage_at_or_beyond_half_the_distance :
    (testsFull.all fun T => T.stages.all fun x => decide (x.1.d ≤ 2 * x.2)) = true := by decide +kernel

/-- The same of the main row's code alone. -/
theorem main_code_at_or_beyond_half_the_distance :
    (testsFull.all fun T => T.stages.all fun x => decide (x.1.dC ≤ 2 * x.2)) = true := by decide +kernel

/-- At every stage the radius is below the stage's distance and within the library's Johnson condition. -/
theorem below_and_in_johnson :
    (testsFull.all fun T => T.stages.all fun x =>
      decide (x.2 < x.1.d) && decide (2 ^ x.1.C.a * (2 ^ x.1.C.a - x.1.d) < (2 ^ x.1.C.a - x.2) ^ 2)) = true := by
  decide +kernel

/-- What the second clause of that test is. -/
theorem in_johnson_of {T : Johnson.Bridge.TestAt} (hT : T ∈ testsFull) {x : Sg × ℕ} (hx : x ∈ T.stages) :
    x.2 < x.1.d ∧ Cb.InJohnson (2 ^ x.1.C.a) x.1.d x.2 := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 below_and_in_johnson T hT) x hx
  rw [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

/-- Nine tests, 43 stages. -/
theorem count : testsFull.length = 9 ∧ (testsFull.map (·.stages.length)).sum = 43 := by decide +kernel

/-- A control: at the radius 0 the first stage of the first test is not at or beyond half its distance. -/
theorem at_or_beyond_can_fail_at_a_stage :
    ((testsFull.head?).bind fun T => T.stages.head?.map fun x => decide (x.1.d ≤ 2 * 0)) = some false := by
  decide +kernel

/-- The same at `typedNine`, at the planner's own radii. -/
theorem typed_at_or_beyond_half_the_distance :
    (typedNine.all fun t => t.2.all fun y => decide ((stageOf y.g y.t).d ≤ 2 * radiusOf t.1 y.g)) = true := by
  decide +kernel

/-- **In scope, at every plan: every stage of the plan's nine tests, at the planner's own radius, is at or beyond half its distance.** -/
theorem plan_stages_at_or_beyond_half_the_distance (groups : H2K.Sizes.LayoutGroupsAre) {Z : VerifierAndGoals.PublicFiles} (scope : VerifierAndGoals.InScope Z = true) {p : Model.Verify.Planned}
    (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    ∀ t ∈ nineTests p.chains.made.sized, ∀ y ∈ t.2, (stageOf y.g y.t).d ≤ 2 * radiusOf t.1 y.g := by
  rw [nine_in_scope groups scope hp]
  intro t ht y hy
  exact of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 typed_at_or_beyond_half_the_distance t ht) y hy)

end Johnson.Bridge.AtPlan

#print axioms Johnson.Bridge.AtPlan.stage_at_or_beyond_half_the_distance
#print axioms Johnson.Bridge.AtPlan.main_code_at_or_beyond_half_the_distance
#print axioms Johnson.Bridge.AtPlan.below_and_in_johnson
#print axioms Johnson.Bridge.AtPlan.in_johnson_of
#print axioms Johnson.Bridge.AtPlan.count
#print axioms Johnson.Bridge.AtPlan.at_or_beyond_can_fail_at_a_stage
#print axioms Johnson.Bridge.AtPlan.typed_at_or_beyond_half_the_distance
#print axioms Johnson.Bridge.AtPlan.plan_stages_at_or_beyond_half_the_distance
#check @Johnson.Bridge.AtPlan.plan_stages_at_or_beyond_half_the_distance
