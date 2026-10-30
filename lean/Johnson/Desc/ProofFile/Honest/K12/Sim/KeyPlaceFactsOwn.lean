-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/KeyPlaceFactsOwn.lean: a test: the nine public tests
`PlaceFactsOwn` (Sim/OwnAnyAtPlace.lean) at the place of the proximity test on G_omega in the key
file's description, whose first fold sends its own fresh table. The place is the seated one itself:
in the goals' scope the description seats its tests at two written values (`key_head`,
Sim/KeyHead.lean), and the second has a place for this test (`o_typed`,
Johnson/HB/LLHARD/KB8/Typed.lean). Closed facts on public numbers, by the kernel's own evaluation.
No property is claimed.

  `pKO`          the place, made of the library's typed `oT` as the description makes it
  `stage_KO`     five numbers of its first stage
  `facts_KO`     `PlaceFactsOwn`, of nine evaluations beside it
  `bud_KO_border`, `bud_KO_t`, `bud_KO_beyond`   `budFirst` (Sim/Row.lean) at written positions 0,
                 1, 2 and so on: true at Z.r of them and at t of them, false at one more than Z.r

By what. `decide +kernel`; `formPubB` and `tabB` under `set_option maxRecDepth 100000`, as in
Sim/FirstPubAtHead.lean. The guard is evaluated by the compiler.

Limits.
- A "true" counts nothing by itself: these are tests of a place against itself. `bud_KO_beyond` says
  nothing on the equation beyond the border.
- That the positions which a run reads of the fold's own tree are at most Z.r different ones is not
  shown.
- The full size alone. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.OwnAnyAtPlace
import Johnson.Desc.ProofFile.Honest.K12.Sim.KeyPlaceFacts
import Johnson.HB.LLHARD.KB8.Typed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open H2K.JointK (laidOf pGomega)
open Johnson.KB8 (oT)

/-- The place of the test on G_omega, as the key file's description seats it in scope. -/
def pKO : P12 := pGomega oT

/-- **Five numbers of the seated place's first stage.** -/
theorem stage_KO :
    (pKO.nums.stages.headD default).k = 4 ∧ (pKO.nums.stages.headD default).h = 0 ∧
      (pKO.nums.stages.headD default).Z.r = 146 ∧ (pKO.nums.stages.headD default).Z.a = 13 ∧
      (pKO.nums.stages.headD default).t = 49 := by decide +kernel

theorem plan_KO : (proximityTestKind guardedProximityTestParts pKO : Block T12 Unit).planOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem form_KO : formPubB pKO = true := by decide +kernel

theorem enough_KO : firstLen pKO.nums.stages ≤ (laidOf pKO).length := by decide +kernel

set_option maxRecDepth 100000 in
theorem tab_KO : tabB pKO true = true := by decide +kernel

theorem points_KO : (pKO.nums.stages.headD default).Z.a ≤ 32 := by decide +kernel

theorem count_KO : (laidOf pKO).length = firstLen pKO.nums.stages + restLen pKO.nums.stages := by
  decide +kernel

theorem quiet_KO : quietB (((laidOf pKO).take (firstLen pKO.nums.stages)).map (·.1)) = true := by
  decide +kernel

theorem draws_KO :
    drawsFit (((laidOf pKO).take (firstLen pKO.nums.stages)).map (·.1)) (dsOne 6) = true := by
  decide +kernel

theorem len_KO : (dsOne 6).length = firstLen pKO.nums.stages := by decide +kernel

theorem facts_KO : PlaceFactsOwn pKO (dsOne 6) :=
  ⟨plan_KO, form_KO, enough_KO, tab_KO, points_KO, count_KO, quiet_KO, draws_KO, len_KO⟩

/-- The bound at as many different positions as the mask code's tail has entries. -/
theorem bud_KO_border : budFirst (pKO.nums.stages.headD default) (asksTo 146) = true := by
  decide +kernel

/-- The bound at as many different positions as the first stage's t. -/
theorem bud_KO_t : budFirst (pKO.nums.stages.headD default) (asksTo 49) = true := by
  decide +kernel

/-- One position beyond the border the bound says no. It says nothing on the equation there. -/
theorem bud_KO_beyond : budFirst (pKO.nums.stages.headD default) (asksTo 147) = false := by
  decide +kernel

-- at the other flag the test on the tables says no
#guard !tabB pKO false

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.pKO
#print axioms ProofFile.Honest.K12.Light.stage_KO
#print axioms ProofFile.Honest.K12.Light.plan_KO
#print axioms ProofFile.Honest.K12.Light.form_KO
#print axioms ProofFile.Honest.K12.Light.enough_KO
#print axioms ProofFile.Honest.K12.Light.tab_KO
#print axioms ProofFile.Honest.K12.Light.points_KO
#print axioms ProofFile.Honest.K12.Light.count_KO
#print axioms ProofFile.Honest.K12.Light.quiet_KO
#print axioms ProofFile.Honest.K12.Light.draws_KO
#print axioms ProofFile.Honest.K12.Light.len_KO
#print axioms ProofFile.Honest.K12.Light.facts_KO
#print axioms ProofFile.Honest.K12.Light.bud_KO_border
#print axioms ProofFile.Honest.K12.Light.bud_KO_t
#print axioms ProofFile.Honest.K12.Light.bud_KO_beyond
