-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/KeyPlaceFacts.lean: a test: the seven public tests
`PlaceFacts` (Sim/FirstAnyAtPlace.lean) at three places of a proximity test in the key file's
description: the ranges' test, the test on G_u and the own test, where the first fold's fresh table
has come earlier. The places are the seated ones themselves: in the goals' scope the description
seats its tests at two written values (`key_head`, Sim/KeyHead.lean), so nothing is carried over
from another place. Closed facts on public numbers, by the kernel's own evaluation. No property is
claimed.

  `pKR`, `pKU`, `pKW`   the three places, made of `rangesNumsFull` and `laterPlacesFull`
                 (Johnson/HB/LLHARD/KB8/Written.lean) as the description makes them
  `dsOne`        a list of challenges, written by hand: each is one field element, the same one
  `k_KR`, `k_KU`, `k_KW`   the first stage's number of fold rounds
  `facts_KR`, `facts_KU`, `facts_KW`   `PlaceFacts`, each of seven evaluations beside it

By what. `decide +kernel`; `formPubB` and `tabB` under `set_option maxRecDepth 100000`, as in
Sim/FirstPubAtHead.lean. The two guards are evaluated by the compiler.

Limits.
- A "true" counts nothing by itself: these are tests of a place against itself.
- The two written values are terms over the library's typed sizes of a key (`keyFull`) and setting;
  three of each place's numbers were typed off a print of the planner (that file's limits).
- The test on G_omega, whose first fold sends its own table, is not here.
- The full size alone. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtPlace
import Johnson.Desc.ProofFile.Honest.K12.Sim.KeyHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block Key.rangesParams)
open VerifiableInference.Desc
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open H2K.JointK (laidOf pOwnK)
open Johnson.KB8 (rangesNumsFull laterPlacesFull)

/-! ## 1 The seated places, and written lists of challenges -/

/-- The place of the ranges' test, as the key file's description seats it in scope. -/
def pKR : P12 := Key.rangesParams rangesNumsFull

/-- The place of the test on G_u. -/
def pKU : P12 := H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ laterPlacesFull.U

/-- The place of the own test. -/
def pKW : P12 := pOwnK laterPlacesFull

/-- n challenges, each of one field element. -/
def dsOne (n : ℕ) : List Fmt.Drawn := List.replicate n ⟨[(1, 0, 0)], [], [], none⟩

/-! ## 2 The ranges' test -/

theorem k_KR : (pKR.nums.stages.headD default).k = 4 := by decide +kernel

theorem plan_KR : (proximityTestKind guardedProximityTestParts pKR : Block T12 Unit).planOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem form_KR : formPubB pKR = true := by decide +kernel

theorem enough_KR : firstLen pKR.nums.stages ≤ (laidOf pKR).length := by decide +kernel

set_option maxRecDepth 100000 in
theorem tab_KR : tabB pKR false = true := by decide +kernel

theorem count_KR : (laidOf pKR).length = firstLen pKR.nums.stages + restLen pKR.nums.stages := by
  decide +kernel

theorem quiet_KR : quietB (((laidOf pKR).take (firstLen pKR.nums.stages)).map (·.1)) = true := by
  decide +kernel

theorem draws_KR :
    drawsFit (((laidOf pKR).take (firstLen pKR.nums.stages)).map (·.1)) (dsOne 6) = true := by
  decide +kernel

theorem facts_KR : PlaceFacts pKR (dsOne 6) :=
  ⟨plan_KR, form_KR, enough_KR, tab_KR, count_KR, quiet_KR, draws_KR⟩

/-! ## 3 The test on G_u -/

theorem k_KU : (pKU.nums.stages.headD default).k = 7 := by decide +kernel

theorem plan_KU : (proximityTestKind guardedProximityTestParts pKU : Block T12 Unit).planOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem form_KU : formPubB pKU = true := by decide +kernel

theorem enough_KU : firstLen pKU.nums.stages ≤ (laidOf pKU).length := by decide +kernel

set_option maxRecDepth 100000 in
theorem tab_KU : tabB pKU false = true := by decide +kernel

theorem count_KU : (laidOf pKU).length = firstLen pKU.nums.stages + restLen pKU.nums.stages := by
  decide +kernel

theorem quiet_KU : quietB (((laidOf pKU).take (firstLen pKU.nums.stages)).map (·.1)) = true := by
  decide +kernel

theorem draws_KU :
    drawsFit (((laidOf pKU).take (firstLen pKU.nums.stages)).map (·.1)) (dsOne 9) = true := by
  decide +kernel

theorem facts_KU : PlaceFacts pKU (dsOne 9) :=
  ⟨plan_KU, form_KU, enough_KU, tab_KU, count_KU, quiet_KU, draws_KU⟩

/-! ## 4 The own test -/

theorem k_KW : (pKW.nums.stages.headD default).k = 5 := by decide +kernel

theorem plan_KW : (proximityTestKind guardedProximityTestParts pKW : Block T12 Unit).planOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem form_KW : formPubB pKW = true := by decide +kernel

theorem enough_KW : firstLen pKW.nums.stages ≤ (laidOf pKW).length := by decide +kernel

set_option maxRecDepth 100000 in
theorem tab_KW : tabB pKW false = true := by decide +kernel

theorem count_KW : (laidOf pKW).length = firstLen pKW.nums.stages + restLen pKW.nums.stages := by
  decide +kernel

theorem quiet_KW : quietB (((laidOf pKW).take (firstLen pKW.nums.stages)).map (·.1)) = true := by
  decide +kernel

theorem draws_KW :
    drawsFit (((laidOf pKW).take (firstLen pKW.nums.stages)).map (·.1)) (dsOne 7) = true := by
  decide +kernel

theorem facts_KW : PlaceFacts pKW (dsOne 7) :=
  ⟨plan_KW, form_KW, enough_KW, tab_KW, count_KW, quiet_KW, draws_KW⟩

-- a list of another length does not have the declared form
#guard !drawsFit (((laidOf pKR).take (firstLen pKR.nums.stages)).map (·.1)) (dsOne 5)
-- at the other flag the test on the tables says no
#guard !tabB pKR true && !tabB pKU true && !tabB pKW true

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.pKR
#print axioms ProofFile.Honest.K12.Light.pKU
#print axioms ProofFile.Honest.K12.Light.pKW
#print axioms ProofFile.Honest.K12.Light.dsOne
#print axioms ProofFile.Honest.K12.Light.k_KR
#print axioms ProofFile.Honest.K12.Light.plan_KR
#print axioms ProofFile.Honest.K12.Light.form_KR
#print axioms ProofFile.Honest.K12.Light.enough_KR
#print axioms ProofFile.Honest.K12.Light.tab_KR
#print axioms ProofFile.Honest.K12.Light.count_KR
#print axioms ProofFile.Honest.K12.Light.quiet_KR
#print axioms ProofFile.Honest.K12.Light.draws_KR
#print axioms ProofFile.Honest.K12.Light.facts_KR
#print axioms ProofFile.Honest.K12.Light.k_KU
#print axioms ProofFile.Honest.K12.Light.plan_KU
#print axioms ProofFile.Honest.K12.Light.form_KU
#print axioms ProofFile.Honest.K12.Light.enough_KU
#print axioms ProofFile.Honest.K12.Light.tab_KU
#print axioms ProofFile.Honest.K12.Light.count_KU
#print axioms ProofFile.Honest.K12.Light.quiet_KU
#print axioms ProofFile.Honest.K12.Light.draws_KU
#print axioms ProofFile.Honest.K12.Light.facts_KU
#print axioms ProofFile.Honest.K12.Light.k_KW
#print axioms ProofFile.Honest.K12.Light.plan_KW
#print axioms ProofFile.Honest.K12.Light.form_KW
#print axioms ProofFile.Honest.K12.Light.enough_KW
#print axioms ProofFile.Honest.K12.Light.tab_KW
#print axioms ProofFile.Honest.K12.Light.count_KW
#print axioms ProofFile.Honest.K12.Light.quiet_KW
#print axioms ProofFile.Honest.K12.Light.draws_KW
#print axioms ProofFile.Honest.K12.Light.facts_KW
