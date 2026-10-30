-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/CondAtPlanned.lean: the condition of the law of a proximity test (the kind K12)
at the places made off what `madeOf` makes of the three public files.

`k12Condition_at_made_L`, `_U`, `_O`, `_W` (CondAtMade.lean) ask `oneRadB`. Here that premise is
exchanged for another: `madeOf pol lay KL = .ok m`; at Omega's test besides that the shape says that
the shared chain splits (RoundsMore.lean strikes that one).
Main names: `planned_of_madeOf`: what `madeOf` returns holds what the program's `planned` returned.
`k12Condition_at_madeOf_L`, `_U`, `_O`, `_W`.
This file stands above Johnson/Bridge/ through its imports, and so above
Cb/Bridge/CodeListRSProved.lean and the files under ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Limits: an exchange of premises, not a premise less. Left on the planner's record: `planTestsB
Rad.planner`, and that the plans' round "BASE" of the test's number has the setting's bits of work
at the test's scope; beside them the yes of `placesOfMade`, of the block's test on the plan and of
`pubOk`. The numbers 0 to 3 of the rounds "BASE" are right only where all four tests have such a
round, so only where the shared chain splits. `planTestsB` makes a test of each of its nine lists of
stages that is not empty and asks that they are nine (Johnson/Bridge/PlanTests.lean): so it says no
where Omega's list is empty. It speaks of a planner's return: where a law is stated at a written
plan, the premise on `madeOf` is not at hand. No member: m is a variable. Nothing on soundness.
Nothing on hiding.

-/
import Johnson.Desc.K12.Law.OneRadB
import Johnson.Desc.K12.Law.OneRadPlanned

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Johnson.G.OfPlan
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Bridge (Rad baseWorks planTestsB)
open H2U (placesOfMade laterOfProof Places4 PlaceNums proximityTestParametersAt)
open H2K.Made (workShared workOwn)
open scoped ENNReal

/-- What `madeOf` returns holds what the program's `planned` returned. -/
theorem planned_of_madeOf {pol lay KL : ByteArray} {m : Made} (h : madeOf pol lay KL = .ok m) :
    OnBytes.Model.Verify.planned pol KL (some lay) = .ok m.p := by
  unfold madeOf at h
  obtain ⟨p, hp, h⟩ := exc_bind h
  obtain ⟨l, _, h⟩ := exc_bind h
  split at h
  · cases h
    exact hp
  · cases h

section
variable {Cl : Type} {pol lay KL : ByteArray} (m : Made) (hm : madeOf pol lay KL = .ok m)
  (X : Places4) (h : placesOfMade m = .ok X) (place : Place) (K : Codes)
  (hM : planTestsB Rad.planner m.p.chains.made = true)
include hm h hM

theorem k12Condition_at_madeOf_L
    (hw : (baseWorks m.p.chains.made)[0]? =
      some (m.p.chains.made.sized.set.workOf .query .request))
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.L) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place X.L) K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.last.stages)
      (proximityTestParametersAt place X.L) K ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_made_L m X h place K hM hw
    (oneRadB_of_oneRad (oneRad_planned (planned_of_madeOf hm) _).1) hp hpub

theorem k12Condition_at_madeOf_U
    (hw : (baseWorks m.p.chains.made)[1]? = some (workShared (laterOfProof m 0)))
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.U) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place X.U) K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.folded.stages)
      (proximityTestParametersAt place X.U) K ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_made_U m X h place K hM hw
    (oneRadB_of_oneRad (oneRad_planned (planned_of_madeOf hm) _).2.1) hp hpub

theorem k12Condition_at_madeOf_O (o : PlaceNums) (ho : X.O = some o)
    (hs : m.p.chains.made.sized.proof.batch.shape.sharedSplitNeeded = true)
    (hw : (baseWorks m.p.chains.made)[2]? = some (workShared (laterOfProof m 0)))
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place o) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place o) K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.omega.stages)
      (proximityTestParametersAt place o) K ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_made_O m X h place K hM o ho hw
    (oneRadB_of_oneRad ((oneRad_planned (planned_of_madeOf hm) _).2.2.1 hs)) hp hpub

theorem k12Condition_at_madeOf_W
    (hw : (baseWorks m.p.chains.made)[3]? = some (workOwn (laterOfProof m 0)))
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.W) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place X.W) K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.own.stages)
      (proximityTestParametersAt place X.W) K ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_made_W m X h place K hM hw
    (oneRadB_of_oneRad (oneRad_planned (planned_of_madeOf hm) _).2.2.2) hp hpub

end

end H2K.Pub

#print axioms H2K.Pub.k12Condition_at_madeOf_L
#print axioms H2K.Pub.k12Condition_at_madeOf_U
#print axioms H2K.Pub.k12Condition_at_madeOf_O
#print axioms H2K.Pub.k12Condition_at_madeOf_W
