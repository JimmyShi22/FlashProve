-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PartsByJobLaw.lean: for a job R that is given on words (`RunJob`,
RunJob.lean): `lightHalfOf R = proverSideOfProximityTest R.toTest` for every R, and `runHalfOf R = proverSideOfProximityTest R.toTest`
where the stages pass `StagesOk` (RunBy.lean). `runHalfOf` and `lightHalfOf` are defined in
PartsByJob.lean, `proverSideOfProximityTest` in Parts.lean. It imports Mathlib.

  `runTermOf_eq`   where the stages pass `StagesOk`, `runBy` at `Seams.fast` and `RunIn.ofRun R`
                 gives the rounds, trees and opened columns of `testAll R.toTest`
  `Spec.runHalfOf_eq`, `runHalfOf_eq`   the second equation as a named `Prop`, and its proof
  `lightHalfOf_eq`   the first equation

By what. `runTermOf_eq` is `fast_eq` (FastWLaw.lean) followed by `runJob_eq` (RunJobLaw.lean). Then
`halfBy_testAll` (PartsByLaw.lean). `lightHalfOf_eq` splits on the value of `StagesOk`.

Limits.
- `runHalfOf_eq` has one hypothesis, `StagesOk R.p.nums.stages = true`. It says nothing of other
  jobs.
- `lightHalfOf_eq` has no hypothesis and does not say which branch `lightHalfOf R` takes: where
  `StagesOk` is false, `lightHalfOf R` is `proverSideOfProximityTest R.toTest` by definition.
- `StagesOk` is proved at literal parameter sets (RunBySpecAt.lean) and at every p whose block
  passes its test on the plan (`stagesOk_of_planOk`, StagesOfPlan.lean); at a job with such a p,
  `lightHalfOf R` is `runHalfOf R` by definition. That a job's p is such a p is for the caller to
  show.
- The right side is `proverSideOfProximityTest` at `R.toTest`, which is built from R: so the equations say nothing on
  the rows, such as whether a tail is there. See RunJob.lean's limits.
- Two definitions give the same value. Nothing follows on what a verifier decides. Nothing on
  completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.PartsByJob
import Johnson.Desc.ProofFile.Honest.K12.PartsByLaw
import Johnson.Desc.ProofFile.Honest.K12.RunJobLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light

variable {V W X : Type}

theorem runTermOf_eq (R : RunJob W X) (ok : StagesOk R.p.nums.stages = true) :
    runTermOf Seams.fast R = testAll R.toTest := by
  funext w fr K D
  rw [fast_eq]
  exact runJob_eq R w fr K D ok

def Spec.runHalfOf_eq : Prop :=
  ∀ (V W X : Type) (R : RunJob W X), StagesOk R.p.nums.stages = true →
    (runHalfOf R : Placed V W X) = proverSideOfProximityTest R.toTest

theorem runHalfOf_eq : Spec.runHalfOf_eq := by
  intro V W X R ok
  unfold runHalfOf
  rw [runTermOf_eq R ok, halfBy_testAll]

/-- `lightHalfOf R` equals `proverSideOfProximityTest R.toTest` for every R. -/
theorem lightHalfOf_eq (R : RunJob W X) : (lightHalfOf R : Placed V W X) = proverSideOfProximityTest R.toTest := by
  unfold lightHalfOf
  split
  · rename_i h
    exact runHalfOf_eq V W X R h
  · rfl

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.runTermOf_eq
#print axioms ProofFile.Honest.K12.Light.runHalfOf_eq
#print axioms ProofFile.Honest.K12.Light.lightHalfOf_eq
#print axioms ProofFile.Honest.K12.Light.Spec.runHalfOf_eq
