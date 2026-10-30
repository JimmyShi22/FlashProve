-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PartsByLaw.lean: `lightHalf J = proverSideOfProximityTest J` for every job, and
`runHalf J = proverSideOfProximityTest J` where the job's stages pass `StagesOk` (RunBy.lean). `runHalf` and
`lightHalf` are defined in PartsBy.lean, `proverSideOfProximityTest` in Parts.lean. Both sides are values of type
`Placed V W X` (Johnson/Desc/ProofFile/Honest/Frame.lean), so the equations cover all that a caller
can read of the two parts. Every theorem on `proverSideOfProximityTest J` carries over to `lightHalf J`, and to
`runHalf J` under the hypothesis. It imports Mathlib.

  `halfBy_testAll`   at `tm := testAll J` the copies of PartsBy.lean equal the originals of
                 Parts.lean, for every job
  `runTerm_eq`   where the stages pass `StagesOk`, `runBy` at `Seams.fast` and `RunIn.ofTest` gives
                 the rounds, trees and opened columns of `testAll J`
  `Spec.runHalf_eq`, `runHalf_eq`   the second equation as a named `Prop`, and its proof
  `lightHalf_eq`   the first equation

By what. `halfBy_testAll` holds by unfolding. `runTerm_eq` is `fast_eq` (FastWLaw.lean) followed by
`runBy_eq` (RunByEq.lean). `lightHalf_eq` splits on the value of `StagesOk`.

Limits.
- `runHalf_eq` has one hypothesis, `StagesOk J.p.nums.stages = true`. It says nothing of other jobs.
- `lightHalf_eq` has no hypothesis and does not say which branch `lightHalf J` takes: where
  `StagesOk` is false, `lightHalf J` is `proverSideOfProximityTest J` by definition.
- `StagesOk` is proved at literal parameter sets (RunBySpecAt.lean) and at every p whose block
  passes its test on the plan (`stagesOk_of_planOk`, StagesOfPlan.lean); at a job with such a p,
  `lightHalf J` is `runHalf J` by definition. That a job's p is such a p is for the caller to show.
- Two definitions give the same value. Nothing follows on what a verifier decides. Nothing on
  completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.PartsBy
import Johnson.Desc.ProofFile.Honest.K12.RunByEq
import Johnson.Desc.ProofFile.Honest.K12.FastWLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light

variable {V W X C : Type}

/-! ## 1 At `testAll` the copy equals the original -/

theorem msgBy_testAll (J : TestJob W X) : msgBy J (testAll J) = msgAt J := rfl

theorem moveBy_testAll (J : TestJob W X) (rd : C → TestCoins) (i : ℕ) :
    moveBy J (testAll J) rd i = moveAt J rd i := rfl

theorem movesBy_testAll (J : TestJob W X) (rd : C → TestCoins) (a n : ℕ) :
    movesBy J (testAll J) rd a n = movesFrom J rd a n := rfl

theorem firstPartBy_testAll (J : TestJob W X) :
    (firstPartBy J (testAll J) : Part V W X) = firstPart J := by
  unfold firstPartBy firstPart
  cases J.fresh <;> rfl

theorem restPartBy_testAll (J : TestJob W X) :
    (restPartBy J (testAll J) : Part V W X) = restPart J := rfl

/-- At `tm := testAll J` the copy `halfBy` equals the original `proverSideOfProximityTest`, for every job. -/
theorem halfBy_testAll (J : TestJob W X) :
    (halfBy J (testAll J) : Placed V W X) = proverSideOfProximityTest J := by
  unfold halfBy proverSideOfProximityTest
  rw [firstPartBy_testAll, restPartBy_testAll]

/-! ## 2 With `runBy` -/

theorem runTerm_eq (J : TestJob W X) (ok : StagesOk J.p.nums.stages = true) :
    runTerm Seams.fast J = testAll J := by
  funext w fr K D
  rw [fast_eq]
  exact runBy_eq W X J w fr K D ok

def Spec.runHalf_eq : Prop :=
  ∀ (V W X : Type) (J : TestJob W X), StagesOk J.p.nums.stages = true →
    (runHalf J : Placed V W X) = proverSideOfProximityTest J

theorem runHalf_eq : Spec.runHalf_eq := by
  intro V W X J ok
  unfold runHalf
  rw [runTerm_eq J ok, halfBy_testAll]

/-- `lightHalf J` equals `proverSideOfProximityTest J` for every job. -/
theorem lightHalf_eq (J : TestJob W X) : (lightHalf J : Placed V W X) = proverSideOfProximityTest J := by
  unfold lightHalf
  split
  · rename_i h
    exact runHalf_eq V W X J h
  · rfl

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.msgBy_testAll
#print axioms ProofFile.Honest.K12.Light.moveBy_testAll
#print axioms ProofFile.Honest.K12.Light.movesBy_testAll
#print axioms ProofFile.Honest.K12.Light.firstPartBy_testAll
#print axioms ProofFile.Honest.K12.Light.restPartBy_testAll
#print axioms ProofFile.Honest.K12.Light.halfBy_testAll
#print axioms ProofFile.Honest.K12.Light.runTerm_eq
#print axioms ProofFile.Honest.K12.Light.runHalf_eq
#print axioms ProofFile.Honest.K12.Light.lightHalf_eq
#print axioms ProofFile.Honest.K12.Light.Spec.runHalf_eq
