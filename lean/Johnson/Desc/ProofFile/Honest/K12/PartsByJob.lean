-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PartsByJob.lean: the two parts of PartsBy.lean for a job that is
given on words (`RunJob`, RunJob.lean). `runHalfOf R` is `halfBy` at the job `R.toTest`, with
`runBy` at the input `RunIn.ofRun R` as the function that computes the rounds. `lightHalfOf R` is
`runHalfOf R` where the stages pass the check `StagesOk` (RunBy.lean), and `proverSideOfProximityTest R.toTest`
(Parts.lean) elsewhere. Definitions only. It imports Mathlib.

PartsByJobLaw.lean proves `runHalfOf R = proverSideOfProximityTest R.toTest` where the stages pass `StagesOk`
(`runHalfOf_eq`), and `lightHalfOf R = proverSideOfProximityTest R.toTest` for every R (`lightHalfOf_eq`).

Limits.
- The limits of PartsBy.lean and of RunJob.lean apply.
- The counts of random values and the numbers of rounds are computed from `R.toTest`. They depend on
  its fields `p`, `members` and `fresh` only.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.PartsBy
import Johnson.Desc.ProofFile.Honest.K12.RunJob

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light

variable {V W X : Type}

/-- `runBy` at the input computed on words, as a function that computes all that is shown. S: the
five expensive functions of a run (`Seams`, Run.lean). -/
def runTermOf (S : Seams) (R : RunJob W X) : Term W X :=
  fun w fr K D => (runBy S (RunIn.ofRun R w fr K) D).toB

/-- The two parts with `runBy` at its fastest functions, for a job on words. Not for a prover's side
that is used: where `StagesOk` fails, `runBy` can send a row's end unmasked (see `stagesBy`,
RunBy.lean). Use `lightHalfOf`. -/
def runHalfOf (R : RunJob W X) : Placed V W X := halfBy R.toTest (runTermOf Seams.fast R)

/-- `runHalfOf R` where the job's stages pass `StagesOk`, `proverSideOfProximityTest R.toTest` elsewhere. It equals
`proverSideOfProximityTest R.toTest` for every R (`lightHalfOf_eq`, PartsByJobLaw.lean). Which branch a run takes is
the value of `StagesOk R.p.nums.stages`: where it is false, the run computes with `testAll`. -/
def lightHalfOf (R : RunJob W X) : Placed V W X :=
  if StagesOk R.p.nums.stages then runHalfOf R else proverSideOfProximityTest R.toTest

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.runTermOf
#print axioms ProofFile.Honest.K12.Light.runHalfOf
#print axioms ProofFile.Honest.K12.Light.lightHalfOf
