-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/StepPlanFull.lean: PlanFrom (Johnson/Prover/Link/FormStepPlan.lean) AT THE FULL
SIZE: at the place of the link's proximity test (pF := p12Of frP,
Johnson/Prover/Link/DoorPlanFull.lean), the typed parameters' codes, and the rounds that the frame
deals to the stages (laidS, Johnson/Desc/K12/Law/ReadsK.lean): FIVE STAGES: four steps with a
switch, and the last.

Main names (namespace Johnson.Prover.Link.Full).
  planFromOk_full   the test of Johnson/Prover/Link/StepPlanOk.lean says yes: ONE evaluation by the
    kernel (decide +kernel).
  planFrom_full   THE STATEMENT: PlanFrom holds at these arguments.
  rest_full, planFrom_full_cons   the stages behind the first begin with the second; planFrom_full
    in that form, off which a step is taken.

What is checked besides when the file compiles (#guard): no clause refuses; there are five stages.
Controls, where planFromNo names the clauses that refuse and, at one of them, planFromOk says no: at
the toy, Johnson/Prover/Link/StepPlanToy.lean; this file holds none.

Limits. Public numbers alone: no record, no view, no value. That the statement's codes in front of
the test are these codes is not shown here. A #guard line is run by Lean's evaluator (compiled code,
outside the kernel) and leaves no theorem. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.StepPlanOk
import Johnson.Prover.Link.DoorPlanFull
import Johnson.Desc.K12.Law.ReadsK

set_option autoImplicit false

namespace Johnson.Prover.Link.Full
open OnBytes OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.K12 Desc.K15
open H2K.JointK (laidS)

#guard planFromNo pF (pF.nums.stages.drop 1) 0 curF (laidS pF) frP.codes = []
#guard pF.nums.stages.length = 5

/-- The test says yes at the full size: by the kernel's evaluation. -/
theorem planFromOk_full :
    planFromOk pF (pF.nums.stages.drop 1) 0 curF (laidS pF) frP.codes = true := by
  decide +kernel

/-- **PlanFrom AT THE FULL SIZE**: four steps and the last stage. -/
theorem planFrom_full : PlanFrom pF (pF.nums.stages.drop 1) 0 curF (laidS pF) frP.codes :=
  planFrom_of_ok _ _ _ _ _ _ planFromOk_full

/-- The stages behind the first begin with the second. -/
theorem rest_full : pF.nums.stages.drop 1 = nxtF :: pF.nums.stages.drop 2 := by decide +kernel

/-- The same, with the stages behind the first written as a list that begins: the form in which a
step is taken off it. -/
theorem planFrom_full_cons :
    PlanFrom pF (nxtF :: pF.nums.stages.drop 2) 0 curF (laidS pF) frP.codes :=
  rest_full ▸ planFrom_full

end Johnson.Prover.Link.Full
