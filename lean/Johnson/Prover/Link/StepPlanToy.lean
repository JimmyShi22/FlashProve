-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/StepPlanToy.lean: PlanFrom (Johnson/Prover/Link/FormStepPlan.lean) CAN BE MET,
AND ITS TEST (planFromOk, Johnson/Prover/Link/StepPlanOk.lean) CAN SAY NO: at the toy's place
(Johnson/Prover/Link/ToyParts.lean: three stages, two switches), its codes, and the rounds that the
frame deals to the stages (laidS, Johnson/Desc/K12/Law/ReadsK.lean).

What is checked when the file compiles (#guard, by evaluation): the test says yes and no clause
refuses; there are three stages; a step has forty clauses. SEVEN CONTROLS: a turned plan, and THE
VERY LIST of the clauses that then refuse (planFromNo): two answers to a sample (there a second
command checks that the test itself says no) · the masks not early · a declared round dropped · a
code's messages twice as long · the first fold sends a mask of its own · another first free own
number (TestNums.free, Johnson/Desc/K12/TestEntries.lean) · a stage that draws one position more.
The lists are written here; why just these clauses refuse is not argued here.

Main names (namespace Johnson.Prover.Link.Toy).
  stepsNo   the clauses that refuse at a place.
  planFrom_toy   THE STATEMENT: PlanFrom holds at these arguments.

Limits. A TOY's: made-up numbers. Of the forty clauses of a step these are made to refuse by no
control: stage, stageN, idx, hk, hkN, folds, ok, vars, shortN, fits, the four of sized, room, three
of codes, zk, zkN, nk, nh, lengths, the two of bounds, cutS, trees, oneTree. SIX OF THE SEVEN
CONTROLS HOLD planFromNo, THE NAMES, ALONE: there no command holds that planFromOk says no, and
nothing ties the two but their text (StepPlanOk.lean). planFrom_toy goes by the kernel's evaluation
(decide +kernel). A #guard line is run by Lean's evaluator (compiled code, outside the kernel) and
leaves no theorem. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.StepPlanOk
import Johnson.Prover.Link.ToyParts
import Johnson.Desc.K12.Law.ReadsK

set_option autoImplicit false

namespace Johnson.Prover.Link.Toy
open OnBytes OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK (laidS)

/-- the clauses that refuse at a place, at codes and at rounds still to be dealt -/
def stepsNo (p : P12) (l : Laid) (K : Codes) : List String :=
  planFromNo p (p.nums.stages.drop 1) 0 (p.nums.stages.getD 0 default) l K

#guard planFromOk p12 (p12.nums.stages.drop 1) 0 (st 0) (laidS p12) tinyCodes
#guard stepsNo p12 (laidS p12) tinyCodes = []
#guard p12.nums.stages.length = 3
#guard (stepPlanL p12 tinyCodes 0 (st 0) (st 1) false (laidS p12) default default default
  default).length = 40
-- CONTROLS: a turned plan, and the clauses that then refuse ("the step's number : the field")
-- two answers to a sample
#guard stepsNo { p12 with answers := 2 } (laidS p12) tinyCodes = ["0:one", "1:one"]
-- there the test itself says no
#guard !planFromOk { p12 with answers := 2 } (p12.nums.stages.drop 1) 0 (st 0) (laidS p12) tinyCodes
-- the masks do not come early
#guard stepsNo { p12 with early := false } (laidS p12) tinyCodes = ["0:early", "1:early"]
-- the first switch's round "SEND seed" is dropped from the rounds still to be dealt
#guard stepsNo p12 ((laidS p12).eraseIdx 4) tinyCodes =
  ["0:cutSw", "0:opensS", "0:opensC", "0:drawE", "0:poss", "0:count", "0:Dealt", "1:cutF",
   "1:cutSw", "1:opensS", "1:opensC", "1:drawE", "1:poss", "1:count", "1:Dealt", "2:cut",
   "2:drawE", "2:logN", "2:Dealt"]
-- the second stage's main code has messages twice as long
#guard stepsNo p12 (laidS p12)
  { tinyCodes with base := tinyCodes.base.modify 1 fun c => { c with ell := 2 * c.ell } } =
  ["0:codeN", "1:codes.base"]
-- the first fold sends a mask of its own
#guard stepsNo { p12 with nums := { p12.nums with ownMask := true } } (laidS p12) tinyCodes =
  ["0:Dealt", "0:ownMask", "1:label", "1:Dealt", "1:ownMask", "2:Dealt", "2:ownMask"]
-- another first free own number (TestNums.free: the roots that the chain has received in front)
#guard stepsNo { p12 with nums := { p12.nums with free := 2 } } (laidS p12) tinyCodes =
  ["0:Dealt", "1:Dealt", "2:Dealt"]
-- the first stage draws one position more, in the argument cur alone (the plan's list is unturned)
#guard planFromNo p12 (p12.nums.stages.drop 1) 0 { st 0 with t := 3 } (laidS p12) tinyCodes =
  ["0:poss", "0:count", "0:stages"]

/-- **PlanFrom holds at the toy's place.** -/
theorem planFrom_toy : PlanFrom p12 (p12.nums.stages.drop 1) 0 (st 0) (laidS p12) tinyCodes :=
  planFrom_of_ok _ _ _ _ _ _ (by decide +kernel)

end Johnson.Prover.Link.Toy
