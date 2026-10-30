-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/PlanKernel.lean: the test on the plan (`planPlaysB`,
K12/PlanPlaysAt.lean) at the proof file's three written places, BY THE KERNEL's OWN EVALUATION
(`decide +kernel`). It imports PlanGuards.lean, where the evaluator says the same first.

  `plan_U`, `plan_O`, `plan_W`   it is true at `piUFull`, 3 trees in front, the fresh table come
                 earlier; at `piOFull`, 7 in front, the first fold sending its own table; at
                 `piWFull`, none in front, the fresh table come earlier
  `plan_U_own`, `plan_O_own`, `plan_W_own`   controls: the other word on the fresh table, no
  `plan_U_2`, `plan_U_4`, `plan_O_6`, `plan_O_8`, `plan_W_1`   controls: another number in front, no
  `planNo_U_one`, `planNo_U_three`, `planNo_W_two`, `planNo_W_four`   `planB` (K12/PlanB.lean) reads
                 the number of trees that the first switch opens, from both sides: one clause
                 refuses. Beside `planB_U_full`, `planB_W_full` (Sim/TreesPlanAt.lean) and
                 `planONo_O_two`, `planONo_O_four` (Own/PlanOwn.lean)

Limits. It reads the plan alone: no run, no half, no job. The numbers 3, 7 and 0 are the places' own
field `free`; that they are what the chain has sent is not said here. The written places are closed
terms that a program made off the print of a run: that they are the places of a file is no theorem:
PlanAtSeat.lean carries these lines to the seated places, under the library's head. Nothing on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.PlanGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12.AtFile
open VerifiableInference.Desc.K12
open H2K.Member (piUFull piOFull piWFull codesFull)

/-- At the test on G_u. -/
theorem plan_U : planPlaysB piUFull false 3 = true := by decide +kernel

/-- At the test on G_omega, where the first fold sends its own table. -/
theorem plan_O : planPlaysB piOFull true 7 = true := by decide +kernel

/-- At the last chain's test, where no own tree stands in front. -/
theorem plan_W : planPlaysB piWFull false 0 = true := by decide +kernel

/-- Control: the other word on the fresh table. -/
theorem plan_U_own : planPlaysB piUFull true 3 = false := by decide +kernel

/-- Control: the other word on the fresh table. -/
theorem plan_O_own : planPlaysB piOFull false 7 = false := by decide +kernel

/-- Control: the other word on the fresh table. -/
theorem plan_W_own : planPlaysB piWFull true 0 = false := by decide +kernel

/-- Control: one tree fewer in front. -/
theorem plan_U_2 : planPlaysB piUFull false 2 = false := by decide +kernel

/-- Control: one tree more in front. -/
theorem plan_U_4 : planPlaysB piUFull false 4 = false := by decide +kernel

/-- Control: one tree fewer in front. -/
theorem plan_O_6 : planPlaysB piOFull true 6 = false := by decide +kernel

/-- Control: one tree more in front. -/
theorem plan_O_8 : planPlaysB piOFull true 8 = false := by decide +kernel

/-- Control: one tree more in front. -/
theorem plan_W_1 : planPlaysB piWFull false 1 = false := by decide +kernel

/-- The plan's half at G_u refuses one tree fewer opened, in one clause. -/
theorem planNo_U_one : planNo piUFull codesFull 1 = ["oS"] := by decide +kernel

/-- The plan's half at G_u refuses one tree more opened, in one clause. -/
theorem planNo_U_three : planNo piUFull codesFull 3 = ["oS"] := by decide +kernel

/-- The plan's half at the last chain's test refuses one tree fewer opened, in one clause. -/
theorem planNo_W_two : planNo piWFull codesFull 2 = ["oS"] := by decide +kernel

/-- The plan's half at the last chain's test refuses one tree more opened, in one clause. -/
theorem planNo_W_four : planNo piWFull codesFull 4 = ["oS"] := by decide +kernel

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.plan_U
#print axioms ProofFile.Honest.K12.AtFile.plan_O
#print axioms ProofFile.Honest.K12.AtFile.plan_W
#print axioms ProofFile.Honest.K12.AtFile.plan_U_own
#print axioms ProofFile.Honest.K12.AtFile.plan_O_own
#print axioms ProofFile.Honest.K12.AtFile.plan_W_own
#print axioms ProofFile.Honest.K12.AtFile.plan_U_2
#print axioms ProofFile.Honest.K12.AtFile.plan_U_4
#print axioms ProofFile.Honest.K12.AtFile.plan_O_6
#print axioms ProofFile.Honest.K12.AtFile.plan_O_8
#print axioms ProofFile.Honest.K12.AtFile.plan_W_1
#print axioms ProofFile.Honest.K12.AtFile.planNo_U_one
#print axioms ProofFile.Honest.K12.AtFile.planNo_U_three
#print axioms ProofFile.Honest.K12.AtFile.planNo_W_two
#print axioms ProofFile.Honest.K12.AtFile.planNo_W_four
