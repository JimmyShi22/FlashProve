-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PlanAtKeyKernel.lean

The test on the plan (`planPlaysB`, PlanPlaysAt.lean in this folder) at the key file's two places
of the shared chain, BY THE KERNEL's OWN EVALUATION (`decide +kernel`). It imports
PlanAtKeyGuards.lean, where the evaluator says the same first.

  `plan_KU`, `plan_KO`   it is true at `piKUFull`, 3 trees in front, the fresh table come earlier;
                         at `piKOFull`, 7 in front, the first fold sending its own table
  `plan_KU_own`, `plan_KO_own`   controls: the other word on the fresh table, no
  `plan_KU_2`, `plan_KU_4`, `plan_KO_6`, `plan_KO_8`   controls: another number in front, no
  `planPlays_KU`, `planPlays_KO`   so `PlanPlays` at every job at that place with that word

Limits. It reads the plan alone: no run, no half, no job of the key. The numbers 3 and 7 are the
places' own field `free`; that they are what the chain has sent is not said here. `PlanPlays` is
one premise of `playsOn_k12`; the others are not touched, and `playsOn_k12` does not apply to a
half behind the guard. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.PlanAtKeyGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.PlanAtKey
open VerifiableInference.Desc.K12
open H2K.Member (piKUFull piKOFull)

variable {W X : Type}

set_option maxRecDepth 100000 in
/-- At the test on G_u. -/
theorem plan_KU : planPlaysB piKUFull false 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- At the test on G_omega, where the first fold sends its own table. -/
theorem plan_KO : planPlaysB piKOFull true 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Control: the other word on the fresh table. -/
theorem plan_KU_own : planPlaysB piKUFull true 3 = false := by decide +kernel

set_option maxRecDepth 100000 in
/-- Control: the other word on the fresh table. -/
theorem plan_KO_own : planPlaysB piKOFull false 7 = false := by decide +kernel

set_option maxRecDepth 100000 in
/-- Control: one tree fewer in front. -/
theorem plan_KU_2 : planPlaysB piKUFull false 2 = false := by decide +kernel

set_option maxRecDepth 100000 in
/-- Control: one tree more in front. -/
theorem plan_KU_4 : planPlaysB piKUFull false 4 = false := by decide +kernel

set_option maxRecDepth 100000 in
/-- Control: one tree fewer in front. -/
theorem plan_KO_6 : planPlaysB piKOFull true 6 = false := by decide +kernel

set_option maxRecDepth 100000 in
/-- Control: one tree more in front. -/
theorem plan_KO_8 : planPlaysB piKOFull true 8 = false := by decide +kernel

/-- `PlanPlays` at every job at the place of the test on G_u whose fresh table has come earlier. -/
theorem planPlays_KU (J : TestJob W X) (hJ : J.p = piKUFull) (hfr : J.fresh.isNone = false)
    (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: rest) :
    PlanPlays J s rest 3 :=
  planPlays_of_B J s rest hst 3 (by
    rw [hJ, hfr]
    exact plan_KU)

/-- `PlanPlays` at every job at the place of the test on G_omega whose first fold sends its own
table. -/
theorem planPlays_KO (J : TestJob W X) (hJ : J.p = piKOFull) (hfr : J.fresh.isNone = true)
    (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: rest) :
    PlanPlays J s rest 7 :=
  planPlays_of_B J s rest hst 7 (by
    rw [hJ, hfr]
    exact plan_KO)

end ProofFile.Honest.K12.PlanAtKey

#print axioms ProofFile.Honest.K12.PlanAtKey.plan_KU
#print axioms ProofFile.Honest.K12.PlanAtKey.plan_KO
#print axioms ProofFile.Honest.K12.PlanAtKey.plan_KU_own
#print axioms ProofFile.Honest.K12.PlanAtKey.plan_KO_own
#print axioms ProofFile.Honest.K12.PlanAtKey.plan_KU_2
#print axioms ProofFile.Honest.K12.PlanAtKey.plan_KU_4
#print axioms ProofFile.Honest.K12.PlanAtKey.plan_KO_6
#print axioms ProofFile.Honest.K12.PlanAtKey.plan_KO_8
#print axioms ProofFile.Honest.K12.PlanAtKey.planPlays_KU
#print axioms ProofFile.Honest.K12.PlanAtKey.planPlays_KO
