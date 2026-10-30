-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingLinesHead.lean: the test on the plan at the seated
place of the first chain's closing test, under the library's head.

  `planPlaysB_head_L`   at the seated place
  `planPlays_head_L`    `PlanPlays` at every job at the seated place whose fresh table came earlier

By what. `plan_L` (ClosingLines.lean); `planPlaysB_congr` (PlanAtSeat.lean in this folder);
`nums_head_L` (AtFullSide/K12/RestTiesAtHeadL.lean); `reads_head_L`, `facts_LFull`
(AtFullSide/K12/FirstAnyAtHeadL.lean); `thin_of_reads` (Sim/ThinOfReads.lean).

Limits. Conditional on the head, at the full size. Public numbers alone. Nothing on completeness,
soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingLines
import Johnson.Desc.ProofFile.Honest.K12.AtFile.PlanAtSeat
import AtFullSide.K12.RestTiesAtHeadL

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12.AtFile
open H2K.Member (piLFull)
open ProofFile.Honest.K12 (TestJob PlanPlays planPlaysB planPlays_of_B)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light (nums_head_L reads_head_L facts_LFull thin_of_reads)

variable {W X : Type}
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **At the seated place of the first chain's closing test**, under the head. -/
theorem planPlaysB_head_L (h : P5J.AtMg o Z D r Zp Np cF) :
    planPlaysB (fourOf Np).L false 77 = true := by
  obtain ⟨h1, h2, h3, h4⟩ := reads_head_L h
  rw [planPlaysB_congr (nums_head_L h)
    (thin_of_reads VerifiableInference.Desc.K12.guardedProximityTestParts h1 h2 h3 h4 facts_LFull.plan) h4
    facts_LFull.plan]
  exact plan_L

/-- **`PlanPlays` at every job at the seated place** whose fresh table has come earlier. -/
theorem planPlays_head_L (h : P5J.AtMg o Z D r Zp Np cF) (J : TestJob W X)
    (hJ : J.p = (fourOf Np).L) (hfr : J.fresh.isNone = false) (s : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: rest) : PlanPlays J s rest 77 :=
  planPlays_of_B J s rest hst 77 (by
    rw [hJ, hfr]
    exact planPlaysB_head_L h)

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.planPlaysB_head_L
#print axioms ProofFile.Honest.K12.AtFile.planPlays_head_L
