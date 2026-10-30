-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingLines.lean: the test on the plan (`planPlaysB`,
K12/PlanPlaysAt.lean) at the written place of the first chain's closing test (`piLFull`,
Johnson/Desc/K12/Law/PlacesFull.lean), 77 trees in front, the fresh table come earlier: by the
evaluator first, then by the kernel. ClosingLinesHead.lean carries it to the seated place.

  `plan_L`              it is true there
  `plan_L_own`, `plan_L_76`, `plan_L_78`   controls: the other word on the fresh table, no; another
                        number in front, no

Limits. It reads the plan alone: no run, no half, no job. The number 77 is the place's field `free`;
that the chain has sent as many is `treesTo_354` (K12/OffAt354.lean), under the head. The written place is a closed term. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.PlanKernel
import Johnson.Desc.K12.Law.PlacesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12.AtFile
open H2K.Member (piLFull)
open ProofFile.Honest.K12 (planPlaysB)

-- What each clause says: plan, sorts, tables, count, stored, wide.
#eval planClauses piLFull false 77
#eval planClauses piLFull true 77
#eval planClauses piLFull false 76
#eval planClauses piLFull false 78

#guard piLFull.nums.free == 77 && !piLFull.nums.ownMask

-- THE LINE. Foretold: yes.
#guard planPlaysB piLFull false 77

-- CONTROLS. Foretold: no.
#guard !planPlaysB piLFull true 77
#guard !planPlaysB piLFull false 76
#guard !planPlaysB piLFull false 78

/-- At the first chain's closing test. -/
theorem plan_L : planPlaysB piLFull false 77 = true := by decide +kernel

theorem plan_L_own : planPlaysB piLFull true 77 = false := by decide +kernel

theorem plan_L_76 : planPlaysB piLFull false 76 = false := by decide +kernel

theorem plan_L_78 : planPlaysB piLFull false 78 = false := by decide +kernel

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.plan_L
#print axioms ProofFile.Honest.K12.AtFile.plan_L_own
#print axioms ProofFile.Honest.K12.AtFile.plan_L_76
#print axioms ProofFile.Honest.K12.AtFile.plan_L_78
