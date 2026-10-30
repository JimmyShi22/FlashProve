-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.K12CutSplit
import Johnson.Desc.Ok.NumberPrices.ProofAtWritten
import Johnson.Desc.Ok.PlanWritten.SizedLit
/-
H2K12/K12CutNamesW.lean: ONE CLOSED FACT FOR THE
PROXIMITY TEST's (the kind K12's) ROW, ALONE IN ITS FILE, since it is an evaluation in Lean's kernel
along the first chain's written list of rounds (proofThree.A,
Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean: 48,293 rounds).
  namesW           H2U.testCutAt's own test (fewer than two stages, or the names from entry number
                   48,237 on are not "BAT" and the tower's) says NO at the written stages of the
                   last test (proofSizedFull.request.last,
                   Johnson/Desc/Ok/PlanWritten/SizedLit.lean): so the routine does not refuse there
The number was first seen in a print of Lean's evaluator; here the kernel decides it. A written
value: that the planner makes it of any public files is not said. No soundness statement. Nothing on
hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Number.ByRuns (proofThree)
open VerifiableInference.PlanWritten (proofSizedFull)
open H2U (towerLen towerNames)

theorem namesW :
    (decide (proofSizedFull.request.last.length < 2) ||
      (((proofThree.A.plan.rounds.map (·.entry)).drop 48237).take
        (1 + towerLen proofSizedFull.request.last)).map (·.name) !=
        "BAT" :: towerNames proofSizedFull.request.last) = false := by
  decide +kernel

end H2K12

#print axioms H2K12.namesW
