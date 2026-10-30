-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.K12CutSplit
import Johnson.Desc.Ok.NumberPrices.ProofAtWritten
/-
H2K12/K12LocsW.lean: ONE CLOSED FACT FOR THE
PROXIMITY TEST's (the kind K12's) ROW, ALONE IN ITS FILE, since it is an evaluation in Lean's kernel
along the first chain's written list of rounds (proofThree.A,
Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean: 48,293 rounds).
  locsW            25 of the list's rounds are named "LOC" (and not "RECORD"): one eager count along
                   the runs (cntG, Johnson/G/Runs.lean), in the form in which count_of_lit
                   (H2K12/K12CutSplit.lean) ends
The number was first seen in a print of Lean's evaluator; here the kernel decides it. A written
value: that the planner makes it of any public files is not said. No soundness statement. Nothing on
hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Number.ByRuns (proofThree)
open OnBytes.Params (PlanRound)
open Johnson.G.Runs (cntG valRuns)

theorem locsW :
    cntG (fun r : PlanRound => (r.entry.name == "LOC") && (r.entry.name != Fmt.recordName)) 0
      (valRuns proofThree.A.recs proofThree.A.runs) = 25 := by
  decide +kernel

end H2K12

#print axioms H2K12.locsW
