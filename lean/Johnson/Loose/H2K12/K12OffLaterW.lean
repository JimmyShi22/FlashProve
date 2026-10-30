-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.K12CutSplit
import Johnson.Desc.Ok.NumberPrices.ProofAtWritten
/-
H2K12/K12OffLaterW.lean: TWO CLOSED FACTS FOR THE PROXIMITY TEST's (the
kind K12's) ROW, on the proof file's two SHORT written lists of rounds (proofThree.B, proofThree.C,
Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean: 68 and 30 rounds): so the two stand in one file.
  offW1            none of the second list's entries is named "RECORD": one eager count along the
                   runs (cntG, Johnson/G/Runs.lean), in the form in which off_of_lit
                   (H2K12/K12CutSplit.lean) ends. offW2: the like of the third list
By evaluations in Lean's kernel. Written values: that the planner makes them of any public files is
not said. No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Number.ByRuns (proofThree)
open OnBytes.Params (PlanRound)
open Johnson.G.Runs (cntG valRuns)

theorem offW1 :
    cntG (fun r : PlanRound => !(r.entry.name != Fmt.recordName)) 0
      (valRuns proofThree.B.recs proofThree.B.runs) = 0 := by
  decide +kernel

theorem offW2 :
    cntG (fun r : PlanRound => !(r.entry.name != Fmt.recordName)) 0
      (valRuns proofThree.C.recs proofThree.C.runs) = 0 := by
  decide +kernel

end H2K12

#print axioms H2K12.offW1
#print axioms H2K12.offW2
