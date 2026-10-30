-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.K12CutSplit
import Johnson.Desc.Ok.NumberPrices.ProofAtWritten
/-
Johnson/Loose/H2K12/K12CutSplitWNo.lean:
ONE CLOSED FACT FOR THE PROXIMITY TEST's (the kind K12's)
ROW, ALONE IN ITS FILE, since it is an evaluation in Lean's kernel along the first chain's written
list of rounds (proofThree.A, Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean: 48,293 rounds).
  splitW_no        THE NEGATIVE TEST OF splitW (K12CutSplitW.lean): one place on, behind the
                   first 48,238 entries, the list is not at its end, and its head is NOT named "BAT"
The number was first seen in a print of Lean's evaluator; here the kernel decides it. A written
value: that the planner makes it of any public files is not said. No soundness statement. Nothing on
hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Number.ByRuns (proofThree)

theorem splitW_no :
    (match (proofThree.A.plan.rounds.map (·.entry)).drop 48238 with
      | e :: _ => !(e.name == "BAT")
      | [] => false) = true := by
  decide +kernel

end H2K12

#print axioms H2K12.splitW_no
