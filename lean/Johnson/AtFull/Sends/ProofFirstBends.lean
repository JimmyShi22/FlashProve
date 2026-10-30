-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Sends/ProofFirstBends.lean: A CONTROL THAT BITES for
Johnson/AtFull/Sends/ProofFirst.lean's closed fact p0B: against each of five bends of the first
chain's written value, each of which turns one thing inside its 82 sendings
(Johnson/AtFull/Sends/Bends.lean), the comparison says no: so the test looks into the sendings.
One closed fact by Lean's kernel.
Nothing on soundness.
-/
import Johnson.AtFull.Sends.Bends

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Sends

open Johnson.G

theorem p0B_bends : noneOf p0R (bendsOf proofSendsFull.1) = true := by decide +kernel

end Johnson.AtFull.Sends

#print axioms Johnson.AtFull.Sends.p0B_bends
