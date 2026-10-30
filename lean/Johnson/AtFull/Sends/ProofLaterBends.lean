-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Sends/ProofLaterBends.lean: CONTROLS THAT BITE for
Johnson/AtFull/Sends/ProofLater.lean's closed facts p1B | p2B: against each of five bends of the
written value, each of which turns one thing inside its sendings
(Johnson/AtFull/Sends/Bends.lean), the comparison says no.
Two short closed facts by Lean's kernel.
Nothing on soundness.

-/
import Johnson.AtFull.Sends.Bends
import Johnson.AtFull.Sends.ProofLater

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Sends

open Johnson.G

theorem p1B_bends : noneOf p1R (bendsOf proofSendsFull.2.1) = true := by decide +kernel
theorem p2B_bends : noneOf p2R (bendsOf proofSendsFull.2.2) = true := by decide +kernel

end Johnson.AtFull.Sends

#print axioms Johnson.AtFull.Sends.p1B_bends
#print axioms Johnson.AtFull.Sends.p2B_bends
