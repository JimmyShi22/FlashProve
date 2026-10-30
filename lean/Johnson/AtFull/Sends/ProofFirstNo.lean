-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Sends/ProofFirstNo.lean: THE CONTROL OF Johnson/AtFull/Sends/ProofFirst.lean's CLOSED
FACT p0B: held against the SECOND chain's written value the same test comes out false: so the test
can fail. One closed fact by Lean's kernel. Nothing on soundness.
-/
import Johnson.AtFull.Sends.ProofFirst

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Sends

open Johnson.G

theorem p0B_no : isB p0R proofSendsFull.2.1 = false := by decide +kernel

end Johnson.AtFull.Sends

#print axioms Johnson.AtFull.Sends.p0B_no
