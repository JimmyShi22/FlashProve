-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/No/BeforeL3.lean: A NEGATIVE LINE: THE TEST `beforeAt` OVER TABLES
(`P2Law.OneWalk.beforeAtL`, Johnson/AtFull/ProofPlan/OneWalk.lean) SAYS NO AT THE SECOND CHAIN WHERE
ITS FIRST ROW NAMES THE CHAIN's OWN LAST MESSAGE (number 3), WHICH IS SENT BEHIND THAT BLOCK. One
closed fact, by an evaluation in Lean's kernel, alone in its file. Two limits are raised for it:
maxRecDepth to 1000000; maxHeartbeats is lifted. Its positive line:
Johnson/AtFull/ProofPlan/At/BeforeL3.lean.

Limits. A fact on a made-up value. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.At.Bent2
import Johnson.AtFull.ProofPlan.At.TabLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc
open VerifiableInference.PlanWritten (cutFirstFull cutSharedFull cutSecondFull)
open P2Law.OneWalk (beforeAtL)

/-- `WP` with the second chain's first row naming that chain's message 3 too. -/
def wpBefore₃ : FileDescription Unit :=
  wOf cutFirstFull cutSharedFull (cutSecondFull.modify 0 fun r =>
      (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, (3, 3) :: r.2.2.2.2.2))
    declProofFull 32

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wp_beforeL₃_no :
    beforeAtL (wpTab₁, wpTab₂, wpTab₃) 2 0 wpBefore₃.second.blocksInOrder = false := by
  decide +kernel

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wp_beforeL₃_no
