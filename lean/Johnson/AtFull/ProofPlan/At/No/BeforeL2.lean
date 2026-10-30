-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/No/BeforeL2.lean: A NEGATIVE LINE: THE TEST `beforeAt` OVER TABLES
(`P2Law.OneWalk.beforeAtL`, Johnson/AtFull/ProofPlan/OneWalk.lean) SAYS NO AT THE SHARED CHAIN WHERE
ITS FIRST ROW NAMES THE CHAIN's OWN LAST MESSAGE (number 10), WHICH IS SENT BEHIND THAT BLOCK. One
closed fact, by an evaluation in Lean's kernel, alone in its file. Two limits are raised for it:
maxRecDepth to 1000000; maxHeartbeats is lifted. Its positive line:
Johnson/AtFull/ProofPlan/At/BeforeL2.lean.

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

/-- `WP` with the shared chain's first row naming that chain's message 10 too. -/
def wpBefore₂ : FileDescription Unit :=
  wOf cutFirstFull (cutSharedFull.modify 0 fun r =>
      (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, (2, 10) :: r.2.2.2.2.2)) cutSecondFull
    declProofFull 32

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wp_beforeL₂_no :
    beforeAtL (wpTab₁, wpTab₂, wpTab₃) 1 0 wpBefore₂.shared.blocksInOrder = false := by
  decide +kernel

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wp_beforeL₂_no
