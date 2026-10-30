-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/No/BeforeOkL.lean: A NEGATIVE LINE: beforeOk SAYS NO AT `wpBefore`
(Johnson/AtFull/ProofPlan/At/Bent2.lean: the first chain's fourth row names the message 82 of its
own chain too, which is sent behind that block's first draw), BY THE ROAD OF THE POSITIVE LINE
(Johnson/AtFull/ProofPlan/At/BeforeOkL.lean). `wpBefore_L₁`: the test over the tables at the first
chain says no: one closed fact, by an evaluation in Lean's kernel. Two limits are raised for it:
maxRecDepth to 1000000; maxHeartbeats is lifted. `wp_beforeOkL_no`: so the test itself, by
`beforeOk_tab` at the three tables (At/No/BeforeTabs.lean).

Limits. A fact on a made-up value. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.At.No.BeforeTabs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc
open P2Law.OneWalk (beforeAtL beforeOk_tab)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wpBefore_L₁ : beforeAtL (wpTab₁, wpTab₂, wpTab₃) 0 0 wpBefore.first.blocksInOrder = false := by
  decide +kernel

theorem wp_beforeOkL_no : wpBefore.beforeOk = false := by
  rw [beforeOk_tab wpBefore wpBefore_tab₁ wpBefore_tab₂ wpBefore_tab₃, wpBefore_L₁]
  rfl

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wpBefore_L₁
#print axioms P2Law.ProofPlan.wp_beforeOkL_no
