-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/BeforeL3.lean: THE TEST `beforeAt` OVER TABLES
(`P2Law.OneWalk.beforeAtL`, Johnson/AtFull/ProofPlan/OneWalk.lean) AT THE SECOND CHAIN OF THE
WRITTEN DESCRIPTION `WP` (Johnson/AtFull/ProofPlan/WP.lean), OVER THE THREE WRITTEN TABLES
(Johnson/AtFull/ProofPlan/At/TabLit.lean). One closed fact, by an evaluation in Lean's kernel, alone
in its file. Two limits are raised for it: maxRecDepth to 1000000; maxHeartbeats is lifted.

Limits. A fact on written values. That the proof file's description is alike to `WP` is not said
here. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.WP
import Johnson.AtFull.ProofPlan.At.TabLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc
open P2Law.OneWalk (beforeAtL)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wp_beforeL₃ : beforeAtL (wpTab₁, wpTab₂, wpTab₃) 2 0 WP.second.blocksInOrder = true := by
  decide +kernel

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wp_beforeL₃
