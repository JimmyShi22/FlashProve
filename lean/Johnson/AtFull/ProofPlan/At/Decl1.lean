-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/Decl1.lean: ONE OF THE TESTS ON THE PLAN (`FileDescription.planOk`,
Johnson/Desc/Block.lean) AT THE WRITTEN DESCRIPTION `WP` (Johnson/AtFull/ProofPlan/WP.lean): the
first chain's declared rounds against the plan's. One closed fact, by an evaluation in Lean's
kernel, alone in its file. Two limits are raised for it: maxRecDepth to 1000000; maxHeartbeats is
lifted.

Limits. A fact on written values. That the proof file's description is alike to `WP` is not said
here. At `WP` every block's own test and fileOk are the literal true, and this test is true almost
by make (see Johnson/AtFull/ProofPlan/At/No/Decl1Short.lean). Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.WP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wp_decl₁ : (WP.roundsDeclaredByBlocks.1 == WP.plans.1) = true := by decide +kernel

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wp_decl₁
