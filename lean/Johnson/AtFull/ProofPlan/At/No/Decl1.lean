-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/No/Decl1.lean: A NEGATIVE LINE: ONE OF THE TESTS ON THE PLAN
(`FileDescription.planOk`, Johnson/Desc/Block.lean) SAYS NO AT `wpPlans`
(Johnson/AtFull/ProofPlan/At/Bent.lean: the written description with one thing turned): the first
chain's declared rounds against the plan's. Its positive line:
Johnson/AtFull/ProofPlan/At/Decl1.lean. One closed fact, by an evaluation in Lean's kernel, alone in
its file. Two limits are raised for it: maxRecDepth to 1000000; maxHeartbeats is lifted.

Limits. A fact on a made-up value: the plan's list is emptied: it does not show that a round's
content is read (see Johnson/AtFull/ProofPlan/At/No/Decl1Short.lean). Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.At.Bent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wp_decl₁_no : (wpPlans.roundsDeclaredByBlocks.1 == wpPlans.plans.1) = false := by decide +kernel

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wp_decl₁_no
