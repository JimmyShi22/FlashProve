-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/No/BookInOrder.lean: A NEGATIVE LINE: ONE OF THE TESTS ON THE PLAN
(`FileDescription.planOk`, Johnson/Desc/Block.lean) SAYS NO AT `wpInOrder`
(Johnson/AtFull/ProofPlan/At/Bent2.lean: the written description with one thing turned): the clause
"inOrder" of BookPlan. Its positive line: Johnson/AtFull/ProofPlan/At/Book/InOrder.lean. One closed
fact, by an evaluation in Lean's kernel, alone in its file. Two limits are raised for it:
maxRecDepth to 1000000; maxHeartbeats is lifted.

Limits. A fact on a made-up value. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.At.Bent2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wp_book_inOrder_no : BookPlan.inOrder wpInOrder.roundsDeclaredByBlocks = false := by
  decide +kernel

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wp_book_inOrder_no
