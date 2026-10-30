-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/No/BookAllTold.lean: A NEGATIVE LINE: ONE OF THE TESTS ON THE PLAN
(`FileDescription.planOk`, Johnson/Desc/Block.lean) SAYS NO AT `wpTold`
(Johnson/AtFull/ProofPlan/At/Bent2.lean: the written description with one thing turned): the clause
"sentOraclesMatchEntries" of BookPlan. Its positive line: Johnson/AtFull/ProofPlan/At/Book/AllTold.lean. One closed
fact, alone in its file. The three sums of roots that the clause reads are laid in as the numerals
83, 11 and 4 (Johnson/AtFull/ProofPlan/At/No/RootsSumTold.lean); what the blocks tell, which is what
is turned, is evaluated in Lean's kernel here. Two limits are raised for it: maxRecDepth to 1000000;
maxHeartbeats is lifted.

Limits. A fact on a made-up value. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.At.No.RootsSumTold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wp_book_allTold_no : BookPlan.sentOraclesMatchEntries wpTold.roundsDeclaredByBlocks wpTold.roots = false := by
  rw [Johnson.AtFull.ProofPlan.allTold_of_sums Johnson.AtFull.ProofPlan.wpTold_roots₁
    Johnson.AtFull.ProofPlan.wpTold_roots₂ Johnson.AtFull.ProofPlan.wpTold_roots₃]
  decide +kernel

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wp_book_allTold_no
