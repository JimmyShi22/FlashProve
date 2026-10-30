-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/Book/Range.lean: ONE CLAUSE OF THE TESTS FOR THE TREES' TENANTS AND
OPENINGS (`BookPlan.clauses`, Johnson/Desc/BookPlan.lean: "range") AT THE WRITTEN DESCRIPTION `WP`
(Johnson/AtFull/ProofPlan/WP.lean). One closed fact, by an evaluation in Lean's kernel, alone in its
file. Two limits are raised for it: maxRecDepth to 1000000; maxHeartbeats is lifted.

Limits. A fact on written values. That the proof file's description is alike to `WP` is not said
here. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.WP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wp_book_range : BookPlan.range WP.roundsDeclaredByBlocks = true := by
  decide +kernel

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wp_book_range
