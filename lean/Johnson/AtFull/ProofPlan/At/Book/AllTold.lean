-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/Book/AllTold.lean: ONE CLAUSE OF THE TESTS FOR THE TREES' TENANTS AND
OPENINGS (`BookPlan.clauses`, Johnson/Desc/BookPlan.lean: "allTold") AT THE WRITTEN DESCRIPTION `WP`
(Johnson/AtFull/ProofPlan/WP.lean). One closed fact, alone in its file. The three sums of roots that
the clause reads are laid in as the numerals 83, 11 and 4 (`allTold_of_sums`, `wp_roots₁` to
`wp_roots₃`, Johnson/AtFull/ProofPlan/At/RootsSum.lean); the rest is an evaluation in Lean's kernel.
Two limits are raised for it: maxRecDepth to 1000000; maxHeartbeats is lifted.

Limits. A fact on written values. That the proof file's description is alike to `WP` is not said
here. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.At.RootsSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wp_book_allTold : BookPlan.sentOraclesMatchEntries WP.roundsDeclaredByBlocks WP.roots = true := by
  rw [Johnson.AtFull.ProofPlan.allTold_of_sums Johnson.AtFull.ProofPlan.wp_roots₁
    Johnson.AtFull.ProofPlan.wp_roots₂ Johnson.AtFull.ProofPlan.wp_roots₃]
  decide +kernel

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wp_book_allTold
