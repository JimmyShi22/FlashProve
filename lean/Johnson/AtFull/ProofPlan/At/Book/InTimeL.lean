-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/Book/InTimeL.lean: ONE CLAUSE OF THE TESTS FOR THE TREES' TENANTS AND
OPENINGS (`BookPlan.clauses`, Johnson/Desc/BookPlan.lean: "inTime") AT THE WRITTEN DESCRIPTION `WP`
(Johnson/AtFull/ProofPlan/WP.lean). `wp_inTimeL`: the clause over the three written tables
(`P2Law.OneWalk.inTimeL`, Johnson/AtFull/ProofPlan/OneWalk.lean): one closed fact, by an evaluation
in Lean's kernel. Two limits are raised for it: maxRecDepth to 1000000; maxHeartbeats is lifted.
`wp_book_inTimeL`: so the clause itself, by `inTime_tab` at the three tables (At/Tab1.lean,
Tab2.lean, Tab3.lean).

Limits. A fact on written values. That the proof file's description is alike to `WP` is not said
here. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.At.Tab1
import Johnson.AtFull.ProofPlan.At.Tab2
import Johnson.AtFull.ProofPlan.At.Tab3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc
open P2Law.OneWalk (inTimeL inTime_tab)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wp_inTimeL : inTimeL WP.roundsDeclaredByBlocks (wpTab₁, wpTab₂, wpTab₃) = true := by decide +kernel

theorem wp_book_inTimeL : BookPlan.inTime WP.roundsDeclaredByBlocks WP.roots = true :=
  (inTime_tab WP.roundsDeclaredByBlocks (oraclesOf WP.first.blocksInOrder) (oraclesOf WP.shared.blocksInOrder)
    (oraclesOf WP.second.blocksInOrder) wp_tab₁ wp_tab₂ wp_tab₃).trans wp_inTimeL

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wp_inTimeL
#print axioms P2Law.ProofPlan.wp_book_inTimeL
