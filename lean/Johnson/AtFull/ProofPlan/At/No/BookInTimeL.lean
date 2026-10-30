-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/No/BookInTimeL.lean: A NEGATIVE LINE: THE CLAUSE "inTime" OF BookPlan
SAYS NO AT `wpInTime` (Johnson/AtFull/ProofPlan/At/Bent2.lean: the distinct declared round number 38
opens, as its first tree, the chain's own tree 82, which is sent far behind it), BY THE ROAD OF THE
POSITIVE LINE (Johnson/AtFull/ProofPlan/At/Book/InTimeL.lean). `wpInTime_L`: the clause over the
tables says no: one closed fact, by an evaluation in Lean's kernel. Two limits are raised for it:
maxRecDepth to 1000000; maxHeartbeats is lifted. `wp_book_inTimeL_no`: so the clause itself, by
`inTime_tab` at the three tables (At/No/InTimeTabs.lean).

Limits. A fact on a made-up value. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.At.No.InTimeTabs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc
open P2Law.OneWalk (inTimeL inTime_tab)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wpInTime_L : inTimeL wpInTime.roundsDeclaredByBlocks (wpTab₁, wpTab₂, wpTab₃) = false := by decide +kernel

theorem wp_book_inTimeL_no : BookPlan.inTime wpInTime.roundsDeclaredByBlocks wpInTime.roots = false :=
  (inTime_tab wpInTime.roundsDeclaredByBlocks (oraclesOf wpInTime.first.blocksInOrder) (oraclesOf wpInTime.shared.blocksInOrder)
    (oraclesOf wpInTime.second.blocksInOrder) wpInTime_tab₁ wpInTime_tab₂ wpInTime_tab₃).trans wpInTime_L

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wpInTime_L
#print axioms P2Law.ProofPlan.wp_book_inTimeL_no
