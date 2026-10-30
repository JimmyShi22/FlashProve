-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/No/Tab3.lean: A NEGATIVE LINE: THE TABLE (`P2Law.OneWalk.tabOf`,
Johnson/AtFull/ProofPlan/OneWalk.lean) OF THE SECOND CHAIN IS NOT THE WRITTEN ONE (`wpTab₃`,
Johnson/AtFull/ProofPlan/At/TabLit.lean) WHERE THE DISTINCT DECLARED ROUND NUMBER 132, WHICH STANDS
IN THAT CHAIN ALONE, SENDS ONE ROOT MORE. One closed fact, by an evaluation in Lean's kernel, alone
in its file. Two limits are raised for it: maxRecDepth to 1000000; maxHeartbeats is lifted. Its
positive line: Johnson/AtFull/ProofPlan/At/Tab3.lean.

Limits. A fact on a made-up value. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.At.Bent2
import Johnson.AtFull.ProofPlan.At.TabLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc
open P2Law.OneWalk (tabOf)

/-- `WP` with the distinct declared round number 132 sending one root more. -/
def wpRoots₃ : FileDescription Unit :=
  wpRec 132 fun r => { r with entry := { r.entry with roots := r.entry.roots + 1 } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wp_tab₃_no : tabOf wpRoots₃.roundsDeclaredByBlocks.2.2 (oraclesOf wpRoots₃.second.blocksInOrder) ≠ wpTab₃ := by
  decide +kernel

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wp_tab₃_no
