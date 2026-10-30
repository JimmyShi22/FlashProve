-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/No/BeforeTabs.lean: THE THREE CHAINS' TABLES (`P2Law.OneWalk.tabOf`,
Johnson/AtFull/ProofPlan/OneWalk.lean) OF `wpBefore` (Johnson/AtFull/ProofPlan/At/Bent2.lean: the
written description with one thing turned) ARE THE WRITTEN ONES
(Johnson/AtFull/ProofPlan/At/TabLit.lean): what is turned there is read by no table. Three closed
facts, by evaluations in Lean's kernel. Two limits are raised for it: maxRecDepth to 1000000;
maxHeartbeats is lifted. They serve a negative line.

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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wpBefore_tab₁ : tabOf wpBefore.roundsDeclaredByBlocks.1 (oraclesOf wpBefore.first.blocksInOrder) = wpTab₁ := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wpBefore_tab₂ : tabOf wpBefore.roundsDeclaredByBlocks.2.1 (oraclesOf wpBefore.shared.blocksInOrder) = wpTab₂ := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wpBefore_tab₃ : tabOf wpBefore.roundsDeclaredByBlocks.2.2 (oraclesOf wpBefore.second.blocksInOrder) = wpTab₃ := by
  decide +kernel

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wpBefore_tab₁
#print axioms P2Law.ProofPlan.wpBefore_tab₂
#print axioms P2Law.ProofPlan.wpBefore_tab₃
