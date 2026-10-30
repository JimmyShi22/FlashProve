-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/No/Depth.lean: A NEGATIVE LINE: ONE OF THE TESTS ON THE PLAN
(`FileDescription.planOk`, Johnson/Desc/Block.lean) SAYS NO AT `wpDepth`
(Johnson/AtFull/ProofPlan/At/Bent.lean: the written description with one thing turned): the stored
parts' depth. Its positive line: Johnson/AtFull/ProofPlan/At/Depth.lean. One closed fact, by an
evaluation in Lean's kernel, alone in its file. Two limits are raised for it: maxRecDepth to
1000000; maxHeartbeats is lifted.

Limits. A fact on a made-up value. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.At.Bent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wp_depth_no :
    ((wpDepth.roundsDeclaredByBlocks.1 ++ wpDepth.roundsDeclaredByBlocks.2.1 ++ wpDepth.roundsDeclaredByBlocks.2.2).all
      (fun r => r.stored.all (·.sh.a == wpDepth.tableDepth))) = false := by
  decide +kernel

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wp_depth_no
