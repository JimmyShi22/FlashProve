-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/LabelsOk.lean: ONE OF THE TESTS ON THE PLAN (`FileDescription.planOk`,
Johnson/Desc/Block.lean) AT THE WRITTEN DESCRIPTION `WP` (Johnson/AtFull/ProofPlan/WP.lean):
labelsOk. One closed fact, alone in its file. The number of the third chain's first own tree, which
the test reads, is laid in as the numeral 84 (`wp_firstTree₃`,
Johnson/AtFull/ProofPlan/At/RootsSum.lean); the rest is an evaluation in Lean's kernel. Two limits
are raised for it: maxRecDepth to 1000000; maxHeartbeats is lifted.

Limits. A fact on written values. That the proof file's description is alike to `WP` is not said
here. At `WP` every block's own test and fileOk are the literal true. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.At.RootsSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wp_labelsOk : WP.labelsOk = true := by
  unfold FileDescription.labelsOk
  rw [Johnson.AtFull.ProofPlan.wp_firstTree₃]
  decide +kernel

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wp_labelsOk
