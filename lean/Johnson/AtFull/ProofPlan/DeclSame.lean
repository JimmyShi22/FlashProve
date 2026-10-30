-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/DeclSame.lean: TWO NAMES, ONE TERM: THE WRITTEN DECLARED ROUNDS OF A PROOF
FILE OF FULL SIZE STAND DEFINED TWICE IN THE LIBRARY; AND SO THE TESTS ON THE PLAN PASS AT THE
WRITTEN DESCRIPTION AT EITHER NAME. Two statements with their proofs. Nothing is evaluated here.

Why. `Johnson.AtFull.ProofRows.declProofFull` (Johnson/AtFull/ProofRows/WrittenProof.lean) and
`P2Law.ProofPlan.declProofFull` (Johnson/AtFull/ProofPlan/WP.lean) were written apart.
Each is the distinct declared rounds (`VerifiableInference.PlanWritten.declRecsFull`) laid out by
`Johnson.G.Runs.unrunG` along the three written lists of runs (`Johnson.G.dryProofRunsFull0`, `1`,
`2`). The first has the type `Decl3`, an abbreviation of the triple of lists that the second's type
writes out. `wp_planOk` (Johnson/AtFull/ProofPlan/WPPlanOk.lean) stands at the second name. The
master ledger of the proof file's side (Johnson/AtFull/Top/) fixes its letter R to the first, and so
do the laws on what the blocks declare.

  `decl_same`: the two are equal: by unfolding the two names; no run is laid out.
  `hW_met`: the ledger's premise hW (`PlanWordOwed`: "the tests on the plan pass at
    the written description made of the written cut, R and the depth 32") AT R := THE FIRST NAME. It
    names no description F: it is a closed sentence.

Limits. One of the two definitions is a twin: which stays is not said here. What `wp_planOk` does
not show, this does not show: at the written description every block's own test and fileOk are the
literal true, and the test of the declared rounds against the plan's is true almost by make
(Johnson/AtFull/ProofPlan/At/No/Decl1Short.lean). Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.WPPlanOk
import Johnson.AtFull.ProofRows.WrittenProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofPlan

open VerifiableInference.PlanWritten (cutFirstFull cutSharedFull cutSecondFull)

/-- **Two names, one term.** -/
theorem decl_same : Johnson.AtFull.ProofRows.declProofFull = P2Law.ProofPlan.declProofFull := rfl

/-- **The ledger's hW, at the ledger's own R.** -/
theorem hW_met :
    (P2Law.ProofPlan.wOf cutFirstFull cutSharedFull cutSecondFull
      Johnson.AtFull.ProofRows.declProofFull 32).planOk = true := by
  rw [decl_same]
  exact P2Law.ProofPlan.wp_planOk

end Johnson.AtFull.ProofPlan

#print axioms Johnson.AtFull.ProofPlan.decl_same
#print axioms Johnson.AtFull.ProofPlan.hW_met
