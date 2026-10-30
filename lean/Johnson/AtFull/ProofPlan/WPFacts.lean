-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/WPFacts.lean: CLOSED FACTS ON THE PARTS OF THE WRITTEN DESCRIPTION `WP`
(Johnson/AtFull/ProofPlan/WP.lean). Statements and proofs.

  `rows_fit`: the rounds that the rows of the written cut declare, summed, are as many as the
    written lists have, chain by chain. Why it is worth a line: `piecesBy`
    (Johnson/AtFull/ProofPlan/WrittenDesc.lean) is silent both ways. A sum below the length would
    make `WP.roundsDeclaredByBlocks` a proper front of the rounds: the test of the declared rounds against the plan's
    sees that. A sum above it would leave the pieces in a row equal to the rounds, with the last
    blocks short: that test would pass. No evaluation: from `cut_rounds`
    (Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean) and `decl_lengths`.
  `recs_back`: TWO WRITTEN VALUES HOLD EACH OTHER: the distinct declared rounds (`declRecsFull`) are
    the distinct written rounds (`dryProofRecsFull`, Johnson/G/DryProofLit.lean) turned back by
    `backR` (Johnson/HB/LLHARD/KB8/Written.lean), whole. The two were printed by two programs,
    written apart, off two functions.
  `taken_seen`: the equation of `recs_back` reads the sources at number 130: with "own 0" for each
    source at the one distinct declared round that takes trees over (number 130) the equation fails.
  `lost_value_seen`: `unrunG` is silent at a number without a value. With the last of the distinct
    declared rounds taken away the second chain's list has not 30 rounds.

What `recs_back` does not hold. The runs: one list of runs stands on both sides. Of a written round
`backR` reads its entry, its stored parts and its opened trees alone. Each of the two values' own
files says at which public files it was printed; neither file says that these are the same public
files.

Limits. Facts on written values. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.WP
import Johnson.HB.LLHARD.KB8.Written

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc
open VerifiableInference.PlanWritten (declRecsFull cutFirstFull cutSharedFull cutSecondFull
  cut_rounds)
open Johnson.G (dryProofRecsFull dryProofRunsFull2)
open Johnson.G.Runs (unrunG)
open Johnson.KB8 (backR)

/-- **The rows' numbers of rounds fit the written lists.** -/
theorem rows_fit :
    (cutFirstFull.map (·.2.2.1)).sum = declProofFull.1.length ∧
      (cutSharedFull.map (·.2.2.1)).sum = declProofFull.2.1.length ∧
      (cutSecondFull.map (·.2.2.1)).sum = declProofFull.2.2.length := by
  obtain ⟨a1, a2, a3⟩ := cut_rounds
  obtain ⟨b1, b23⟩ := Prod.mk.inj decl_lengths
  obtain ⟨b2, b3⟩ := Prod.mk.inj b23
  exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm⟩

/-- **Two written values hold each other.** -/
theorem recs_back : declRecsFull = dryProofRecsFull.map backR := by decide +kernel

theorem taken_seen :
    (declRecsFull.modify 130 fun r => { r with opens := r.opens.map fun o => (o.1, .own 0) }) ≠
      dryProofRecsFull.map backR := by
  decide +kernel

theorem lost_value_seen : (unrunG (declRecsFull.take 135) dryProofRunsFull2).length ≠ 30 := by
  decide +kernel

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.rows_fit
#print axioms P2Law.ProofPlan.recs_back
#print axioms P2Law.ProofPlan.taken_seen
#print axioms P2Law.ProofPlan.lost_value_seen
