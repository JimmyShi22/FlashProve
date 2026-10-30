-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/PaysByCarry.lean: the closing of a segment (K10): what the book lays for each closing to carry is what the part states, by name
and count, in order. From the comparison of triples (PaysByDigest.lean) and the two lemmas on the naming function
(PaysByTriples.lean): no name is evaluated.

  **`closeCarry_by_triples`**   the statement, at the written values

Limits. A fact on written values alone, at the full size; the tie to the description of the head is in
AtFullSide/K10/PaysAtHead.lean.
-/
import AtFullSide.K10.PaysByDigest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open ProofFile.Honest ProofFile.Honest.K10 AtFullSide.K14
open P2Law.ProofPlan (WP)

/-- **What the book lays for each closing to carry is what the part states**, by name and count, in
order. -/
theorem closeCarry_by_triples : (parsW.all fun P =>
    (segmentCarriesAt (planOf WP.first.blocksInOrder) sentFirstW (closeAddr P)).map Ahead.named ==
      closeCarries ⟨P, borneW P⟩) = true := by
  rw [List.all_eq_true]
  intro P hP
  rw [beq_iff_eq, carries_named, closeCarries_named, digest_written, bf_written]
  have hm : (P.link, P.piece) ∈ lpW := by
    rw [← pars_written]
    exact List.mem_map.2 ⟨P, hP, rfl⟩
  exact congrArg (List.map (nameAt (closeAddr P)))
    (beq_iff_eq.1 (List.all_eq_true.1 triples_written _ hm))

end AtFullSide.K10

#print axioms AtFullSide.K10.closeCarry_by_triples
