-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/GoodKey.lean: FROM THE 32 PIECES OF «key 0» TO ITS WALK: the premise g0 of the
last join (`rows_of_partsL`; Johnson/AtFull/Rows/JoinKey.lean), from one closed fact a piece. A
joining: calls alone; every closed fact is a named premise. A law file; no running text imports it.

Statement.
  `good_key0_of_pieces`: lenK («key 0» has 32 pieces at the written values) · dk (its written rounds
    are 18,852, by two drops: in the form of JoinKey.lean's dk) · pk (each piece, by `pieceD`, along
    `tabK3`) ⊢ Good sW (kW 0).rounds (⟨.once, 0, 0, 0⟩, 0) (key0R cW).
How: `key0R_seq`, `fr_key0Pieces`, `faith_key0Pieces` (CutKey.lean) · `good_of_tableC` (TableC.lean)
· `pieceD_eq`, `length_of_drops` (Slice.lean): as JoinKey.lean's g4 for «proof 0».

Limits. IT PAYS NOTHING: if a premise were false it would be empty. What `Good` says: the routine
returns, ends at counters 0, and its rounds are, by `sameAll` (four of a round's fields: entry,
error, why, scope), the written ones. The door for this one is `rowsWB_of_pieces`
(Johnson/AtFull/Rows/JoinKey.lean). Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.AtK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

/-- **From the pieces to the walk of «key 0».** -/
theorem good_key0_of_pieces (lenK : ((key0Pieces cW).length == 32) = true)
    (dk : (((kW 0).rounds.drop (18851 + 1)).isEmpty && !((kW 0).rounds.drop 18851).isEmpty) = true)
    (pk : ∀ i, i < 32 →
      pieceD sW (kW 0).rounds (tabK3 i) ((key0Pieces cW).getD i (pure ())) = some (tabK3 (i + 1))) :
    Good sW (kW 0).rounds (⟨.once, 0, 0, 0⟩, 0) (key0R cW) := by
  have l : (key0Pieces cW).length = 32 := beq_iff_eq.1 lenK
  have lk : (kW 0).rounds.length = 18851 + 1 := length_of_drops _ _ dk
  rw [key0R_seq]
  exact good_of_tableC (s := sW) (truth := (kW 0).rounds) (sc' := .once) tabK3 (key0Pieces cW)
    (fr_key0Pieces cW) (faith_key0Pieces cW)
    (fun i hi => (pieceD_eq _ _ _ _).symm.trans (pk i (l ▸ hi)))
    (by rw [l, lk]; rfl)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.good_key0_of_pieces
