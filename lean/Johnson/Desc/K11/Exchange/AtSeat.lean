-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/AtSeat.lean: the proofs of `LotBlockIs`, `MergeStatedAtSeat` and
`MergedAtMgSeated` (Johnson/Desc/K11/Exchange/AtSeatStatement.lean), to the letter. Lemmas; none of
the library's goals.

How. The first: by unfolding. The kind's block as it stands alone at a seat is that block with the
test on a mark of failure, the seat's name and the seat's place, without the guard
(`headMergeSeated`, Johnson/Desc/K11/Returns/Seat.lean); none of these three turns its runs of
claims. Then `mergedAtMg` (Johnson/Desc/K11/Exchange/AtMg.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Exchange.AtSeatStatement
import Johnson.Desc.K11.Exchange.AtMg
import Johnson.Desc.K11.Returns.Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open VerifiableInference.Desc.K9 (statesOfLink)
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open Johnson.Desc.First.ForkMerge.Returns (headMergeSeated)

/-- **The lot's block is the kind's block at the lot's numbers.** -/
theorem lotBlockIs : LotBlockIs := by
  intro Z look G h
  unfold K11.blkAt K11.blk
  rw [h, Bool.and_true]

/-- **Such a link states the merge's own run of claims.** -/
theorem mergeStatedAtSeat : MergeStatedAtSeat := by
  intro l P name a h
  unfold statesOfLink
  rw [h, headMergeSeated P name a]
  rfl

/-- **The field forms of the composed meaning at (9, "merged"), from the block's form.** -/
theorem mergedAtMgSeated : MergedAtMgSeated := by
  intro Xi P Tok rows cols nR X D Mg m l Pm name a z b y w hsub hlk hseat h
  exact mergedAtMg Xi P Tok rows cols nR X D Mg m l "the merge" headMergeClaim z b y w hsub hlk
    (mergeStatedAtSeat l Pm name a hseat) (fun _ _ _ => Iff.rfl) h

end Johnson.Desc.First.ForkMerge.Exchange

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Exchange.lotBlockIs
#print axioms Johnson.Desc.First.ForkMerge.Exchange.mergeStatedAtSeat
#print axioms Johnson.Desc.First.ForkMerge.Exchange.mergedAtMgSeated
