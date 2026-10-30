-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/SeatAtFull.lean: the proofs of `HeadMergePlaceIs`,
`HeadMergeMemberAtFull` and `HeadMergeGoodAtFull` (Honest/K11/Plays/SeatAtFullStatement.lean), to
the letter. Lemmas; none of the library's goals.

How. The two places: by definition. The member: `headMergeAtFull`
(Johnson/Desc/K11/Exchange/AtFull.lean) has member number 346 at the library's name for the place;
`placeOfLot` (Johnson/Desc/K11/Exchange/NumsAtFull.lean) says that it is the block's own; where no
two members stand at one place the first member at a member's place is that member (`find_at`,
Honest/Thread/Rows.lean). `Good`: `headMergeGoodSeated` (SLot.lean of this folder).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.SeatAtFullStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.SLot
import Johnson.Desc.K11.Exchange.AtFull
import Johnson.Desc.K11.Exchange.NumsAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open Johnson.Desc.First.ForkMerge (headClaimMergeKind)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull placeOfLot)

/-- **The two places are one.** -/
theorem headMergePlaceIs : HeadMergePlaceIs := fun _ => rfl

/-- **The first member at the row's place.** -/
theorem headMergeMemberAtFull : HeadMergeMemberAtFull := by
  intro Z D r Zp Np cF x h hn
  obtain ⟨Bs, _, name, hB, _, _, _, _, hf, hl⟩ := headMergeAtFull Z D r Zp Np cF x h
  have hp : headMergePlace (_root_.K11.parOf Zp Bs.G₀) = IM.k11Place :=
    (headMergePlaceIs _).trans (placeOfLot Zp Bs.G₀ hl)
  refine ⟨Bs, name, hB, ?_⟩
  rw [hp]
  exact find_at cF.blocksInOrder 346 _ hn hf

/-- **`Good` at the side that is taken off the first chain's flat list.** -/
theorem headMergeGoodAtFull : HeadMergeGoodAtFull := by
  intro W₀ Rc Xi Tr X Z D r Zp Np cF x Bs fs₀ σ₀ φ Bk ord chain firstTree pre claims weights h hn hB
    hσ hown
  obtain ⟨Bs', name, hB', hm⟩ := headMergeMemberAtFull Z D r Zp Np cF x h hn
  obtain rfl : Bs' = Bs := Except.ok.inj (hB'.symm.trans hB)
  exact headMergeGoodSeated W₀ Rc Xi Tr X cF.blocksInOrder fs₀ σ₀ φ Bk ord chain firstTree pre _ claims
    weights name hσ hm hown

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.headMergePlaceIs
#print axioms ProofFile.Honest.K11.headMergeMemberAtFull
#print axioms ProofFile.Honest.K11.headMergeGoodAtFull
