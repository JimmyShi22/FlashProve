-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/Makers/LaterNames.lean: THE TWO LATER CHAINS' NAMES AND LISTS OF STAND-INS ARE
THE WRITTEN ONES WHEREVER THEIR STRUCTURES ARE MADE. General laws; nothing is evaluated here.

Why. The theorem that the proof file's description returns at the full size
(Johnson/Desc/ProofFile/Law/Skel/Full/) asks of each of the two later chains' structures both that
it is made and that its name and its list of stand-ins (sub-protocols that would run steps of
verify-on-bytes) are the written ones: the name as typed, the list empty. The makers
(`Desc.K14.sharedSeatAt`, Johnson/Desc/ProofFile/Lot/K14SeatAtZ.lean; `P2Third.secondSeat`,
Johnson/Desc/ProofFile/Lot/LastChain.lean) write these two fields as constants. So the second
hypothesis follows from the first.

  `shared_named`: from `onlineSharedChain Z = some A`.
  `second_named`: from `onlineLastChain Z = some B`.

Limits. That either structure is made is a premise. Of their other fields nothing is said.
Nothing on soundness.

-/
import Johnson.Desc.ProofFile.OnlineDescriptionBlocks
import Johnson.Desc.ProofFile.Law.Skel.Full.Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Entry

/-- The shared chain's structure, wherever it is made, bears the written name and no stand-in. -/
theorem shared_named {Z : ProofFile.Pub} {A : ProofFile.SharedSeat} (r₆ : ProofFile.onlineSharedChain Z = some A) :
    ((ProofFile.onlineSharedChain Z).map fun A => (A.lot, A.standIns)) = ProofFile.Sk.Full.sharedW := by
  rw [r₆]
  unfold ProofFile.onlineSharedChain ProofFile.laterShared _root_.Desc.K14.sharedSeatAt at r₆
  split at r₆
  · obtain rfl := Option.some.inj r₆
    rfl
  · exact nomatch r₆

/-- The last chain's structure, wherever it is made, bears the written name and no stand-in. -/
theorem second_named {Z : ProofFile.Pub} {B : ProofFile.SecondSeat} (r₇ : ProofFile.onlineLastChain Z = some B) :
    ((ProofFile.onlineLastChain Z).map fun A => (A.lot, A.standIns)) = ProofFile.Sk.Full.secondW := by
  rw [r₇]
  unfold ProofFile.onlineLastChain ProofFile.laterSecond P2Third.secondSeat at r₇
  split at r₇
  · obtain rfl := Option.some.inj r₇
    rfl
  · exact nomatch r₇

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.shared_named
#print axioms Johnson.AtFull.Entry.second_named
