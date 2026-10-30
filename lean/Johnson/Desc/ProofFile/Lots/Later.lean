-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lots/Later.lean: the records for a proof file's two later chains, under the
names that ProofFile/OnlineDescriptionBlocks.lean uses. Both are made elsewhere: the shared chain's in
ProofFile/Lot/K14SeatAtZ.lean, the last chain's in ProofFile/Lot/LastChain.lean.

-/
import Johnson.Desc.ProofFile.Lot.K14SeatAtZ
import Johnson.Desc.ProofFile.Lot.LastChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile

/-- The shared chain's record. -/
def laterShared (Z : Pub) : Option SharedSeat := Desc.K14.sharedSeatAt Z

/-- The last chain's record. -/
def laterSecond (Z : Pub) : Option SecondSeat := P2Third.secondSeat Z

end ProofFile
