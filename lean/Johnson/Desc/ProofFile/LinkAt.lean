-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/LinkAt.lean: THE PROOF FILE's FIRST CHAIN, AND ITS LINK NUMBER m, AS TERMS
OFF THE PUBLIC PART Z ALONE. Definitions with code; nothing is proved here.

  `chainOfSeat Z T`: the first chain as `onlineDescriptionFromPublicPart` and `onlineDescriptionAfterTests` (OnlineDescriptionFromBlockTables.lean) put it together from a
    `PureSeat`: `partsOf`, `PureParts.base`, `chainBy`. IT DOES NOT ASK `faultsAt` AND `lackingAt`,
    which `onlineDescriptionFromPublicPart` asks before: so it can give a chain where the description refuses.
  `emptySecondHashFunction`: a stand-in for the second hash function. The first chain does not read that field of
    the seat (Law/LinkAtLaw.lean: `chainOfSeat_older`).
  `onlineFirstChainAt Z`: the chain at the description's own seat (`pureSeat`, OnlineDescription.lean).
  **`linkAt Z m`**: its link number m, from 0; none where there is no chain or no such link.
What for: two letters of the table of joints' composed meaning (the runs' readers; what follows a
link's batching) are functions of a link's own blocks.
Limits. That these are the seated description's own chain and links: Law/LinkAtLaw.lean. No
soundness is claimed.

-/
import Johnson.Desc.ProofFile.OnlineDescription

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open VerifiableInference.Desc (Chain Link)
open VerifiableInference.Desc.First (S)

/-- The first chain, from the public part and a seat. -/
def chainOfSeat (Z : Pub) (T : PureSeat) : Except String (Chain S Cl) :=
  (partsOf Z T).bind fun P => P.base.bind fun base => chainBy Z base P.frames P.road

/-- A fixed value in the place of the second hash function, where it is not read. -/
def emptySecondHashFunction : SecondHashFunctionArgument := fun _ _ => ByteArray.empty

/-- **The proof file's first chain, off the public part.** -/
def onlineFirstChainAt (Z : Pub) : Except String (Chain S Cl) := chainOfSeat Z (pureSeat emptySecondHashFunction Z)

/-- **Link number m of the proof file's first chain, off the public part.** -/
def linkAt (Z : Pub) (m : Nat) : Option (Link S Cl) :=
  (onlineFirstChainAt Z).toOption.bind fun c => c.links[m]?

end ProofFile
