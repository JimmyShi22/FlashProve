-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/OnlineDescriptionBlocks.lean: which blocks a proof file's description is made of.
Definitions only; no theorem.

A lot (ProofFile/LotCore.lean) is a named table of blocks for some places of the first chain.
`onlineFirstChainBlockTables Z` lists the lots; `onlineSharedChain` and `onlineLastChain` are the records for the two later
chains. ProofFile/OnlineDescriptionFromBlockTables.lean puts the lots' blocks at the plan's places, and returns no description
where a place is left without one.

At every segment the batching comes from K9's lot (`k9Ninth`) as a function of the segment's
gatherer: the claims that it adds are the lists that the segment's earlier blocks state, in the
segment's order, and no table of this file's. A list that the order names and no block states fails
the test on the plan of the segment's first block. Nothing is proved of that here.



-/
import Johnson.Desc.ProofFile.Lots.PureLots
import Johnson.Desc.ProofFile.Lots.Later
import Johnson.Desc.ProofFile.Lot.K3
import Johnson.Desc.ProofFile.Lot.K4
import Johnson.Desc.ProofFile.Lot.K5
import Johnson.Desc.ProofFile.Lot.K8
import Johnson.Desc.ProofFile.Lot.K9
import Johnson.Desc.ProofFile.Lot.K11
import Johnson.Desc.ProofFile.Lot.K12
import Johnson.Desc.ProofFile.Lot.K13At4
import Johnson.Desc.ProofFile.Lot.K13End

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile

/-- The first chain's lots. -/
def onlineFirstChainBlockTables (Z : Pub) : List Lot :=
  [framesLot Z, k1Pure Z, k2Pure Z, K3Lot.lot Z, k4Lot Z, H2K5.lotN Z, P1K8.lot Z,
   k9Ninth Z, K11.lot Z, VerifiableInference.Desc.K12.lot Z,
   VerifiableInference.Desc.K13.lot Z, VerifiableInference.Desc.K13.lot4 Z,
   VerifiableInference.Desc.K13.lotEnd Z] ++ p4Pure Z

/-- The records for the two later chains. -/
def onlineSharedChain (Z : Pub) : Option SharedSeat := laterShared Z
def onlineLastChain (Z : Pub) : Option SecondSeat := laterSecond Z

end ProofFile
