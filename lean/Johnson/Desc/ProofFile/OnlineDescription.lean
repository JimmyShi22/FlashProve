-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/OnlineDescription.lean: the proof file's description, `onlineDescription`. It is `onlineDescriptionFromBlockTables`
(OnlineDescriptionFromBlockTables.lean) at the blocks that OnlineDescriptionBlocks.lean lists and at the way of computing the public part that
OnlineDescriptionPublicPart.lean chooses.
What this file imports follows from what the modules listed in OnlineDescriptionBlocks.lean import. Which constants
the term `onlineDescription` reaches is not shown here; a walk over constants shows it.

-/
import Johnson.Desc.ProofFile.OnlineDescriptionFromBlockTables
import Johnson.Desc.ProofFile.OnlineDescriptionPublicPart
import Johnson.Desc.ProofFile.OnlineDescriptionBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile

/-- The blocks that the description is assembled from. `o` stands for the second hash function. -/
def pureSeat (o : SecondHashFunctionArgument) (Z : Pub) : PureSeat :=
  { links := pureRoad.links, lots := onlineFirstChainBlockTables Z, shared := onlineSharedChain Z
    second := onlineLastChain Z, older := o }

/-- **The proof file's description**, from the three public files (policy.txt, layout.txt, KL.bin).
`o` stands for the second hash function: the caller supplies it, and no hash function is named
here in its place. The head of OnlineDescriptionFromBlockTables.lean says when the result is a refusal. -/
def onlineDescription (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) :
    Except String (VerifiableInference.Desc.FileDescription Inst) :=
  onlineDescriptionFromBlockTables o pureRoad onlineFirstChainBlockTables onlineSharedChain onlineLastChain pol lay KL

end ProofFile
