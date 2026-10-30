-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lots/H1.lean: the block at "H:1", the first place of the head's segment.
A definition with code; no theorem.

The place has two steps. The first enters the head's segment: `K2.headFrontQ`
(Johnson/Top/H0/Tw/K2C/Head.lean), taken as a block without a round. The second hears the reply:
`P4.k7Core` (ProofFile/Lot/K6K7.lean). `h1Own` joins them under the second's place.

The chain's guard on the reply (Johnson/Desc/SeatGuard.lean) goes by a block's place, and leaves the
decision at K7's place free, because K7's block is the one that writes the reply. The joined block
is at that place, so the guard would leave its first half free too. The first half is therefore
guarded here, before the join: it is refused if it changes the reply.

-/
import Johnson.Desc.ProofFile.Frames1
import Johnson.Desc.ProofFile.Lot.K6K7
import Johnson.Top.H0.Tw.K2C.Head

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open VerifiableInference.Desc (Block roundlessBlock)
open VerifiableInference.Desc.First

/-- The block at "H:1". The place is stamped on the first half before it is guarded, as
SeatGuard.lean asks; `fun _ => false` guards it whatever its place. -/
def h1Own (G : Ground) : List (Block S Unit) :=
  let l := G.built.size - 1
  let own : Block S Unit := P4.k7Core G
  let front : Block S Unit :=
    { (roundlessBlock "H:1" 1 (some l) 1 (K2.headFrontQ G.W.H.tl) : Block S Unit) with
      place := own.place }
  [(front.guarded sameReply fun _ => false).andThen "H:1" own]

end ProofFile
