-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lots/PureLots.lean: five lots of the proof file's list
(ProofFile/OnlineDescriptionBlocks.lean), under four names. Definitions with code; no theorem.

  `framesLot`   the blocks that start and end each segment: ProofFile/Lot/Frames.lean's lot as it is
  `k1Pure`      K1's lot (ProofFile/Lot/K1.lean) with one more block for each segment joined in: a
                block without a round, after the commitment that comes before the smallness test
                (`readsQuietAt`, Lots/Makers.lean)
  `k2Pure`      K2's lot (ProofFile/Lot/K2.lean) as it is
  `p4Pure`      K6's lot (ProofFile/Lot/K6K7.lean), and a lot with the one block at "H:1"

`letters := false` at `k1Pure` and at the lot for "H:1" is written here: it says that these blocks
read nothing of the request out of `Ground`.

-/
import Johnson.Desc.ProofFile.Lots.Makers
import Johnson.Desc.ProofFile.Lots.H1
import Johnson.Desc.ProofFile.Lot.K1
import Johnson.Desc.ProofFile.Lot.K2
import Johnson.Desc.ProofFile.Lot.Frames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open VerifiableInference.Desc (Block roundlessBlock)
open VerifiableInference.Desc.First

/-- The blocks that start and end each segment. -/
def framesLot (Z : Pub) : Lot := P1L20.lot Z

/-- K1's places. Where `readsQuietAt` returns no block, `orLoud` puts one there that refuses. -/
def k1Pure (Z : Pub) : Lot :=
  { VerifiableInference.Desc.K1.lotWith
      (fun (G : Ground) (l : Nat) (X : OnBytes.Model.Stages.LinkH) =>
        let piece : Nat := if X.kind == 0 || X.kind == 1 then 4 else 5
        some (orLoud s!"link {l}: the step after the commitment before the smallness test"
          ⟨1, some l, piece, .K1⟩
          "the step after the commitment that comes before the smallness test"
          (readsQuietAt G l X piece))) Z with
    name := "the commitments (K1)"
    letters := false }

/-- K2's places. -/
def k2Pure (Z : Pub) : Lot := P1K2.lot Z

/-- K6 at "H:4" and K7 at "H:1". -/
def p4Pure (Z : Pub) : List Lot :=
  [P4.k6Lot Z,
   { name := "the next token (K7), with the step that enters the head's link"
     letters := false
     own := h1Own }]

end ProofFile
