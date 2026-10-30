-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Lot00.lean: lot 0 of the first chain's fifteen lots. The
skeletons of its sub-protocols, as they are written out beside the lot's own module
(`P1L20.Row.framesRowsW`, Johnson/AtFull/Desc/Lots/FramesRow.lean), are `lot0` of this folder's file
of data (Full/Data.lean): `lot0_is`, a closed fact, decided by Lean's kernel. So a statement that
`lotSk` of the lot is these written rows gives the row that the joining theorem asks of the lot
(`RowAt`, Full/Ask.lean): `row0`. Two statements with proofs.
Limits. Two writers' texts are held against each other; both come off prints of the same code:
neither is an independent witness. `row0` takes that statement as a hypothesis: it is, at most up to
the unfolding of a constant, the conclusion of a theorem beside the lot's own module
(`P1L20.Row.frames_lotSk`, Johnson/AtFull/Desc/Lots/FramesRow.lean), whose hypotheses are not proved
here. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.FramesRow
import Johnson.Desc.ProofFile.Law.Skel.Full.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem lot0_is :
    (⟨"the links' frames", false, [],
      P1L20.Row.framesRowsW, [], [], []⟩ : LotW) = lot0 := by
  decide +kernel

theorem row0 {Z : Pub} {G : Ground}
    (h : lotSk G (ProofFile.framesLot Z) =
      plainK "the links' frames"
        (P1L20.Row.framesRowsW)) :
    RowAt G (ProofFile.framesLot Z) lot0 :=
  rowAt_plain h lot0_is

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.lot0_is
#print axioms ProofFile.Sk.Full.row0
