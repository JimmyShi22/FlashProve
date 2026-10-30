-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Lot14.lean: lot 14 of the first chain's fifteen lots. The
skeletons of its sub-protocols, as they are written out beside the lot's own module
(`Johnson.AtFull.Lots.h1Skel 24 true`, Johnson/AtFull/Desc/Lots/H1Row.lean), are `lot14` of this
folder's file of data (Full/Data.lean): `lot14_is`, a closed fact, decided by Lean's kernel. So a
statement that `lotSk` of the lot is these written rows gives the row that the joining theorem asks
of the lot (`RowAt`, Full/Ask.lean): `row14`. Two statements with proofs.
Limits. Two writers' texts are held against each other; both come off prints of the same code:
neither is an independent witness. `row14` takes that statement as a hypothesis: it is, at most up
to the unfolding of a constant, the conclusion of a theorem beside the lot's own module
(`Johnson.AtFull.Lots.h1_row_scope`, Johnson/AtFull/Desc/Lots/H1RowScope.lean), whose hypotheses are
not proved here. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.H1Row
import Johnson.Desc.ProofFile.Law.Skel.Full.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem lot14_is :
    (⟨"the next token (K7), with the step that enters the head's link", false, [],
      [Johnson.AtFull.Lots.h1Skel 24 true], [], [], []⟩ : LotW) = lot14 := by
  decide +kernel

theorem row14 {G : Ground}
    (h : lotSk G (Johnson.AtFull.Lots.h1Lot) =
      plainK "the next token (K7), with the step that enters the head's link"
        ([Johnson.AtFull.Lots.h1Skel 24 true])) :
    RowAt G (Johnson.AtFull.Lots.h1Lot) lot14 :=
  rowAt_plain h lot14_is

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.lot14_is
#print axioms ProofFile.Sk.Full.row14
