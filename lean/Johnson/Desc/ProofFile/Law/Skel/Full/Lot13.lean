-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Lot13.lean: lot 13 of the first chain's fifteen lots. The
skeletons of its sub-protocols, as they are written out beside the lot's own module
(`Johnson.AtFull.Lots.k6SkW`, Johnson/AtFull/Desc/Lots/K6Row.lean), are `lot13` of this folder's
file of data (Full/Data.lean): `lot13_is`, a closed fact, decided by Lean's kernel. So a statement
that `lotSk` of the lot is these written rows gives the row that the joining theorem asks of the lot
(`RowAt`, Full/Ask.lean): `row13`. Two statements with proofs.
Limits. Two writers' texts are held against each other; both come off prints of the same code:
neither is an independent witness. `row13` takes that statement as a hypothesis: it is, at most up
to the unfolding of a constant, the conclusion of a theorem beside the lot's own module
(`Johnson.AtFull.Lots.k6_row_scope6`, Johnson/AtFull/Desc/Lots/K6RowOwner.lean), whose hypotheses
are not proved here. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K6Row
import Johnson.Desc.ProofFile.Law.Skel.Full.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem lot13_is :
    (⟨"the output head's own rounds (K6)", false, [],
      [Johnson.AtFull.Lots.k6SkW], [], [], []⟩ : LotW) = lot13 := by
  decide +kernel

theorem row13 {Z : Pub} {G : Ground}
    (h : lotSk G (P4.k6Lot Z) =
      plainK "the output head's own rounds (K6)"
        ([Johnson.AtFull.Lots.k6SkW])) :
    RowAt G (P4.k6Lot Z) lot13 :=
  rowAt_plain h lot13_is

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.lot13_is
#print axioms ProofFile.Sk.Full.row13
