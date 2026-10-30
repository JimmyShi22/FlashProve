-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Lot01.lean: lot 1 of the first chain's fifteen lots. The
skeletons of its sub-protocols, as they are written out beside the lot's own module
(`Johnson.AtFull.Desc.K1Lot.k1LotW.blocks`, Johnson/AtFull/Desc/Lots/K1/Written.lean), are `lot1` of
this folder's file of data (Full/Data.lean): `lot1_is`, a closed fact, decided by Lean's kernel. So
a statement that `lotSk` of the lot is these written rows gives the row that the joining theorem
asks of the lot (`RowAt`, Full/Ask.lean): `row1`. Two statements with proofs.
Limits. Two writers' texts are held against each other; both come off prints of the same code:
neither is an independent witness. `row1` takes that statement as a hypothesis: it is, at most up to
the unfolding of a constant, the conclusion of a theorem beside the lot's own module
(`Johnson.AtFull.Desc.K1Lot.k1_row_in_scope`, Johnson/AtFull/Desc/Lots/K1/View.lean), whose
hypotheses are not proved here. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K1.Written
import Johnson.Desc.ProofFile.Law.Skel.Full.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem lot1_is :
    (⟨"the commitments (K1)", false, [],
      Johnson.AtFull.Desc.K1Lot.k1LotW.blocks, [], [], []⟩ : LotW) = lot1 := by
  decide +kernel

theorem row1 {Z : Pub} {G : Ground}
    (h : lotSk G (ProofFile.k1Pure Z) =
      plainK "the commitments (K1)"
        (Johnson.AtFull.Desc.K1Lot.k1LotW.blocks)) :
    RowAt G (ProofFile.k1Pure Z) lot1 :=
  rowAt_plain h lot1_is

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.lot1_is
#print axioms ProofFile.Sk.Full.row1
