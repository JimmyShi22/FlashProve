-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Lot08.lean: lot 8 of the first chain's fifteen lots. The
skeletons of its sub-protocols, as they are written out beside the lot's own module
(`Johnson.AtFull.Lots.K11Row.rowW`, Johnson/AtFull/Desc/Lots/K11Row.lean), are `lot8` of this
folder's file of data (Full/Data.lean): `lot8_is`, a closed fact, decided by Lean's kernel. So a
statement that `lotSk` of the lot is these written rows gives the row that the joining theorem asks
of the lot (`RowAt`, Full/Ask.lean): `row8`. Two statements with proofs.
Limits. Two writers' texts are held against each other; both come off prints of the same code:
neither is an independent witness. `row8` takes that statement as a hypothesis: it is, at most up to
the unfolding of a constant, the conclusion of a theorem beside the lot's own module
(`Johnson.AtFull.Lots.K11Row.k11_lotSk_scope`, Johnson/AtFull/Desc/Lots/K11RowScope.lean), whose
hypotheses are not proved here. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K11Row
import Johnson.Desc.ProofFile.Law.Skel.Full.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem lot8_is :
    (⟨"the merge of the weights' claims", false, [],
      Johnson.AtFull.Lots.K11Row.rowW, [], [], []⟩ : LotW) = lot8 := by
  decide +kernel

theorem row8 {Z : Pub} {G : Ground}
    (h : lotSk G (K11.lot Z) =
      plainK "the merge of the weights' claims"
        (Johnson.AtFull.Lots.K11Row.rowW)) :
    RowAt G (K11.lot Z) lot8 :=
  rowAt_plain h lot8_is

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.lot8_is
#print axioms ProofFile.Sk.Full.row8
