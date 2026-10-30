-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Lot05.lean: lot 5 of the first chain's fifteen lots. The
skeletons of its sub-protocols, as they are written out beside the lot's own module
(`H2K5.Row.k5SkelW` at the numbers 0 to 11, Johnson/Desc/First/Att/Row/K5RowSkel.lean), are `lot5`
of this folder's file of data (Full/Data.lean): `lot5_is`, a closed fact, decided by Lean's kernel.
So a statement that `lotSk` of the lot is these written rows gives the row that the joining theorem
asks of the lot (`RowAt`, Full/Ask.lean): `row5`. Two statements with proofs.
Limits. Two writers' texts are held against each other; both come off prints of the same code:
neither is an independent witness. `row5` takes that statement as a hypothesis: it is, at most up to
the unfolding of a constant, the conclusion of a theorem beside the lot's own module
(`H2K5.Row.k5_lot_skel_six`, Johnson/Desc/First/Att/Row/K5RowSix.lean), whose hypotheses are not
proved here. Nothing on soundness.

-/
import Johnson.Desc.First.Att.Row.K5RowSkel
import Johnson.Desc.ProofFile.Law.Skel.Full.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem lot5_is :
    (⟨"K5: the attention segments' own rounds", false, [],
      (List.range 12).map H2K5.Row.k5SkelW, [], [], []⟩ : LotW) = lot5 := by
  decide +kernel

theorem row5 {Z : Pub} {G : Ground}
    (h : lotSk G (H2K5.lotN Z) =
      plainK "K5: the attention segments' own rounds"
        ((List.range 12).map H2K5.Row.k5SkelW)) :
    RowAt G (H2K5.lotN Z) lot5 :=
  rowAt_plain h lot5_is

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.lot5_is
#print axioms ProofFile.Sk.Full.row5
