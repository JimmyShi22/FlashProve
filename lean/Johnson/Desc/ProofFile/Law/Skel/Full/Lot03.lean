-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Lot03.lean: lot 3 of the first chain's fifteen lots. The
skeletons of its sub-protocols, as they are written out beside the lot's own module
(`Johnson.AtFull.Lots.K3.k3RowsW`, Johnson/AtFull/Desc/Lots/K3Written.lean), are `lot3` of this
folder's file of data (Full/Data.lean): `lot3_is`, a closed fact, decided by Lean's kernel. So a
statement that the skeletons of the lot's sub-protocols are these written rows gives the row that
the joining theorem asks of the lot (`RowAt`, Full/Ask.lean): `row3`, by the lemma for a lot that
supplies no batching, no `each` and no `tests`. Two statements with proofs.
Limits. Two writers' texts are held against each other; both come off prints of the same code:
neither is an independent witness. `row3` takes that statement as a hypothesis: it is, at most up to
the unfolding of a constant, the conclusion of a theorem beside the lot's own module
(`Johnson.AtFull.Lots.K3.k3_row_scope`, Johnson/AtFull/Desc/Lots/K3RowScope.lean), whose hypotheses
are not proved here. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3Written
import Johnson.Desc.ProofFile.Lot.K3
import Johnson.Desc.ProofFile.Law.Skel.Full.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem lot3_is :
    (⟨"K3: the lookups on the calls and on the digits", false, [],
      Johnson.AtFull.Lots.K3.k3RowsW, [], [], []⟩ : LotW) = lot3 := by
  decide +kernel

theorem row3 {Z : Pub} {G : Ground}
    (h : ((K3Lot.lot Z).blocks G).map skel = Johnson.AtFull.Lots.K3.k3RowsW) :
    RowAt G (K3Lot.lot Z) lot3 := by
  have r := rowAt_of_blocks h (fun _ => rfl) (fun _ => rfl) fun _ => rfl
  exact r.trans lot3_is

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.lot3_is
#print axioms ProofFile.Sk.Full.row3
