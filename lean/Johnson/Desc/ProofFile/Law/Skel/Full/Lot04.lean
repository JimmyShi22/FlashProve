-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Lot04.lean: lot 4 of the first chain's fifteen lots. The
skeletons of its sub-protocols, as they are written out beside the lot's own module
(`Johnson.AtFull.K4Sent.k4SkelFull`, Johnson/AtFull/K4Sent/LotSkel.lean), are `lot4` of this
folder's file of data (Full/Data.lean): `lot4_is`, a closed fact, decided by Lean's kernel. So a
statement that the skeletons of the lot's sub-protocols are these written rows gives the row that
the joining theorem asks of the lot (`RowAt`, Full/Ask.lean): `row4`, by the lemma for a lot that
supplies no batching, no `each` and no `tests`. Two statements with proofs.
Limits. Two writers' texts are held against each other; both come off prints of the same code:
neither is an independent witness. `row4` takes that statement as a hypothesis: it is, at most up to
the unfolding of a constant, the conclusion of a theorem beside the lot's own module
(`Johnson.AtFull.K4Sent.k4_lot_skel`, Johnson/AtFull/K4Sent/LotSkel.lean), whose hypotheses are not
proved here. Nothing on soundness.

-/
import Johnson.AtFull.K4Sent.LotSkel
import Johnson.Desc.ProofFile.Lot.K4
import Johnson.Desc.ProofFile.Law.Skel.Full.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem lot4_is :
    (⟨"K4", false, [], Johnson.AtFull.K4Sent.k4SkelFull, [], [], []⟩ : LotW) = lot4 := by
  decide +kernel

theorem row4 {Z : Pub} {G : Ground}
    (h : ((k4Lot Z).blocks G).map skel = Johnson.AtFull.K4Sent.k4SkelFull) :
    RowAt G (k4Lot Z) lot4 := by
  have r := rowAt_of_blocks h (fun _ => rfl) (fun _ => rfl) fun _ => rfl
  exact r.trans lot4_is

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.lot4_is
#print axioms ProofFile.Sk.Full.row4
