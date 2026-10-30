-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Lot10.lean: lot 10 of the first chain's fifteen lots. The
skeletons of its sub-protocols, as they are written out beside the lot's own module
(`VerifiableInference.Desc.K13.LotRows.skM3 18 82 true`, Johnson/AtFull/Desc/Lots/K13LotSk.lean),
are `lot10` of this folder's file of data (Full/Data.lean): `lot10_is`, a closed fact, decided by
Lean's kernel. So a statement that `lotSk` of the lot is these written rows gives the row that the
joining theorem asks of the lot (`RowAt`, Full/Ask.lean): `row10`. Two statements with proofs.
Limits. Two writers' texts are held against each other; both come off prints of the same code:
neither is an independent witness. `row10` takes that statement as a hypothesis: it is, at most up
to the unfolding of a constant, the conclusion of a theorem beside the lot's own module
(`VerifiableInference.Desc.K13.LotRows.lot_row`, Johnson/AtFull/Desc/Lots/K13LotRows.lean), whose
hypotheses are not proved here. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K13LotRows
import Johnson.Desc.ProofFile.Law.Skel.Full.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem lot10_is :
    (⟨"K13: the members' batching", false, [],
      [VerifiableInference.Desc.K13.LotRows.skM3 18 82 true], [], [], []⟩ : LotW) = lot10 := by
  decide +kernel

theorem row10 {Z : Pub} {G : Ground}
    (h : lotSk G (VerifiableInference.Desc.K13.lot Z) =
      plainK "K13: the members' batching"
        ([VerifiableInference.Desc.K13.LotRows.skM3 18 82 true])) :
    RowAt G (VerifiableInference.Desc.K13.lot Z) lot10 :=
  rowAt_plain h lot10_is

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.lot10_is
#print axioms ProofFile.Sk.Full.row10
