-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Lot11.lean: lot 11 of the first chain's fifteen lots. The
skeletons of its sub-protocols, as they are written out beside the lot's own module
(`VerifiableInference.Desc.K13.LotRows.skM4Full`, Johnson/AtFull/Desc/Lots/K13LotRows.lean), are
`lot11` of this folder's file of data (Full/Data.lean): `lot11_is`, a closed fact, decided by Lean's
kernel. So a statement that `lotSk` of the lot is these written rows gives the row that the joining
theorem asks of the lot (`RowAt`, Full/Ask.lean): `row11`. Two statements with proofs.
Limits. Two writers' texts are held against each other; both come off prints of the same code:
neither is an independent witness. `row11` takes that statement as a hypothesis: it is, at most up
to the unfolding of a constant, the conclusion of a theorem beside the lot's own module
(`VerifiableInference.Desc.K13.LotRows.lot4_row`, Johnson/AtFull/Desc/Lots/K13LotRows.lean), whose
hypotheses are not proved here. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K13LotRows
import Johnson.Desc.ProofFile.Law.Skel.Full.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem lot11_is :
    (⟨"K1 and K13: W's commitment, the request's own group and the row (Eval)", false, [],
      [VerifiableInference.Desc.K13.LotRows.skM4Full], [], [], []⟩ : LotW) = lot11 := by
  decide +kernel

theorem row11 {Z : Pub} {G : Ground}
    (h : lotSk G (VerifiableInference.Desc.K13.lot4 Z) =
      plainK "K1 and K13: W's commitment, the request's own group and the row (Eval)"
        ([VerifiableInference.Desc.K13.LotRows.skM4Full])) :
    RowAt G (VerifiableInference.Desc.K13.lot4 Z) lot11 :=
  rowAt_plain h lot11_is

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.lot11_is
#print axioms ProofFile.Sk.Full.row11
