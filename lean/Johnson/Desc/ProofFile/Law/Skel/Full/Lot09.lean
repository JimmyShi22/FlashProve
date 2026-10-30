-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Lot09.lean: lot 9 of the first chain's fifteen lots. The
skeletons of its sub-protocols, as they are written out beside the lot's own module
(`H2K12.k12SkelW`, Johnson/Loose/H2K12/K12RowSkelW.lean), are `lot9` of this folder's file of data
(Full/Data.lean): `lot9_is`, a closed fact, decided by Lean's kernel. So a statement that `lotSk` of
the lot is these written rows gives the row that the joining theorem asks of the lot (`RowAt`,
Full/Ask.lean): `row9`. Two statements with proofs.
Limits. Two writers' texts are held against each other; both come off prints of the same code:
neither is an independent witness. `row9` takes that statement as a hypothesis: it is, at most up to
the unfolding of a constant, the conclusion of a theorem beside the lot's own module
(`H2K12.k12_lot_skel`, Johnson/Loose/H2K12/K12RowSkel.lean), whose hypotheses are not proved here.
Nothing on soundness.

-/
import Johnson.Loose.H2K12.K12RowSkelW
import Johnson.Desc.ProofFile.Law.Skel.Full.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem lot9_is :
    (⟨"the proximity test at F:2 (K12)", false, [],
      [H2K12.k12SkelW], [], [], []⟩ : LotW) = lot9 := by
  decide +kernel

theorem row9 {Z : Pub} {G : Ground}
    (h : lotSk G (VerifiableInference.Desc.K12.lot Z) =
      plainK "the proximity test at F:2 (K12)"
        ([H2K12.k12SkelW])) :
    RowAt G (VerifiableInference.Desc.K12.lot Z) lot9 :=
  rowAt_plain h lot9_is

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.lot9_is
#print axioms ProofFile.Sk.Full.row9
