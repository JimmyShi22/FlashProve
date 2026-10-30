-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookApartWhole.lean: the two lemmas of Honest/BookApart.lean on the
seventh of the book's own tests, at a book that `bookWhole` (Honest/BookWhole.lean) returns. Two
lemmas with their proofs, each one call; no definition.

  `bookWhole_spentApart`   two entries at two positions of the list of spending entries do not share
     a coin
  `bookWhole_spentApart_parts`   the spending entries of two different parts share no coin

By `bookWhole_word` (Honest/AtPureLaw.lean): a book that `bookWhole` returns fails none of its
tests. They are in a file of their own because that lemma's file imports much more than the frame.

Limits.
  * That `bookWhole` returns at any files is a hypothesis here.
  * All limits of Honest/BookApart.lean hold here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.BookApart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)

variable {Xi : Type} {F : FileDescription Xi} {B : ProverCoinCounts}

/-- `ProverCoinCounts.spentApart` at a book that `bookWhole` returns. -/
theorem bookWhole_spentApart {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    (h : bookWhole F p0 p1 p2 M = .ok B) : ∀ (i j : Nat) (e e' : Ahead),
    (B.ahead.filter (·.once))[i]? = some e → (B.ahead.filter (·.once))[j]? = some e' → i ≠ j →
    e.shares e' = false :=
  ProverCoinCounts.spentApart (bookWhole_word h)

/-- `ProverCoinCounts.spentApart_parts` at a book that `bookWhole` returns. -/
theorem bookWhole_spentApart_parts {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    (h : bookWhole F p0 p1 p2 M = .ok B) {a a' : Addr} (hne : a ≠ a') :
    ∀ e ∈ spentE B a, ∀ e' ∈ spentE B a', e.shares e' = false :=
  ProverCoinCounts.spentApart_parts (bookWhole_word h) hne

end ProofFile.Honest

#print axioms ProofFile.Honest.bookWhole_spentApart
#print axioms ProofFile.Honest.bookWhole_spentApart_parts
