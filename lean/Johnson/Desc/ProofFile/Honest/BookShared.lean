-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookShared.lean: the entries of the book of coins (`ProverCoinCounts`,
Honest/Frame.lean) that can name an owner in the shared chain, as one short list. One executable
definition.

  `sharedAhead`   six of the lists of which the whole book's field `ahead` is made

WHAT IT IS FOR. A test on the book at an owner in the shared chain reads the entries of that owner
alone. The whole book has thousands of entries; these six lists are made of the shared chain's
sub-protocols, its sendings, and one pair of addresses off the second chain. By
`bookWhole_ahead_shared` (Honest/BookSharedLaw.lean) the whole book's entries at such an owner are
this list's.

IT IS A SECOND TEXT OF A PART OF TWO DEFINITIONS, ON PURPOSE: `bookRaw` (Honest/BookWhole.lean) and
`spendingBook` (Honest/BookAll.lean: the line on `f1` and the field `ahead`).
Nine of its lines stand there word for word; `fr` and `om` are written out (there by a
local `under`); the shared chain's own fresh tables are not bound to a name; of the request's own
test's entries only those of Omega's messages that are no mask messages are kept. IF THESE LINES
TURN, THIS FILE TURNS: the lemma's proof then fails.

Limits. No test in this file evaluates it. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)

variable {Xi : Type}

/-- **The entries of the whole book that can name an owner in the shared chain**: six of the lists
of which `bookRaw` (Honest/BookWhole.lean) and `spendingBook` (Honest/BookAll.lean) make the field
`ahead`, in their order there, each by its maker's own term: the shared chain's folds' spending
entries · the split's one coin · the carrying entries of the folded row's test and of Omega's test ·
of the request's own test's: those of Omega's messages that are no mask messages · the carrying
entries of the shared chain's own fresh tables. MADE OF THE SHARED CHAIN's SUB-PROTOCOLS, ITS
SENDINGS, AND ONE PAIR OF
ADDRESSES OFF THE SECOND CHAIN. It rejects where one of these makers does. -/
def sharedAhead (F : FileDescription Xi) (p1 : Johnson.G.ChainSends) : Except String (List Ahead) := do
  let f1 ← foldEntries (planOf F.shared.blocksInOrder) [] p1
  let m1 ← sentIn F.shared.blocksInOrder p1
  let P1 := planOf F.shared.blocksInOrder
  let fr := m1.filter fun m => m.label == "the folded row"
  let om := m1.filter fun m => m.label == "Omega"
  let iF ← due? "the folded row's sending" (fr.head?.map (·.round))
  let cF ← groupCarries P1 iF (fr.filter (!·.fresh) ++ om.filter (·.masks)) (fr.find? (·.fresh))
  let iO ← due? "the folded row's test's last switch"
    ((((seedRounds F.shared.blocksInOrder).zip p1.sends).filter fun x =>
      testOf x.2.label == "the folded row's test").getLast?.map (·.1))
  let cO ← groupCarries P1 iO om none
  let pq ← due? "the second chain's first fold, with a sending behind it"
    (behindFold (planOf F.second.blocksInOrder) 0)
  let tail ← due? "the shared chain's mask code" ((codesUnder p1 "Omega").map (·.2.r))
  pure (f1 ++ (splitEntry F.shared.blocksInOrder p1).toList ++ cF ++ cO ++
    carryPair pq.1 pq.2 (om.filter (!·.masks)) none ++
    (ownFreshIn F.shared.blocksInOrder).map (·.carry tail))

end ProofFile.Honest
