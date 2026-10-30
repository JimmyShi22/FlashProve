-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/Alone.lean: one test on the book of trees, as a named part of the description.

  aloneIn book o
      THE MESSAGE o HAS A TREE TO ITSELF: the book has a place for o, a tree stands at the number
      that the place names, and that tree's parts are o and nothing else.
How far the text is its own: it is the hand-written program's linAloneInItsTree
(OnBytes/Iop/Lin.lean) WITH ONE TURN OF MEANING: the program asks that the tree has one part; this
asks that the one part is o. It refuses wherever the program's test refuses, and also where the tree
at that number holds one other message: in a book whose two tables disagree. Nothing of the
program's files is called but the records' fields.
What it checks as a statement, that its yes gives the program's yes, and just where the two part, is
stated in theorems beside, in Johnson/Desc/Own/AloneMeans.lean, which no block imports.
No theorem here. Nothing on soundness.

-/
import OnBytes.Iop.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

/-- The message o has a tree to itself. -/
def aloneIn (book : TreeBook) (o : Nat) : Bool :=
  match (book.place[o]?).bind fun p => book.trees[p.1]? with
  | some t => t.parts == #[o]
  | none => false

end VerifiableInference.Desc.Own
