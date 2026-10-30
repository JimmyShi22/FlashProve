-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ReadSeat.lean: THE FORM's HALF AT A SWITCH: WHAT RIDES IN THE CARRIED RECORD FOR
THE READING OF THE OLD ROWS: the group's members and the fresh mask's message are, in this order,
ALL the parts of one tree, which is a letter; the tree has been opened at no list; what shares its
leaves passes the description's own test; the messages are there. General in the members: the first
stage's two and a later stage's one are both its values.

What is proved of it: Johnson/Prover/Link/ReadPay.lean.

Main names (namespace Johnson.Prover.Link).
  ReadSeat st book ms id t tr   A RECORD OF PREMISES: six clauses.

Limits. A letter: nothing says here that a record meets it. Beside SeatP
(Johnson/Desc/K12/Law/SwDid.lean), which has the tree's shape and number behind "there is" and
neither its parts, nor its count of lists, nor the parts' lists of groups. "mask" is the library's
name for a message: nothing is said of what a mask does.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.ReadFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes

/-- **What rides for the reading.** ms: the group's members; id: the fresh mask's message; t, tr:
the tree's place in the book, and the tree.
"fresh" is the library's name (SingleRows.fresh, OnBytes/Iop/Fold.lean): the number of a message. No
clause here says how that message's entries are made. -/
structure ReadSeat (st : Statement) (book : TreeBook) (ms : List Nat) (id t : Nat) (tr : Tree) :
    Prop where
  /-- [G8] the tree is in the book -/
  inBook : book.trees[t]? = some tr
  /-- [G13] part p of the tree is the p-th of the members and the fresh message -/
  place : ∀ p (h : p < (ms ++ [id]).length), book.place[(ms ++ [id])[p]]? = some (t, p)
  /-- [G14] the tree holds these and nothing else -/
  parts : tr.parts = (ms ++ [id]).toArray
  /-- [G10] the tree has been opened at no list -/
  once : tr.lists = 0
  /-- [G9] `sharesOk` (Johnson/Prover/Link/ReadFront.lean) at the statement and the tree -/
  shares : sharesOk st tr = true
  /-- [G15] each of these messages has a number below the statement's count of messages -/
  there : ∀ o ∈ ms ++ [id], o < st.oracles.size

end Johnson.Prover.Link
