-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ReadFront.lean: THE FORM's HALF AT A SWITCH: THE LETTER FOR THE READING OF THE
OLD ROWS (Tw.L9.readOld, Johnson/Top/H0/Tw/L9/Switch.lean: its guards G8 to G16), where the messages
asked for are the parts of ONE tree that is as long as the list's range, no member is kept, and the
carried rows have the old and the fresh mask row. Each clause is one test of the description's own
text, or a number.

What is proved of it: Johnson/Prover/Link/ReadYes.lean. A member:
Johnson/Prover/Link/ReadToy.lean [not in this library].

Main names (namespace Johnson.Prover.Link).
  bookRead   the book with one more list counted at a tree: what the reading leaves.
  sharesOk   the guard G9, as the text tests it, under a name.
  ReadFront i pos t tr   A RECORD OF PREMISES: sixteen clauses; the guards' numbers stand in their
    comments.
  Spec.read_yes   the statement, typed.

Limits. A letter: nothing says here that a record of the link meets it: readFront_sent
(Johnson/Prover/Link/ReadPay.lean) has it from ReadSeat and numbers, which are premises there; who
pays these at the first stage and at a later one is not shown here. A tree that is shorter than the
list's range is not covered.
"mask" is the library's name for a message and for rows: nothing is said of what a mask does.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.H0.Tw.L9.Switch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes
open VerifiableInference.Desc

/-- The book with one more list counted at the tree t. -/
def bookRead (B : TreeBook) (t : Nat) : TreeBook :=
  { B with trees := B.trees.modify t fun x => { x with lists := x.lists + 1 } }

/-- [G9] (the guards' numbers: Johnson/Top/H0/Tw/L9/Switch.lean), as the description's text tests
it, at a tree: the sampled parts belong to the same groups; a tree with a mask: to one group at
most. -/
def sharesOk (S : Statement) (tree : Tree) : Bool :=
  match tree.parts.toList.filterMap fun o =>
      (S.oracles[o]?).bind fun x => if x.shape.answers == 0 then none else some x.groups with
  | [] => true
  | a :: l => l.all (· == a) && (!tree.oneList || decide (a.length ≤ 1))

/-- **What the reading of the old rows asks**, where the messages asked for are the parts of ONE
tree of the list's range, no member is kept, and the rows have the old and the fresh mask row.
"fresh" is the library's name (SingleRows.fresh, OnBytes/Iop/Fold.lean): the number of a message. No
clause here says how that message's entries are made. -/
structure ReadFront (i : Tw.L9.SwIn) (pos : Positions) (t : Nat) (tr : Tree) : Prop where
  /-- the rows: main · old mask · fresh mask; no kept row -/
  masks : i.old.masks = 2
  keptRows : i.old.keptRows = 0
  noKept : ∀ w, i.old.layout.kept.getD w false = false
  /-- [G16] the tests on the rows' own numbers -/
  shape : Own.shapeFits i.old = true
  /-- [G13] part p of the tree t is the p-th message asked for -/
  place : ∀ p (h : p < (singleRowsOracles i.old).size),
    i.book.place[(singleRowsOracles i.old)[p]]? = some (t, p)
  /-- [G8] the tree is in the book -/
  inBook : i.book.trees[t]? = some tr
  /-- [G14] the messages asked for are all that the tree holds -/
  parts : (tr.parts.all (singleRowsOracles i.old).contains) = true
  /-- [G9] `sharesOk` at the statement and the tree -/
  shares : sharesOk i.st tr = true
  /-- [G10] a tree that holds a message without a sample has not been opened before -/
  once : (!tr.oneList || tr.lists == 0) = true
  /-- [G11], and the tree's own list is the list -/
  log : tr.shape.logN = pos.logN
  /-- [G12], and no column is left -/
  dealt : i.opened.length = pos.all.size
  stand : Own.colsStand (tr.number - i.firstTree)
    (tr.shape.mainWidth + tr.shape.maskWidth) i.opened pos.all.toList = true
  /-- [G15] each message asked for is there -/
  there : ∀ p (h : p < (singleRowsOracles i.old).size),
    (i.st.oracles[(singleRowsOracles i.old)[p]]?).isSome = true
  /-- [G16] each member's rows have room in the layout's two tables -/
  roomZ : ∀ w x, w < i.old.layout.members.size →
    i.st.oracles[i.old.layout.members.getD w 0]? = some x → 0 < x.shape.maskRows →
    ∃ f, i.old.layout.maskFirst.getD w none = some f ∧ f + x.shape.maskRows ≤ 2 ^ i.old.layout.h
  roomM : ∀ w x, w < i.old.layout.members.size →
    i.st.oracles[i.old.layout.members.getD w 0]? = some x → 0 < x.shape.mainRows →
    ∃ f, i.old.layout.mainFirst.getD w none = some f ∧ f + x.shape.mainRows ≤ 2 ^ i.old.layout.k
  /-- [G16] the fresh mask's message has 2^h mask rows -/
  fresh : ∀ x, i.st.oracles[i.old.fresh]? = some x → x.shape.maskRows = 2 ^ i.old.layout.h

/-- THE STATEMENT, typed; proved in Johnson/Prover/Link/ReadYes.lean. -/
def Spec.read_yes : Prop :=
  ∀ (i : Tw.L9.SwIn) (pos : Positions) (t : Nat) (tr : Tree), ReadFront i pos t tr →
    ∃ y, Tw.L9.readOld i pos = .ok (bookRead i.book t, [], y) ∧
      y.size = pos.all.size * i.old.rows

end Johnson.Prover.Link
