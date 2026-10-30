-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/Symbols.lean: two readings on whose «nothing» the code switch refuses, in
a text of this library's description: what an oracle message holds at the drawn positions, out of
the opened trees' columns (`symbolsAt`); and the symbols of the carried single rows at these
positions, out of the columns of the messages that are folded into them (`rowsSymbols`).
Definitions with code; no monad of the hand-written program.

WHAT `symbolsAt` ASKS, in this order: the message's tree stands in the book · the message stands in
the statement · that tree is among the opened ones · at each drawn position: the tree was opened
there (a tree as long as the positions' range: at the same number in the list; a shorter tree: the
position modulo its length stands in the tree's own list) · and a column was taken there.
WHAT `rowsSymbols` ASKS: as many challenges as the layout has row variables, and no more mask than
main variables · the layout's three lists are as long as its members · at each position: each member
has a column there · its mask symbols have a first row and fit the mask table · the main symbols of
a member that is not kept have a first row and fit the main table · the kept members' main symbols
are as many as the carried rows say · with a fresh mask: its message has a column there, of just
2^h mask symbols.

What is called of the hand-written program: tools that always return: `Blk.columnOf` (a leaf's
words cut into symbols), `foldLow` (a table folded at challenges), and the records' fields.
That each reading agrees with the hand-written program's at all arguments is proved in
Johnson/Desc/Own/SymbolsAgree.lean.
HOW FAR THE TEXT IS ITS OWN. `rowsSymbols`: the tests on the rows' own numbers stand apart, in one
Bool (`shapeFits`); the loops are recursions over lists with a named record of the three tables; the
laying of symbols into a table is a recursion of its own (`layFrom`), its three cases told apart by
the symbols' list and the first row. `symbolsAt`: the reading is short and its asks are plain: the
three look-ups are one match; where a position was opened has a name (`whereOpened`); the words
skipped in a leaf, the comparison of the two lengths and the search in the tree's own list are
written as the hand-written text writes them.
Limits: no law on what the symbols mean.
-/
import OnBytes.Iop.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

/-- An opened tree: its place in the book, the list at which it was opened, the columns there. -/
abbrev Opened : Type := Nat × Array Nat × Array (Array F)

/-- At which number of a tree's own list the i-th drawn position x was opened. same: the tree is as
long as the positions' range. -/
def whereOpened (same : Bool) (own : Array Nat) (length i x : Nat) : Option Nat :=
  if same then some i else own.idxOf? (x % length)

/-- **What the oracle message o, part p.2 of the tree at place p.1, holds at every drawn
position.** -/
def symbolsAt (S : Statement) (B : TreeBook) (pos : Positions) (cols : List Opened) (o : Nat)
    (p : Nat × Nat) : Option (Array Column) :=
  match B.trees[p.1]?, S.oracles[o]?, cols.find? (·.1 == p.1) with
  | some tree, some x, some mine =>
    let mainSkip := (tree.shape.mainSymbols.extract 0 p.2).foldl (· + ·) 0
    let maskSkip := tree.shape.mainWidth + (tree.shape.maskSymbols.extract 0 p.2).foldl (· + ·) 0
    ((List.range pos.all.size).mapM fun i =>
      (whereOpened (tree.shape.logN == pos.logN) mine.2.1 (2 ^ tree.shape.logN) i
          (pos.all.getD i 0)).bind fun here =>
        (mine.2.2[here]?).map (Blk.columnOf x mainSkip maskSkip)).map List.toArray
  | _, _, _ => none

/-- The symbols laid into a table, one row after the other, from row f on. -/
def layFrom (table : Array E) (f : Nat) : List E → Array E
  | [] => table
  | e :: es => layFrom (table.setIfInBounds f e) (f + 1) es

/-- A column's symbols laid into a table at their first row. No symbols: the table as it is. Nothing
if there are symbols and no first row, or if they do not fit. -/
def layRows (table : Array E) (first : Option Nat) (col : Array E) : Option (Array E) :=
  match col.toList, first with
  | [], _ => some table
  | _ :: _, none => none
  | l@(_ :: _), some f => if f + l.length ≤ table.size then some (layFrom table f l) else none

/-- The main table, the mask table and the kept rows, as far as they are laid. -/
structure Tables where
  main : Array E
  mask : Array E
  kept : Array E

/-- One member's column laid in. -/
def layMember (L : GroupLayout) (w : Nat) (col : Column) (t : Tables) : Option Tables :=
  (layRows t.mask (L.maskFirst.getD w none) col.mask).bind fun mask =>
    if L.kept.getD w false then some ⟨t.main, mask, t.kept ++ col.main⟩
    else (layRows t.main (L.mainFirst.getD w none) col.main).map fun main => ⟨main, mask, t.kept⟩

/-- The members' columns at position number i laid in, one member after the other. The list: the
numbers of the members that are still to be laid. -/
def layMembers (L : GroupLayout) (opened : Array (Array Column)) (i : Nat) :
    List Nat → Tables → Option Tables
  | [], t => some t
  | w :: ws, t =>
    ((opened[w]?).bind (·[i]?)).bind fun col =>
      (layMember L w col t).bind (layMembers L opened i ws)

/-- The rows' symbols at position number i, laid behind y: main · kept · old mask · fresh mask. -/
def rowsAt (s : SingleRows) (opened : Array (Array Column)) (y : Array E) (i : Nat) :
    Option (Array E) :=
  let L := s.layout
  (layMembers L opened i (List.range L.members.size)
      ⟨Array.replicate (2 ^ L.k) zeroE, Array.replicate (2 ^ L.h) zeroE, #[]⟩).bind fun t =>
    if t.kept.size != s.keptRows then none
    else
      let low := s.gamma.take L.h
      let y1 := y.push ((foldLow t.main s.gamma).getD 0 zeroE) ++ t.kept
      let y2 := if 1 ≤ s.masks then y1.push ((foldLow t.mask low).getD 0 zeroE) else y1
      if s.masks == 2 then
        ((opened[L.members.size]?).bind (·[i]?)).bind fun fresh =>
          if fresh.mask.size != 2 ^ L.h then none
          else some (y2.push ((foldLow fresh.mask low).getD 0 zeroE))
      else some y2

/-- The tests on the carried rows' own numbers. -/
def shapeFits (s : SingleRows) : Bool :=
  s.gamma.length == s.layout.k && decide (s.layout.h ≤ s.layout.k) &&
    s.layout.kept.size == s.layout.members.size &&
    s.layout.mainFirst.size == s.layout.members.size &&
    s.layout.maskFirst.size == s.layout.members.size

/-- The positions' rows one after the other. -/
def rowsFrom (s : SingleRows) (opened : Array (Array Column)) :
    List Nat → Array E → Option (Array E)
  | [], y => some y
  | i :: is, y => (rowsAt s opened y i).bind (rowsFrom s opened is)

/-- **The symbols of the carried single rows at the first `positions` drawn positions.** Entry
i * s.rows + j: row j at the i-th position. -/
def rowsSymbols (s : SingleRows) (opened : Array (Array Column)) (positions : Nat) :
    Option (Array E) :=
  if shapeFits s then rowsFrom s opened (List.range positions) #[] else none

end VerifiableInference.Desc.Own
