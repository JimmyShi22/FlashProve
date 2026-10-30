-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/Tw/K2/Switch.lean: the kind «the code switch»: the switch at a link's first call (the
program's csSigmaVerify, OnBytes/Iop/Cs.lean:601-603,
= switchVerify .. false, :574-598) as a plain function on data. The effects on the statement (a
message joins a group; rows are added; a ledger is shut) are the plain ground's functions
joinP | addRowsP | closeLedgerP, called by name.

  SwIn   what the step reads: the statement, the book of trees and the opened columns that are left,
  BEHIND THE SENDING; the chain's
         first tree's number; the carried rows (old); the plan's target (T); the new group's number;
         the numbers that the sending
         returned; the plan's entry of the round «LOC»; whether the round closed before owes a
         count; the round «LOC» as the view has it,
         with how many of its items the sending has taken.
  SwOut  what it writes: the statement (the new group's members and rows: carried :: samples ++
  generators; g's ledger closed; the
         messages' groups), the book (each opened tree's count of lists), the columns that are left,
         and Switched (g · kept · others ·
         positions): kept is the frame's keptBefore; others holds the link's own messages, the fresh
         mask, what is sent at the start.
  switchGuard    the public test in front of the sending.
  switchBehind   the step behind the sending. No Blk, no Ctx.
THE PUBLIC TEST [G0] IS THE KIND's OWN TEXT (K2/Target.lean: targetOk); [G12], THAT THE OPENED
COLUMNS FIT, IS Johnson/Desc/Own/Shapes.lean's colsStand.
WHAT IS CALLED BY NAME, being pure routines of the program: Positions.ofDraws · singleRowsOracles ·
listOfT · ownList ·
THE MAKER OF THE NEW GROUP's ROWS IS THE DESCRIPTION's OWN TEXT TOO:
Johnson/Desc/Own/SwitchRows.lean's swRows (the program's switchRows taken over token for token; no
refusal hangs on it: [G33] is asked in front). THE READING OF THE OPENED COLUMNS [G15] [G16]:
Johnson/Desc/Own/Symbols.lean's symbolsAt · rowsSymbols. OF THE PLAIN GROUND, BY NAME: closeLedgerP
· joinP · addRowsP (with rowsL · addRowP and the lists of clauses, for a refusal's word).
WHAT IS TYPED ANEW after the program's text: every call that goes through the context: close ·
lastEntry · closePositions · readOpened ·
openTrees · countOpening · takeColumns. The list (guard · the program's file:line) stands beneath
each definition.
WHAT IS NOT IN THIS FILE: THE SENDING (sendVerify notices false, Cs.lean:580): it stands between
switchGuard and switchBehind.
The program's notes (Cs.lean:592-596) are left out: no test reads them.
No soundness: definitions with code.
-/
import OnBytes.Iop.Cs
import Johnson.Desc.First.Base.Ground
import Johnson.Top.H0.Tw.K2.Target
import Johnson.Top.H0.Tw.K2.RowsCan
import Johnson.Desc.Own.Shapes
import Johnson.Desc.Own.Symbols
import Johnson.Desc.Own.SwitchRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Tw.K2
open OnBytes
open VerifiableInference.Desc.Ground (Clauses ok joinL joinP rowL addRowP rowsL addRowsP
    closeLedgerL closeLedgerP)

abbrev Col : Type := Nat × Nat × List UInt64

structure SwIn where
  st : Statement
  book : TreeBook
  firstTree : Nat
  opened : List Col
  old : SingleRows
  T : SwitchTarget
  grp : Nat
  ids : Array Nat
  /-- the plan's entry of the round that the step closes -/
  entry : Fmt.Entry
  /-- the round closed before owes no count of rows (Chan.settled) -/
  settled : Bool
  /-- what the round draws -/
  drawn : Fmt.Drawn
  /-- the items of the round's message that the sending has left untaken -/
  itemsLeft : Nat

structure SwOut where
  st : Statement
  book : TreeBook
  opened : List Col
  out : Switched

/-- The public test in front of the sending. [G0] Cs.lean:577. -/
def switchGuard (S : Statement) (old : SingleRows) (T : SwitchTarget) : Bool := targetOk S old T

/-- The announcements of the sending. Cs.lean:578-579. -/
def switchNotices (T : SwitchTarget) (others : Array OracleNotice) : Array OracleNotice :=
  #[(⟨T.shape, T.leafClass⟩ : OracleNotice)] ++ T.kept.map (fun k =>
      ⟨k.shape, k.leafClass⟩) ++ others

/-- Closes the round «LOC» and gives its positions. After Blk.closePositions (Ground.lean:877-881)
over Blk.close (:821-845) and
Blk.lastEntry (:737-740).
 [G1] the plan's next entry has the name «LOC»            Ground.lean:825 (e.name != name)
 [G2] it draws no element from the non-zero elements      Ground.lean:825 (e.drawNZ != nz; nz = 0)
 [G3] the round closed before owes no count               Ground.lean:825 (!c.ch.settled)
 [G4] every item of the message has been taken            Ground.lean:841 (r.vals.isEmpty)
 [G5] as many elements, positions, matrix entries are drawn as the entry says     
 Ground.lean:841-842
 [G6] the entry's range is the old main code's, and it draws a position            Ground.lean:880
 [G7] no element is drawn behind the positions            Cs.lean:583-587 (false, []) -/
def locPositions (i : SwIn) (logN : Nat) : Except String Positions :=
  if i.entry.name != "LOC" then .error "G1: the plan's entry is not LOC"
  else if i.entry.drawNZ != 0 then .error "G2: the entry draws non-zero elements"
  else if !i.settled then .error "G3: the round before owes a count of rows"
  else if i.itemsLeft != 0 then .error "G4: an item of the message is left"
  else if !(i.drawn.elems.length == i.entry.drawE && i.drawn.poss.length == i.entry.poss &&
      i.drawn.trits.length == i.entry.trits) then
          .error "G5: the numbers of draws are not the entry's"
  else if !(i.entry.logN == logN && decide (0 < i.entry.poss)) then
      .error "G6: the entry's range or number of positions"
  else if !i.drawn.elems.isEmpty then .error "G7: an element is drawn behind the positions"
  else .ok (Positions.ofDraws logN i.drawn.poss)

/-- One tree is opened at the list. After Blk.countOpening (Ground.lean:1530-1540), the loop of
openTreesInto (:1554-1560) and
Blk.takeColumns (:1509-1523).
 [G8]  the tree is in the book                            Ground.lean:1533, :1556
 [G9]  the sampled parts belong to the same groups; a tree with a mask: to one group at most       
 Ground.lean:1536-1538
 [G10] a tree that holds a message without a sample has not been opened before                     
 Ground.lean:1539
 [G11] the tree is not longer than the list's range       Ground.lean:1557
 [G12] the next columns are as many as the list, each with the tree's key, at the list's position,
 of the tree's width   Ground.lean:1519-1520 -/
def openOne (S : Statement) (firstTree : Nat) (pos : Positions) (B0 : TreeBook) (t : Nat)
    (s : TreeBook × List Col × Array (Nat × Array Nat × Array (Array F))) :
    Except String (TreeBook × List Col × Array (Nat × Array Nat × Array (Array F))) :=
  match s.1.trees[t]?, B0.trees[t]? with
  | some tree, some tree0 =>
    let groups := tree.parts.toList.filterMap fun o =>
      (S.oracles[o]?).bind fun x => if x.shape.answers == 0 then none else some x.groups
    if !(match groups with
      | [] => true
      | a :: l => l.all (· == a) && (!tree.oneList || decide (a.length ≤ 1))) then
          .error "G9: what shares a leaf"
    else if !(!tree.oneList || tree.lists == 0) then
        .error "G10: a tree with a mask is opened twice"
    else
      let B := { s.1 with trees := s.1.trees.modify t fun x => { x with lists := x.lists + 1 } }
      if !decide (tree0.shape.logN ≤ pos.logN) then .error "G11: the tree is longer than the range"
      else
        let xs := Blk.ownList tree0 pos
        let W := tree0.shape.mainWidth + tree0.shape.maskWidth
        let got := s.2.1.take xs.size
        if got.length == xs.size && VerifiableInference.Desc.Own.colsStand (tree0.number -
            firstTree) W got xs.toList then
          .ok (B, s.2.1.drop xs.size, s.2.2.push (t, xs, (got.map fun y => y.2.2.toArray).toArray))
        else .error "G12: the opened columns do not fit"
  | _, _ => .error "G8: the tree is not in the book"

/-- The old rows are read at the positions. After Blk.readOpened (Ground.lean:1600-1607) and
singleRowsRead (Fold.lean:183-185).
 [G13] each message asked for has a place in the book     Ground.lean:1603
 [G14] the messages asked for are all that their trees hold                Ground.lean:1605
 [G15] each message's symbols are found in the opened columns              Ground.lean:1607
 [G16] the columns fit the layout                          Fold.lean:185 (there: singleRowsSymbols
 gives a value; here: Johnson/Desc/Own/Symbols.lean's rowsSymbols) -/
def readOld (i : SwIn) (pos : Positions) : Except String (TreeBook × List Col × Array E) :=
  let ids := singleRowsOracles i.old
  match ids.mapM fun o => i.book.place[o]? with
  | none => .error "G13: a message has no place in the book"
  | some places =>
    let trees := listOfT (places.map (·.1)).toList
    if !(trees.all fun t => ((i.book.trees[t]?).map (·.parts)).getD #[] |>.all ids.contains) then
      .error "G14: a tree holds a message that is not asked for"
    else
      match trees.foldlM (fun s t =>
          openOne i.st i.firstTree pos i.book t s) (i.book, i.opened, #[]) with
      | .error e => .error e
      | .ok (B, left, cols) =>
        match (ids.zip places).mapM fun y =>
            VerifiableInference.Desc.Own.symbolsAt i.st i.book pos cols.toList y.1 y.2 with
        | none => .error "G15: a message's symbols are not among the opened columns"
        | some opened =>
          match VerifiableInference.Desc.Own.rowsSymbols i.old opened pos.all.size with
          | none => .error "G16: the columns do not fit the layout"
          | some y => .ok (B, left, y)

/-! ### The effects on the statement: the plain ground's functions, called by name. An adapter each:
a statement is laid into the plain ground's state record and read back; where the
function refuses, the word of the refusal is the first of ITS OWN named clauses that is false. IN
THIS FILE «Ground.lean:N» ALWAYS MEANS THE PROGRAM's OnBytes/Iop/Ground.lean, never the plain
ground's file. -/

/-- A statement as the plain ground's state: these four effects read and write the statement alone.
-/
def dOf (S : Statement) : Desc.Plain.DState Unit := ⟨S, {}, 0, [], ()⟩

/-- The name of the first clause that is false. -/
def firstFalse (l : Clauses) : String := ((l.find? (!·.2)).map (·.1)).getD "no clause is false"

/-- [G31] g's ledger is shut: closeLedgerP (its one clause, after the program's
Iop/Ground.lean:1258).                 Cs.lean:542 -/
def closeLedgerG (S : Statement) (o : Nat) : Except String Statement :=
  match closeLedgerP (dOf S) o with
  | some d => .ok d.st
  | none => .error ("G31: L22: " ++ firstFalse (closeLedgerL S o))

/-- [G17-G22] a message joins a group: joinP (its eight clauses, after the program's
Iop/Ground.lean:1289-1295).       Cs.lean:543, :545; Req.lean:303 -/
def joinG (S : Statement) (g o : Nat) (kept : Bool) : Except String Statement :=
  match joinP (dOf S) g o kept with
  | some d => .ok d.st
  | none => .error ("G17-G22: L22: " ++ firstFalse (joinL S g o kept))

/-- Which clause refuses which row: for the refusal's word alone. -/
def whyRow (g : Nat) : List Row → Desc.Plain.DState Unit → String
  | [], _ => "no row is refused"
  | r :: l, d =>
    match addRowP d g r with
    | some d' => whyRow g l d'
    | none => firstFalse (rowL d.st g r)

/-- [G32 · G23-G29] the rows are added, in order: addRowsP (its two clauses, after the program's
Iop/Ground.lean:1364-1365; a row's eight, after :1346-1359).      Cs.lean:547 -/
def addRowsG (S : Statement) (g : Nat) (rows : List Row) : Except String Statement :=
  match addRowsP (dOf S) g rows with
  | some d => .ok d.st
  | none => .error (if ok (rowsL S g) then "G23-G29: L22: " ++ whyRow g rows (dOf S) else
      "G32: L22: " ++ firstFalse (rowsL S g))

/-- **THE STEP BEHIND THE SENDING.** After switchVerify (Cs.lean:581-598) and switchAdmit
(:539-547).
 [G30] the old main code is in the list of codes           Cs.lean:581 (read in the statement in
 front of the sending; a sending does not turn the codes)
 [G31] g is there (its ledger is closed)                   Cs.lean:542 over Ground.lean:1329-1330,
 :1257-1260
 [G32] the new group is there and its test has not begun   Ground.lean:1364-1365
 [G33] THE ROWS CAN BE MADE (K2/RowsCan.lean's eight clauses, asked in front of the maker swRows; in
 the program: switchRows gives a value)     Cs.lean:547 over Ground.lean:1366 -/
def switchBehind (i : SwIn) : Except String SwOut := do
  let code ← match i.st.codes.base[i.old.code]? with
    | some c => pure c
    | none => throw "G30: the old main code is not there"
  let pos ← locPositions i code.logN
  let out : Switched :=
    { g := i.ids.getD 0 noId, kept := i.ids.extract 1 (1 + i.T.kept.size),
      others := i.ids.extract (1 + i.T.kept.size) i.ids.size, positions := pos }
  let (B, left, y) ← readOld i pos
  -- switchAdmit
  let S1 ← if 0 < i.T.shape.maskRows then closeLedgerG i.st out.g else pure i.st
  let S2 ← joinG S1 i.grp out.g false
  let S3 ← (out.kept.zip i.T.kept).foldlM (fun S p => joinG S i.grp p.1 p.2.keptAgain) S2
  if !ok (rowsL S3 i.grp) then throw ("G32: L22: " ++ firstFalse (rowsL S3 i.grp))
  if !rowsCan S3 i.old i.T out.kept out.positions y then
      throw ("G33: the rows cannot be made: it is not so that " ++ rowsWhy S3 i.old i.T out.kept
          out.positions y)
  -- behind [G33] the maker returns (K2/RowsMadeAgree.lean: rowsCan_someOwn): the empty list is
  -- never taken
  let rows :=
      (VerifiableInference.Desc.Own.swRows S3 i.old i.T out.g out.kept out.positions y).getD []
  let S4 ← addRowsG S3 i.grp rows
  pure ⟨S4, B, left, out⟩

end Tw.K2
