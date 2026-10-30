-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/Tw/L9/Switch.lean: the code switch at a link's first call (the program's
csSigmaVerify, OnBytes/Iop/Cs.lean:601-603, = switchVerify .. false, :574-598) as a plain function
on data.

A SECOND FORM OF THE CODE SWITCH's TEXT. Another kind's law unfolds this text. The code switch's
own places run the text of Johnson/Top/H0/Tw/K2/, in which the effects on the statement (joinS,
addRowS here) are plain functions of another file, called by name.


  SwIn   what the step reads: the statement, the book of trees and the opened columns that are
         left, BEHIND THE SENDING; the chain's first tree's number; the carried rows (old); the
         plan's target (T); the new group's number; the numbers that the sending returned; the
         plan's entry of the round «LOC»; whether the round closed before owes a count; the round
         «LOC» as the view has it, with how many of its items the sending has taken.
  SwOut  what it writes: the statement (the new group's members and rows: carried :: samples ++
         generators; g's ledger closed; the messages' groups), the book (each opened tree's count
         of lists), the columns that are left, and Switched (g · kept · others · positions): kept
         is the frame's keptBefore; others holds the link's own messages, the fresh mask, what is
         sent at the start.
  switchGuard    the public test in front of the sending.
  switchBehind   the step behind the sending. No Blk, no Ctx.
THE YES-OR-NO TESTS AND THE READINGS ARE THE DESCRIPTION's OWN TEXT, called by name: [G0] targetOk
(K2/Target.lean) · [G12] colsStand · [G25] tensorInOrder · [G28] formFits (Johnson/Desc/Own/
Shapes.lean) · [G15] symbolsAt · [G16] rowsSymbols (Own/Symbols.lean) · [G25]-[G29] placeFits ·
coeffsInside · allZero (Own/Rows.lean) · [G33] rowsMade (K2/RowsMade.lean: eight clauses, then the
maker named there: the program's own switchRows, or an own-text copy of it).
WHAT IS CALLED BY NAME, being pure routines of the program that always return: Positions.ofDraws ·
singleRowsOracles · listOfT · ownList · Row.coefficient.
WHAT IS TYPED ANEW after the program's text: every call that goes through the context: close ·
lastEntry · closePositions · readOpened · openTrees · countOpening · takeColumns · closeLedger ·
join · addRowsOnView · addRow. The list (guard · the program's file:line) stands beneath each
definition.
WHAT IS NOT IN THIS FILE: THE SENDING (sendVerify notices false, Cs.lean:580): it stands between
switchGuard and switchBehind.
The program's notes (Cs.lean:592-596) are left out: no test reads them.
No soundness: definitions with code.

-/
import OnBytes.Iop.Cs
import Johnson.Top.H0.Tw.K2.Target
import Johnson.Top.H0.Tw.K2.RowsMade
import Johnson.Desc.Own.Shapes
import Johnson.Desc.Own.Rows
import Johnson.Desc.Own.Symbols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Tw.L9
open OnBytes
open VerifiableInference.Desc

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
def switchGuard (S : Statement) (old : SingleRows) (T : SwitchTarget) : Bool :=
  _root_.Tw.K2.targetOk S old T

/-- The announcements of the sending. Cs.lean:578-579. -/
def switchNotices (T : SwitchTarget) (others : Array OracleNotice) : Array OracleNotice :=
  #[(⟨T.shape, T.leafClass⟩ : OracleNotice)] ++ T.kept.map (fun k => ⟨k.shape, k.leafClass⟩) ++
    others

/-- Closes the round «LOC» and gives its positions. After Blk.closePositions (Ground.lean:877-881)
over Blk.close (:821-845) and
Blk.lastEntry (:737-740).
 [G1] the plan's next entry has the name «LOC»            Ground.lean:825 (e.name != name)
 [G2] it draws no element from the non-zero elements      Ground.lean:825 (e.drawNZ != nz; nz = 0)
 [G3] the round closed before owes no count               Ground.lean:825 (!c.ch.settled)
 [G4] every item of the message has been taken            Ground.lean:841 (r.vals.isEmpty)
 [G5] as many elements, positions, matrix entries are drawn as the entry says   Ground.lean:841-842
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
 [G10] a tree that holds a message without a sample has not been opened before   Ground.lean:1539
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
        if got.length == xs.size && Own.colsStand (tree0.number - firstTree) W got xs.toList then
          .ok (B, s.2.1.drop xs.size, s.2.2.push (t, xs, (got.map fun y => y.2.2.toArray).toArray))
        else .error "G12: the opened columns do not fit"
  | _, _ => .error "G8: the tree is not in the book"

/-- The old rows are read at the positions. After Blk.readOpened (Ground.lean:1600-1607) and
singleRowsRead (Fold.lean:183-185).
 [G13] each message asked for has a place in the book     Ground.lean:1603
 [G14] the messages asked for are all that their trees hold                Ground.lean:1605
 [G15] each message's symbols are found in the opened columns              Ground.lean:1607
 [G16] the columns fit the layout   Fold.lean:185 (there: singleRowsSymbols gives a value) -/
def readOld (i : SwIn) (pos : Positions) : Except String (TreeBook × List Col × Array E) :=
  let ids := singleRowsOracles i.old
  match ids.mapM fun o => i.book.place[o]? with
  | none => .error "G13: a message has no place in the book"
  | some places =>
    let trees := listOfT (places.map (·.1)).toList
    if !(trees.all fun t => ((i.book.trees[t]?).map (·.parts)).getD #[] |>.all ids.contains) then
      .error "G14: a tree holds a message that is not asked for"
    else
      match trees.foldlM (fun s t => openOne i.st i.firstTree pos i.book t s)
          (i.book, i.opened, #[]) with
      | .error e => .error e
      | .ok (B, left, cols) =>
        match (ids.zip places).mapM fun y => Own.symbolsAt i.st i.book pos cols.toList y.1 y.2 with
        | none => .error "G15: a message's symbols are not among the opened columns"
        | some opened =>
          match Own.rowsSymbols i.old opened pos.all.size with
          | none => .error "G16: the columns do not fit the layout"
          | some y => .ok (B, left, y)

/-- A message joins a group. After Blk.join (Ground.lean:1288-1299).
 [G17] group and message are there                         Ground.lean:1289-1290
 [G18] the message is sampled; the group's test has not begun               Ground.lean:1291
 [G19] its main rows are under the group's code            Ground.lean:1292
 [G20] its mask rows are under the group's mask code       Ground.lean:1293
 [G21] it is no member yet                                 Ground.lean:1294
 [G22] a kept member has main rows                         Ground.lean:1295 -/
def joinS (S : Statement) (g o : Nat) (kept : Bool) : Except String Statement :=
  match S.groups[g]?, S.oracles[o]? with
  | some G, some x =>
    if !(x.sampled && !G.inRun) then .error "G18: not sampled, or the test has begun"
    else if !(x.shape.mainRows == 0 || x.shape.code == G.code) then .error "G19: another main code"
    else if !(x.shape.maskRows == 0 || x.shape.maskCode == G.maskCode) then
      .error "G20: another mask code"
    else if G.members.contains o then .error "G21: a member already"
    else if !(!kept || decide (0 < x.shape.mainRows)) then
      .error "G22: a kept member without main rows"
    else
      let pos := (G.members.filter (· < o)).size
      let S1 := { S with groups := S.groups.modify g fun G => { G with
        members := G.members.insertIdxIfInBounds pos o,
        kept := G.kept.insertIdxIfInBounds pos kept } }
      .ok { S1 with oracles := S1.oracles.modify o fun x => { x with groups := x.groups ++ [g] } }
  | _, _ => .error "G17: the group or the message is not there"

/-- A row is added to a group. After Blk.addRow (Ground.lean:1344-1360), on a view.
 [G23] the group is there                                  Ground.lean:1346
 [G24] its test has not begun; the row is no sample row    Ground.lean:1347
 [G25] each term fits its place                            Ground.lean:1349
 [G26] each single entry fits                              Ground.lean:1350
 [G27] each run fits                                       Ground.lean:1351-1354
 [G28] each form fits                                      Ground.lean:1355-1357
 [G29] THE ROW HAS THE COEFFICIENT 0 ON EVERY PAD (a test on values)        Ground.lean:1358-1359 -/
def addRowS (S : Statement) (g : Nat) (row : Row) : Except String Statement :=
  match S.groups[g]? with
  | none => .error "G23: the group is not there"
  | some G =>
    if !(!G.inRun && row.kind != .sample) then .error "G24: the test has begun, or a sample row"
    else if !(row.terms.all fun t =>
        Own.tensorInOrder t.v && Own.placeFits S G t.oracle t.part t.v.vars 0) then
      .error "G25: a term"
    else if !(row.units.all fun u =>
        Own.placeFits S G u.oracle u.part (S.tableBits u.oracle u.part) u.index) then
      .error "G26: a single entry"
    else if !(row.runs.all fun w =>
        Own.coeffsInside w.coeffs && decide (0 < w.coeffs.size) && decide (1 ≤ w.step) &&
          Own.placeFits S G w.oracle w.part (S.tableBits w.oracle w.part)
            (w.first + w.step * (w.coeffs.size - 1))) then .error "G27: a run"
    else if !(row.forms.all fun f =>
        Own.placeFits S G f.oracle .main (S.tableBits f.oracle .main) 0 &&
          Own.formFits f.c (S.tableBits f.oracle .main)) then .error "G28: a form"
    else if !(G.members.all fun o =>
        ((S.oracles[o]?).map (·.pad)).getD [] |>.all fun p =>
          Own.allZero (row.coefficient o p.1 p.2)) then
      .error "G29: a row reads a pad"
    else .ok { S with groups := S.groups.modify g fun G => { G with rows := G.rows.push row } }

/-- **THE STEP BEHIND THE SENDING.** After switchVerify (Cs.lean:581-598) and switchAdmit
(:539-547).
 [G30] the old main code is in the list of codes   Cs.lean:581 (read in the statement in front of
       the sending; a sending does not turn the codes)
 [G31] g is there (its ledger is closed)   Cs.lean:542 over Ground.lean:1329-1330, :1257-1260
 [G32] the new group is there and its test has not begun   Ground.lean:1364-1365
 [G33] THE ROWS CAN BE MADE (there: switchRows gives a value)   Cs.lean:547 over Ground.lean:1366 -/
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
  let S1 ← if 0 < i.T.shape.maskRows then
      (if out.g < i.st.oracles.size then
        pure { i.st with oracles := i.st.oracles.modify out.g fun x =>
          { x with ledger := x.ledger.map fun l => { l with closed := true } } }
      else throw "G31: g is not there")
    else pure i.st
  let S2 ← joinS S1 i.grp out.g false
  let S3 ← (out.kept.zip i.T.kept).foldlM (fun S p => joinS S i.grp p.1 p.2.keptAgain) S2
  let _ ← match S3.groups[i.grp]? with
    | some G => if G.inRun then throw "G32: the new group's test has begun" else pure ()
    | none => throw "G32: the new group is not there"
  let rows ← match _root_.Tw.K2.rowsMade S3 i.old i.T out.g out.kept out.positions y with
    | some l => pure l
    | none => throw "G33: the rows cannot be made"
  let S4 ← rows.foldlM (fun S r => addRowS S i.grp r) S3
  pure ⟨S4, B, left, out⟩

end Tw.L9
