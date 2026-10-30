-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Base/Meanwhile.lean: plain functions for the two arguments that the step of
Johnson/Desc/First/Base/Base.lean takes:
  spendPlain   the mark that a masking message is spent once: after Blk.spendAsMask
               (OnBytes/Iop/Ground.lean:1279-1282).
  readPlain    the opened columns taken in order, with the book's count: after Blk.readOpened
               (OnBytes/Iop/Ground.lean:1600-1607) over openTreesInto (:1554-1560),
               countOpening (:1530-1540) and takeColumns (:1509-1523).
openOne is the text of openOne in Johnson/Top/H0/Tw/L9/Switch.lean, token for token but for the type
of a refusal (Option here).
THEY ARE PLACEHOLDERS for two other texts of the description: plain functions on data, typed anew.
The description is to have one text on the openings and one on the statement's effects; where these
are laid in as the step's two arguments, each with a theorem or a run that the two agree, this file
goes: no second text is meant to stay. UNTIL THEN A BASE CASE THAT IS RUN WITH THESE TWO DECIDES
THROUGH THEM.
No routine that runs in a context is called: no Blk and no Ctx in any type. FOUR PURE ROUTINES OF
THE HAND-WRITTEN PROGRAM ARE CALLED BY NAME: listOfT, Blk.ownList, Blk.columnsFit, Blk.symbolsOf.
No theorem. Nothing on soundness.

-/
import Johnson.Desc.First.Base.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Base
open OnBytes

/-- [M1] the message is there (OnBytes/Iop/Ground.lean:1280 over :1251); [M2] it is not sampled, has
no answers, is not spent (:1281); it is marked (:1282). -/
def spendPlain : SpendFn := fun S o =>
  match S.oracles[o]? with
  | some x =>
    if !x.sampled && x.shape.answers == 0 && !x.spentAsMask then
      some { S with oracles := S.oracles.modify o fun x => { x with spentAsMask := true } }
    else none
  | none => none

/-- One tree is opened at the list.
 [M3] the tree is in the book: OnBytes/Iop/Ground.lean:1533, :1556.
 [M4] the sampled parts belong to the same groups; a tree with a mask: to one group at most:
      OnBytes/Iop/Ground.lean:1536-1538.
 [M5] a tree that holds a message without a sample has not been opened before (:1539).
 [M6] the tree is not longer than the list's range: OnBytes/Iop/Ground.lean:1557.
 [M7] the next columns are as many as the list, each with the tree's key, at the list's position, of
      the tree's width: OnBytes/Iop/Ground.lean:1519-1520. -/
def openOne (S : Statement) (firstTree : Nat) (pos : Positions) (B0 : TreeBook) (t : Nat)
    (s : TreeBook × List Col × Array (Nat × Array Nat × Array (Array F))) :
    Option (TreeBook × List Col × Array (Nat × Array Nat × Array (Array F))) :=
  match s.1.trees[t]?, B0.trees[t]? with
  | some tree, some tree0 =>
    let groups := tree.parts.toList.filterMap fun o =>
      (S.oracles[o]?).bind fun x => if x.shape.answers == 0 then none else some x.groups
    if !(match groups with
      | [] => true
      | a :: l => l.all (· == a) && (!tree.oneList || decide (a.length ≤ 1))) then none
    else if !(!tree.oneList || tree.lists == 0) then none
    else
      let B := { s.1 with trees := s.1.trees.modify t fun x => { x with lists := x.lists + 1 } }
      if !decide (tree0.shape.logN ≤ pos.logN) then none
      else
        let xs := Blk.ownList tree0 pos
        let W := tree0.shape.mainWidth + tree0.shape.maskWidth
        let got := s.2.1.take xs.size
        if got.length == xs.size && Blk.columnsFit (tree0.number - firstTree) W got xs.toList then
          some (B, s.2.1.drop xs.size, s.2.2.push (t, xs, (got.map fun y => y.2.2.toArray).toArray))
        else none
  | _, _ => none

/-- The messages ids are read at the positions.
 [M8]  each message asked for has a place in the book: OnBytes/Iop/Ground.lean:1603.
 [M9]  the messages asked for are all that their trees hold: OnBytes/Iop/Ground.lean:1605.
 [M10] each message's symbols are found in the opened columns: OnBytes/Iop/Ground.lean:1607. -/
def readPlain : ReadFn := fun S B firstTree cols ids pos =>
  match ids.mapM fun o => B.place[o]? with
  | none => none
  | some places =>
    let trees := listOfT (places.map (·.1)).toList
    if !(trees.all fun t => ((B.trees[t]?).map (·.parts)).getD #[] |>.all ids.contains) then none
    else
      match trees.foldlM (fun s t => openOne S firstTree pos B t s) (B, cols, #[]) with
      | none => none
      | some (B', left, got) =>
        ((ids.zip places).mapM fun y => Blk.symbolsOf S B pos got.toList y.1 y.2).map fun opened =>
          ⟨B', cols.length - left.length, opened⟩

end VerifiableInference.Desc.First.Base
