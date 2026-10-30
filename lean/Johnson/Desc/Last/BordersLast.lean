-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Last/BordersLast.lean: THE TABLE OF JOINTS OF THE PROOF FILE's LAST CHAIN (the third: each request's own): what the record that each
block hands to the next MEANS, in the form of the first chain's table (Johnson/Desc/First/Borders.lean) and the shared chain's
(Johnson/Desc/Shared/BordersShared.lean). Definitions with code, tests on the table by evaluation. No theorem on the protocol. The book-keeping is a Bool; no pin is context at row 0.
That the index and rows 0, 1, 3 render the last chain's text is by report, not shown here; for row 0's law and for row 2 there is no report.

THE CHAIN, in words (read off other files' text of it: K14's second part, the taken trees' sources, K12 at the request's own group, the chain's end). Its
first record is made of the first chain's last record (its statement WHOLE, its book, its roots, of its one pending row the weights g) and of the shared
chain's end (statement and book, read for Omega alone; the shared point psi_sh; Omega's number). Block 0 takes Omega over into the request's own group (W's
group, made at the first chain's end) and lays the row (Dot) behind the row (Eval), which lies there since W's sending. Block 1 holds the declared sources of
the trees that this chain opens and did not send against the book. Block 2 is the proximity test on the own group: three members (W, the index masks'
message, Omega), two open rows ((Eval), (Dot)) beside the members' sample rows. Block 3 asks that no group is left untested.

WHAT IS MEANT AND NO CLAUSE OF THE TEXT ASKS (so it belongs in the promise, or is another chain's): that (Eval) lies on the own group (the first chain's promise: evalLaid) · that g, the one pending
row's weights, belongs to the claim off which (Eval) was laid (by the make of the first chain's record's reader of its pending rows) · until its next turn: that Omega's shape in the shared statement is the plan's,
off which (Dot)'s layout is made (A CLAUSE OF shape 0) · who beside W is a member of the own group (the first chain's promise) · Omega's seat in its tree.

WHAT COMES IN. The shared chain's table leaves six items open (its endS): no mark of the first chain, the index masks' pin, W's pin, (Eval), (Dot), Omega's
pin. "NO MARK" IS NO ITEM HERE: the last chain has a first record only where the first chain stands at its end, whose first clause is "no mark": it is paid at
the joint, by the start's own yes, and stands in the promise. THE START THAT IS MEANT IS THE DESCRIPTION's FIELD start₃ AS THE FILE's FRAME SEATS IT ("refuse unless the first chain stands at its end", then the
last chain's files' own start): THAT START BY ITSELF READS NO MARK: laid bare it does not pay this. THE OTHER FIVE ARE startLast, AS THE SAME TERMS: they read what was handed to the chain (the
first chain's last record, the shared chain's last record), not this chain's own record.

THE ROWS.
  0 (K14's second part): closes (Eval) and (Dot), opens rows: "every open row of the own group, as it lies in the record at the border at which the item is
    read, holds of the witness's messages". No chance, no extractor: (Eval) lies among these rows by the first chain's promise (evalLaid), (Dot) is laid by
    this block. NO PIN IS CONTEXT: all three sentences are "this row holds of the witness's messages": no word is decoded. WHAT THE LAW SPENDS BESIDE IS PUBLIC, SO IT
    STANDS IN THE PROMISE (shape): the row (Eval) in this record's own group is the row that ev's term reads off the first chain's record; (Dot) as the
    block lays it is dot's row, at the first chain's g and the shared chain's psi_sh; the messages' numbers in both rows go to one number of the witness under
    this record's book and under the two earlier records'.
  1 (the taken trees' sources): no item. IT PAYS A CLAUSE OF THE PROMISE IN FRONT OF BLOCK 2: the trees that block 2's declared rounds open and this chain did not
    send are just (AS SETS OF PAIRS: chain, number) the book's trees of the own group's members and of the mask: OMEGA's UNDER CHAIN 1, EVERY OTHER MEMBER's AND THE MASK's UNDER CHAIN 0 (
    the block does not know who sent a tree: that the others were sent by the first chain is the first chain's promise). A tree's number does not name a tree across chains.
  2 (K12 at the own group): CLOSES ALL THAT IS OPEN: rows and the three pins. ITS EXTRACTOR LAYS W's, THE INDEX MASKS' AND OMEGA's COMPONENTS OF THE WITNESS:
    no block in front of it lays them [the shared chain's rows: a test, laidOnce; the first chain's: by reading: a test is owed]. THE TEST DECODES AT ITS OWN
    RECORD; the three pins are stated at the records that were handed: that this record's sample, seat and tree's number of each member are those records' IS A
    CLAUSE OF shape 2, BY NAME: else the row delivers a pin that is not the item. OMEGA's COMPONENT IS LAID IN EACH SLOT's OWN LAST TEST: a pin is functional: whatever meets
    pinO names what Omega's word decodes to with Omega's sample in the shared record: one for all slots.
  3 (the end): nothing. BEHIND IT NOTHING IS OPEN: the relation at the file's last border is "true".

1 THE INDEX: lastPlaces.  2 THE ITEMS: ItemL.  3 THE ROWS: RowOfL, rowL.  4 THE OPEN SETS AND THE TESTS ON THE TABLE: startLast, stepOpenL, openSetsL,
readsOpenL, freshOutsL, endEmptyL, meetsShared, ItemL.reads, laysOfL, laysClearL, laysAllL, laidOnce.  5 THE MEANING: MeaningL, ItemL.holds.  6 THE PROMISE:
PromMeaningL, onL.
The field `whose` of a row names the block whose text the row renders; it is read by no
theorem.

Limits. (1) Read off the texts named: A READING, NOT A THEOREM. (2) rows and the book-keeping are letters. (3) The tests on the table test
the table's own word. (4) That the real last chain's flat list has these places is a test (Shared.placesFitS at lastPlaces): to be run. (5) The test is one
block here: if its files cut it finer, the rows inside are their own. (6) That no block of this chain can defer a failure: its record has no field for a mark, and
the record that is born and dies inside block 2 has none either (statement, book, roots, the group's number, what passes from part to part, the mask's number) [by
reading K14's second part, the sources' block, the end, K12's seat at the own group and its record's type]. THE SEAT's WAY OUT LAYS BACK THE STATEMENT, THE BOOK AND THE ROOTS
AND ASKS NOTHING OF "what passes from part to part": that it is "nothing" behind the base case is a theorem of K12's files on their own text (as reported, not shown here: a law of K12's files rather than a
test). (7) The shape in which the row
(Dot) is split is refused by the chain's own test on the plan: not provided for. (8) The first fold's mask, where it went out ahead, has no component
of the witness (as in the first chain's table).

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Shared.BordersShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc VerifiableInference.Desc.Shared

/-! ## 1 The index -/

/-- The places of the last chain's flat list. -/
def lastPlaces : List Place :=
  [⟨3, none, 0, .K14⟩, ⟨3, none, 1, .frame⟩, ⟨3, none, 2, .K12⟩, ⟨3, none, 3, .frame⟩]

/-! ## 2 The items -/

/-- **An item**: a named claim on the witness. The first five are the shared chain's table's own items and Omega's pin, AS THEY COME OVER THE JOINT. -/
inductive ItemL where
  /-- The row (Eval) on W holds (the shared chain's ev; the first chain's wrow) -/
  | ev
  /-- The row (Dot): W at psi_sh is < g, Omega > (the shared chain's dot) -/
  | dot
  /-- W's pin (the first chain's pinV) -/
  | pinV
  /-- The index masks' pin (the first chain's pinI) -/
  | pinI
  /-- Omega's pin, at the shared chain's last record (the shared chain's pin .oOmega) -/
  | pinO
  /-- Every open row of the request's own group, AS IT LIES IN THIS CHAIN's RECORD AT THE BORDER AT WHICH THE ITEM IS READ, holds of the witness's messages.
  The test closes it: so it owes the rows AT THE RECORD IN FRONT OF ITS BLOCK: the rows that its run takes in. -/
  | rows
  deriving DecidableEq, Repr

/-- The item of the shared chain's table that an item of this table's start is. -/
def ItemL.ofShared : ItemL → Option ItemS
  | .ev => some .ev
  | .dot => some .dot
  | .pinV => some .pinV
  | .pinI => some .pinI
  | .pinO => some (.pin .oOmega)
  | .rows => none

/-! ## 3 The rows -/

/-- **A block's row.** -/
structure RowOfL where
  ins : List ItemL := []
  outs : List ItemL := []
  ctx : List ItemL := []
  /-- its extractor lays components of the witness (else it is the identity) -/
  lays : Bool := false
  known : Bool := true
  whose : String := "the frame's"
  deriving Repr

/-- **The table**, by the block's number (Place.piece). -/
def rowL (p : Place) : RowOfL :=
  match p.piece with
  | 0 =>
    { ins := [.ev, .dot], outs := [.rows]
      whose := "K14's second part" }
  | 1 => { whose := "the taken trees' sources" }
  | 2 =>
    { ins := [.rows, .pinV, .pinI, .pinO], lays := true
      whose := "K12 at the request's own group" }
  | 3 => { whose := "the chain's end" }
  | _ => { known := false }

/-! ## 4 The open sets, and tests on the table -/

/-- What is open at the chain's start. -/
def startLast : List ItemL := [.pinI, .pinV, .ev, .dot, .pinO]

/-- The open set behind a block. -/
def stepOpenL (O : List ItemL) (r : RowOfL) : List ItemL :=
  let rest := O.filter fun i => !r.ins.contains i
  rest ++ r.outs.filter fun i => !rest.contains i

/-- The open sets at all borders: one more than there are blocks. -/
def openSetsL : List Place → List ItemL → List (List ItemL)
  | [], O => [O]
  | p :: ps, O => O :: openSetsL ps (stepOpenL O (rowL p))

/-- A TEST: every item that a block closes or reads is open in front of it. -/
def readsOpenL : List Place → List ItemL → Bool
  | [], _ => true
  | p :: ps, O =>
    ((rowL p).ins ++ (rowL p).ctx).all O.contains && readsOpenL ps (stepOpenL O (rowL p))

/-- A TEST: no block opens an item that is open already. -/
def freshOutsL : List Place → List ItemL → Bool
  | [], _ => true
  | p :: ps, O => ((rowL p).outs.all fun i => !O.contains i) && freshOutsL ps (stepOpenL O (rowL p))

/-- A TEST: behind the last block nothing is open. -/
def endEmptyL : Bool := (openSetsL lastPlaces startLast).getLast? == some []

/-- A TEST AT THE JOINT: this table's start is, item for item, what the shared chain's table leaves open, but for "no mark". -/
def meetsShared : Bool :=
  (endS.filter fun i => i != .unmarked1).all (fun i => startLast.any fun j => j.ofShared == some i) &&
    startLast.all fun j => match j.ofShared with
      | some i => endS.contains i
      | none => false

/-- Which components of the witness an item reads. A COMPONENT .msg m | .w | .index MEANS THE MESSAGE's TABLE BY ITS NUMBER AND THE PAD AT ITS SEAT (no message of these two chains is sent again: one seat a
component). Written by hand; for the five that come over the joint: the shared chain's table's own word. -/
def ItemL.reads : ItemL → List Comp
  | .rows => [.w, .index, .msg .oOmega]
  | i => (i.ofShared.map ItemS.reads).getD []

/-- Which components the extractor of the block at a place lays. -/
def laysOfL (p : Place) : List Comp :=
  if !(rowL p).lays then []
  else match p.piece with
    | 2 => [.w, .index, .msg .oOmega]
    | _ => []

/-- A TEST: no open item that a block does not close reads a component that the block's extractor lays. -/
def laysClearL : List Place → List ItemL → Bool
  | [], _ => true
  | p :: ps, O =>
    ((O.filter fun i => !(rowL p).ins.contains i).all fun i =>
      i.reads.all fun c => !(laysOfL p).contains c) && laysClearL ps (stepOpenL O (rowL p))

/-- A TEST: every component that an item of the start reads is laid by some row of this chain. -/
def laysAllL : Bool :=
  (startLast.flatMap ItemL.reads).all fun c => lastPlaces.any fun p => (laysOfL p).contains c

/-- A TEST OVER TWO TABLES: no component that this chain lays is laid by a row of the shared chain, at either shape. -/
def laidOnce : Bool :=
  [true, false].all fun split =>
    (lastPlaces.flatMap laysOfL).all fun c =>
      (sharedPlaces split).all fun p => !(laysOfS split p).contains c

/-- How many blocks have no row yet. -/
def notYetL (ps : List Place) : Nat := (ps.filter fun p => !(rowL p).known).length

/-! ## 5 The meaning -/

/-- **What this chain's one item of its own says.** S₃: the last chain's own record. -/
structure MeaningL (S₃ Wt : Type) where
  /-- every open row of the own group, as it lies in the record, holds of the witness's messages. NOT HANDED WHAT WAS HANDED TO THE CHAIN: BY TYPE -/
  rows : S₃ → Wt → Prop

section
variable {S₂ S₃ P₁ Wt : Type} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt) (ML : MeaningL S₃ Wt)

/-- **What an item says.** p: the public part with the first chain's last record; e: the shared chain's last record; s: this chain's own record. THE FIVE
THAT COME OVER THE JOINT ARE THE SHARED CHAIN's TABLE's OWN TERMS. -/
def ItemL.holds (i : ItemL) (p : P₁) (e : S₂) (s : S₃) (y : Strs) (w : Wt) : Prop :=
  match i with
  | .ev => ItemS.ev.holdsOwn N Mg p e y w
  | .dot => ItemS.dot.holdsOwn N Mg p e y w
  | .pinV => ItemS.pinV.holdsOwn N Mg p e y w
  | .pinI => ItemS.pinI.holdsOwn N Mg p e y w
  | .pinO => (ItemS.pin .oOmega).holdsSh N Mg e y w
  | .rows => ML.rows s w

end

/-! ## 6 The promise -/

/-- The letters of the promise. -/
structure PromMeaningL (S₂ S₃ P₁ : Type) where
  /-- THE BOOK-KEEPING AT BORDER k: A TEST WITH CODE on public records alone: what was handed, and the chain's own record. MEANT: at 0: the record is the start's of
  what was handed: the own group bears no mark of a test begun, and the first chain's row (Eval) lies among its open rows; at 1 and 2: (Eval) and (Dot), as made of the first
  chain's g and the shared chain's psi_sh, lie among them (AT AN HONEST RUN THEY ARE ALL: one row, then two: the harness asks that too; a law needs "among" alone: a further open row is one
  more that the test closes), and it has JUST three members (an equation: a member that is missing is a pin that the test never took; the order is not asked), W, the index masks' message, Omega, each with the sample, seat and tree's number that it has in the record
  that was handed; at 2 beside: the taken trees' sources; at 3 and 4: the own group's test has begun. WITHOUT IT rows HOLDS FOR NOTHING at a record whose own group has
  no row: THE ITEM ON WHICH THE CLAIM ON THE WEIGHTS HANGS. Other files' to fill; a first filling rides in the harness -/
  shape : Nat → P₁ → S₂ → S₃ → Bool
  /-- every group is tested, every sampled message is in a tested group (the chain's end) -/
  nothingLeft : S₃ → Bool

section
variable {S₂ S₃ P₁ Wt : Type} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt) (Pm : PromMeaning S₂)
  (PL : PromMeaningL S₂ S₃ P₁) (Oc : P₁ → Strs → Prop)

/-- **The promise at border k.** Oc: the slot's own condition, as it rode along the shared chain (at the filling that is meant: the first chain's whole
promise at its last border: there stand W's and the index masks' "held, shown, no collision", and the two conditions on the record that (Eval) lies on
the own group; behind block 2, where these two pins are closed, it says more than is needed: harmless). NO MARK. While Omega's pin is open: the shared chain's promise on Omega, at its last record. The book-keeping. Behind the last block: nothing is
left. -/
def onL (k : Nat) (p : P₁) (e : S₂) (s : S₃) (y : Strs) : Prop :=
  Oc p y ∧ Mg.unmarked1 p ∧
    (((openSetsL lastPlaces startLast)[k]?.getD []).contains .pinO = true →
      (PromS.noColl .oOmega).holds N Pm e y) ∧
    PL.shape k p e s = true ∧ (lastPlaces.length ≤ k → PL.nothingLeft s = true)

end

/-! ## The tests on the table, by evaluation -/

example : readsOpenL lastPlaces startLast = true := by decide
example : freshOutsL lastPlaces startLast = true := by decide
example : endEmptyL = true := by decide
example : meetsShared = true := by decide
example : laysClearL lastPlaces startLast = true := by decide
example : laysAllL = true := by decide
example : laidOnce = true := by decide
example : notYetL lastPlaces = 0 := by decide
example : openSetsL lastPlaces startLast =
    [[.pinI, .pinV, .ev, .dot, .pinO], [.pinI, .pinV, .pinO, .rows], [.pinI, .pinV, .pinO, .rows], [], []] := by decide
-- CONTROLS: each test can fail
example : readsOpenL (lastPlaces.drop 1) startLast = false := by decide
example : ((openSetsL (lastPlaces.take 2) startLast).getLast? == some []) = false := by decide
example : laysClearL [⟨3, none, 2, .K12⟩] (.ev :: startLast) = false := by decide

end VerifiableInference.Desc.Last
