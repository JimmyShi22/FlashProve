-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/LaidData.lean: FROM A PLACE OF AN ORACLE MESSAGE's TABLE BACK TO THE
ARRAY's ELEMENT THAT THE PUBLIC ITEM "layout" LAYS THERE, and a filling of RowData
(Johnson/Desc/ProofFile/Honest/RowData.lean) that is made of it and of the arrays' values.
Definitions with code, and tests at a toy; no theorem.

Why. The item "layout" (Params.ReqLayout, OnBytes/Params/Items.lean) says of every array of every
segment in which oracle message it lies and, laid block by laid block, at which rows and places. So
whoever knows an array's values by (segment, array's name, i, c) has the message's main rows: one
way back serves every array: the matrices of cells, and the arrays that are computed from cells and
challenges.

  blockBack       the way back from the format's rule (laidIn, Johnson/Desc/LaidAt.lean): the
                  element that a laid block holds at a row and place
  arrayBack, laidBack   the same for an array; for a message of a segment: the array and the element
  msgNo           the number, in its segment's list, of the k-th message of a moment
  msgFits         the plan's own test on the arrays of one message (PUBLIC)
  layFits         the layout has a list of arrays for each segment of the shape (PUBLIC)
  ArrayVals       the values of some arrays: which arrays (PUBLIC), and the element at (i, c)
  laidData        THE FILLING: at an address that the seat names, where the layout lays an element
                  of an array that V has: that element
  ArrayVals.inside   a test with code on public data: every array that V has is as large in the
                  layout as V says

The seat (an address ↦ the segment's number and the message's number in the segment's list) and the
number of challenges heard are PUBLIC parameters: the sub-protocol that holds the sending says them.

NOTHING IS LAID WHERE THE LAYOUT LAYS NOTHING: there "lays" is false and RowData.at_ returns none.
By the format these entries are 0: "The entries of the main rows of a segment's oracle message that
no block of the layout file fills (13.4, step 7) MUST be 0, but for the entries of the message's pad
(section 9)" (docs/format/FORMAT.md). NOTHING IS LAID IN A MESSAGE WHOSE ARRAYS FAIL THE PLAN's OWN
TEST (Own.reqMessageLaid, Johnson/Desc/Own/Req.lean): that test says that no laid block lies in a
row that is not sent or holds a place of the sample's pad, and that no two hold one place; NOR IN A
MESSAGE WITHOUT A SAMPLE, all of whose main entries are coins. WHERE THE LAYOUT LAYS AN ARRAY IN
SUCH A MESSAGE, "ready" SAYS SO ALOUD to a caller that asks RowData.readyAt: that is a misfit of
public data. A message in which the layout lays no array is no misfit, sampled or not: nothing is
laid, and "ready" stays true. A LAYOUT THAT HAS NOT ONE LIST OF ARRAYS FOR EACH SEGMENT OF THE SHAPE
IS A MISFIT TOO (layFits): "ready" is false at every seated address.

READ IT THROUGH RowData.at_ ALONE: the field "entry" is not guarded by "lays".

Kin. The rule forward: laidIn, laidAt, seatIn (Johnson/Desc/LaidAt.lean): not typed again; laidIn is
called in the tests here. That no element of an array sits on the pad, forward, under another test
and at one answer: padB_off (Johnson/Desc/Kinds/Law/LaidOffPad.lean). blockCell, cellAt and
listNumber of the kind K2's honest side (Johnson/Desc/ProofFile/Honest/K2/Half.lean) are blockBack,
laidBack and labelNo (Johnson/Desc/ProofFile/Honest/K1/FirstData.lean) without the bound on the
element's number, the plan's test, the size and the one spelling of a name.

Limits. No law HERE. Elsewhere: that blockBack undoes laidIn: OF ONE LAID BLOCK, where it is as
large in the table as in its array (the plan's own test gives that): Honest/Law/LaidBack.lean · of
an array's list of blocks and of a message's arrays (laidBack), under the plan's test:
Honest/Law/LaidLists.lean, LaidApart.lean, LaidOnce.lean · that where the filling lays there is
room, off the pad, and that RowData.clear holds at every seated message: Honest/Law/LaysRoom.lean,
UNDER Codes.lengthsOk: WITHOUT THAT PREMISE clear CAN REFUSE WHERE msgFits ACCEPTS (at a code of
length 3: a test by evaluation: Honest/Law/LaysRoomSmall.lean). The test is held at the shape in the
list and at the codes that are handed in: that these are the sender's: at momentSeat's seats (the
place's part 0, from 0, at K1.firstPar and K1.parLater): Honest/K1/SeatShape.lean. Where two arrays
held one place the first in the list would be read, also where it is not V's and the second is:
msgFits forbids both. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.RowData
import Johnson.Desc.Own.Req
import Johnson.Desc.LaidAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes.Params (LaidBlock ReqArray ReqLayout ReqShape)
open OnBytes.Slice (toF toE ofE)
open VerifiableInference.Desc (laidIn)

/-- **The way back**: the array's element that the laid block holds at (row, place); none outside
its rectangle, and none at a number from the laid block's count of elements on. -/
def blockBack (b : LaidBlock) (r j : Nat) : Option (Nat × Nat) :=
  let x := (r - b.firstRow) * 2 ^ b.placeBits + (j - b.firstPlace)
  if b.firstRow ≤ r ∧ r < b.firstRow + 2 ^ b.rowBits ∧ b.firstPlace ≤ j ∧
      j < b.firstPlace + 2 ^ b.placeBits ∧ x < 2 ^ (b.bitsI + b.bitsC) then
    some (if b.iIsLow then (b.firstI + x % 2 ^ b.bitsI, b.firstC + x / 2 ^ b.bitsI)
      else (b.firstI + x / 2 ^ b.bitsC, b.firstC + x % 2 ^ b.bitsC))
  else none

/-- The element of the array at (row, place). -/
def arrayBack (a : ReqArray) (r j : Nat) : Option (Nat × Nat) :=
  a.blocks.findSome? fun b => blockBack b r j

/-- The array of segment l's message number m, and its element, at (row, place). -/
def laidBack (lay : ReqLayout) (l m r j : Nat) : Option (ReqArray × Nat × Nat) :=
  ((lay.link.getD l []).filter fun a => a.message == m).findSome? fun a =>
    (arrayBack a r j).map fun p => (a, p.1, p.2)

/-- The number, in segment l's list of oracle messages, of the k-th message of moment t. -/
def msgNo (s : ReqShape) (l t k : Nat) : Option Nat :=
  ((((s.link.getD l default).messages.zipIdx.filter fun m => m.1.moment == t))[k]?).map (·.2)

/-- **The plan's own test on the arrays of one message** (Own.reqMessageLaid): the laid blocks are
even, apart, inside the table and cover their arrays; none lies in a row that is not sent; none
holds a place of the pad of the message's sample. AND A MESSAGE THAT HOLDS AN ARRAY IS SAMPLED:
every entry of the main rows of a message without a sample is a coin. True at a message in which the
layout lays no array: there is nothing to fill. False where the segment has no such message. -/
def msgFits (codes : OnBytes.Codes) (s : ReqShape) (lay : ReqLayout) (l m : Nat) : Bool :=
  ((s.link.getD l default).messages[m]?).any fun M =>
    ((lay.link.getD l []).filter fun a => a.message == m).isEmpty ||
      (M.shape.answers != 0 && VerifiableInference.Desc.Own.reqMessageLaid codes M.shape
        ((lay.link.getD l []).filter fun a => a.message == m))

/-- **The layout has a list of arrays for each segment of the shape, and no more**: the first clause
of the plan's own test on a layout (Own.reqLayoutFits). Where the layout is the shorter, a segment
beyond its end would look like one in which no array lies. -/
def layFits (s : ReqShape) (lay : ReqLayout) : Bool := lay.link.length == s.link.length

/-- **The values of some arrays.** -/
structure ArrayVals where
  /-- PUBLIC: the array of this name of this segment is among them; its rows and columns -/
  size : Nat → String → Option (Nat × Nat)
  /-- the element: of the readers, the challenges heard, the segment, the name, i, c -/
  val : Readers → List Fmt.Drawn → Nat → String → Nat → Nat → Cb.Gl.F ⊕ Cb.Gl.E
  /-- a test on the challenges heard, as RowData.ready -/
  ready : List Fmt.Drawn → Nat → Bool := fun _ _ => true

/-- **THE FILLING.** seat: the segment and the message's number in its list; heard: how many
challenges have been heard when the sending begins. IT LAYS NOTHING IN A MESSAGE WHOSE ARRAYS FAIL
THE PLAN's OWN TEST, AND NOTHING AT AN ELEMENT BEYOND THE SIZE THAT V SAYS. "ready" is false at such
a message: a caller that asks RowData.readyAt is told, and need not take "nothing is laid" for free
room. -/
def laidData (codes : OnBytes.Codes) (s : ReqShape) (lay : ReqLayout)
    (seat : MsgAddr → Option (Nat × Nat)) (heard : MsgAddr → Nat) (V : ArrayVals) : RowData :=
  { heardAt := heard
    lays := fun a r j =>
      match seat a with
      | some (l, m) =>
        msgFits codes s lay l m && (laidBack lay l m r j).any fun x =>
          (V.size l x.1.name).any fun z => decide (x.2.1 < z.1 ∧ x.2.2 < z.2)
      | none => false
    entry := fun R h a r j =>
      match seat a with
      | some (l, m) =>
        match laidBack lay l m r j with
        | some (x, i, c) => V.val R h l x.name i c
        | none => .inl (toF 0)
      | none => .inl (toF 0)
    ready := fun h a =>
      (seat a).all fun x => layFits s lay && msgFits codes s lay x.1 x.2 && V.ready h x.1 }

/-- **A test with code on public data**: every array of segment l that V has is as large in the
layout as V says. No guard of the filling's ("lays" asks the size itself): where it passes, at a
seated message that fits (msgFits), every element that the layout lays of V's arrays is meant to be
data: no law here says so. -/
def ArrayVals.inside (V : ArrayVals) (lay : ReqLayout) (l : Nat) : Bool :=
  (lay.link.getD l []).all fun a => (V.size l a.name).all fun s => s == (a.sizeI, a.sizeC)

/-! ### Tests at a toy -/

namespace LaidDataToy

/-- A table of four rows of eight places. "A": 2 × 4, i in the low bits, in the rows 0 and 1 at the
places 0 to 3. "B": 4 × 2, in two laid blocks, c in the low bits: rows 2 and 3, places 0 to 1, and
row 0, places 4 to 7. -/
def bA : LaidBlock := ⟨0, 0, 0, 0, 1, 2, 1, 2, true⟩
def bB0 : LaidBlock := ⟨0, 0, 2, 0, 1, 1, 1, 1, false⟩
def bB1 : LaidBlock := ⟨2, 0, 0, 4, 1, 1, 0, 2, false⟩
def lay : ReqLayout := ⟨[[⟨"A", 0, 2, 4, [bA]⟩, ⟨"B", 0, 4, 2, [bB0, bB1]⟩, ⟨"C", 1, 1, 1, []⟩]]⟩
/-- One base code with messages of eight places. The message 0: four main rows over the base field,
no mask row, one answer: its pad: the last three places of the last row. The message 1: a row. -/
def codes : OnBytes.Codes := { base := #[⟨4, 8, 1⟩] }
def o₀ : OnBytes.OracleShape :=
  { code := 0, mainRows := 4, mainDeg := 1, maskRows := 0, answers := 1 }
def shp : ReqShape :=
  { code := 0, maskCode := 0, atStart := [], answers := 1, last := [], choice := default
    link := [⟨0, [⟨o₀, 0, 0, 0⟩, ⟨{ o₀ with mainRows := 1 }, 0, 0, 0⟩]⟩] }
def a₀ : MsgAddr := ⟨toyTo 0, 0⟩
def a₁ : MsgAddr := ⟨toyTo 0, 1⟩
def seat (a : MsgAddr) : Option (Nat × Nat) := if a == a₀ then some (0, 0) else none
def R : Readers :=
  ⟨⟨fun _ n r j => toF (if n == "A" then 100 + 10 * r.toUInt64 + j.toUInt64 else 0)⟩,
    ⟨fun _ _ => toF 0⟩, fun _ => ⟨fun _ _ => toF 0, fun _ _ => toF 0⟩⟩
/-- V has "A" alone. -/
def V : ArrayVals :=
  { size := fun _ n => if n == "A" then some (2, 4) else none
    val := fun R _ l n i c => .inl (R.cells.cell l n i c) }
def D : RowData := laidData codes shp lay seat (fun _ => 0) V
def seeE (x : Option (Cb.Gl.F ⊕ Cb.Gl.E)) : UInt64 × UInt64 × UInt64 := ofE (asE x)

-- the rule, forward: element (1, 2) of "A" has the number 2 * 2 + 1 = 5: row 1, place 1
#guard laidIn bA 1 2 == some (1, 1) && blockBack bA 1 1 == some (1, 2)
-- THE WAY BACK UNDOES THE RULE, at every element of the three laid blocks
#guard [bA, bB0, bB1].all fun b => (List.range 4).all fun i => (List.range 4).all fun c =>
  (laidIn b i c).all fun p => blockBack b p.1 p.2 == some (i, c)
-- and the rule undoes the way back, at every place of the table
#guard [bA, bB0, bB1].all fun b => (List.range 4).all fun r => (List.range 8).all fun j =>
  (blockBack b r j).all fun e => laidIn b e.1 e.2 == some (r, j)
-- NEGATIVE TEST: a laid block whose rectangle is larger than its count of elements (8 places, 4
-- elements): nothing is handed out from the number 4 on, and the rule still undoes the way back
def bWide : LaidBlock := ⟨0, 0, 0, 0, 1, 1, 1, 2, true⟩
#guard blockBack bWide 0 3 == some (1, 1) && blockBack bWide 1 0 == none &&
  (List.range 4).all fun r => (List.range 8).all fun j =>
    (blockBack bWide r j).all fun e => laidIn bWide e.1 e.2 == some (r, j)
-- as many places as elements: 8 of "A", 8 of "B"
#guard ((List.range 4).flatMap fun r => (List.range 8).filter fun j =>
  (laidBack lay 0 0 r j).any (·.1.name == "A")).length == 8
#guard ((List.range 4).flatMap fun r => (List.range 8).filter fun j =>
  (laidBack lay 0 0 r j).any (·.1.name == "B")).length == 8
-- the filling: "A"'s element (1, 2) at row 1, place 1
#guard seeE (D.at_ R [] a₀ 1 1) == (112, 0, 0)
-- NEGATIVE TESTS: nothing at a place of "B", which V has not; nothing where the layout lays
-- nothing; nothing at an address that the seat does not name; nothing beyond the table
#guard (D.at_ R [] a₀ 2 0).isNone && (D.at_ R [] a₀ 3 2).isNone && (D.at_ R [] a₁ 1 1).isNone &&
  (D.at_ R [] a₀ 4 0).isNone && (D.at_ R [] a₀ 0 8).isNone
-- the sizes: as V says; not so where V says another size
#guard V.inside lay 0 && !({ V with size := fun _ n => if n == "A" then some (2, 5) else none } :
  ArrayVals).inside lay 0
-- NEGATIVE TEST: where V says a smaller size than the layout, nothing is laid beyond V's size:
-- "A"'s element (1, 2) is beyond 2 × 2; (1, 1), at row 0, place 3, is inside
#guard ((laidData codes shp lay seat (fun _ => 0)
    { V with size := fun _ n => if n == "A" then some (2, 2) else none }).at_ R [] a₀ 1 1).isNone &&
  ((laidData codes shp lay seat (fun _ => 0)
    { V with size := fun _ n => if n == "A" then some (2, 2) else none }).at_ R [] a₀ 0 3).isSome
-- two fillings of one message, array by array: apart, and laid over each other
def VB : ArrayVals :=
  { size := fun _ n => if n == "B" then some (4, 2) else none
    val := fun _ _ _ _ i c => .inl (toF (200 + 10 * i.toUInt64 + c.toUInt64)) }
def DB : RowData := laidData codes shp lay seat (fun _ => 0) VB
#guard D.apart DB a₀ 4 8 && seeE ((D.over DB).at_ R [] a₀ 0 6) == (230, 0, 0) &&
  seeE ((D.over DB).at_ R [] a₀ 1 1) == (112, 0, 0) && ((D.over DB).at_ R [] a₀ 3 2).isNone
-- the plan's own test passes at the toy's message 0; the pad's places are clear
#guard msgFits codes shp lay 0 0 && D.clear a₀ 8 o₀
-- NEGATIVE TESTS ON THE LAYOUT: "A" laid over the pad's places (rows 2 and 3, places 4 to 7); "A"
-- in rows that are not sent (a message of one row); two arrays on one place; a segment or a
-- message that is not there: THE TEST FAILS, AND THE FILLING LAYS NOTHING AT ALL IN THAT MESSAGE
def onPad : ReqLayout := ⟨[[⟨"A", 0, 2, 4, [{ bA with firstRow := 2, firstPlace := 4 }]⟩]]⟩
def twice : ReqLayout := ⟨[[⟨"A", 0, 2, 4, [bA]⟩, ⟨"B", 0, 2, 4, [bA]⟩]]⟩
def none8 (D : RowData) (a : MsgAddr) : Bool :=
  (List.range 4).all fun r => (List.range 8).all fun j => !D.lays a r j
#guard !msgFits codes shp onPad 0 0 && none8 (laidData codes shp onPad seat (fun _ => 0) V) a₀
#guard !msgFits codes shp twice 0 0 && none8 (laidData codes shp twice seat (fun _ => 0) V) a₀
#guard !msgFits codes shp ⟨[[⟨"A", 1, 2, 4, [bA]⟩]]⟩ 0 1 && !msgFits codes shp lay 1 0 &&
  !msgFits codes shp lay 0 2
-- a message without a sample: the plan's test passes (it has no pad), msgFits does not
def shp0 : ReqShape := { shp with link := [⟨0, [⟨{ o₀ with answers := 0 }, 0, 0, 0⟩]⟩] }
#guard VerifiableInference.Desc.Own.reqMessageLaid codes { o₀ with answers := 0 }
    ((lay.link.getD 0 []).filter fun a => a.message == 0) &&
  !msgFits codes shp0 lay 0 0 && none8 (laidData codes shp0 lay seat (fun _ => 0) V) a₀
-- but a message without a sample IN WHICH NO ARRAY LIES is no fault: nothing to fill, and ready
#guard msgFits codes shp0 ⟨[[]]⟩ 0 0 &&
  (laidData codes shp0 ⟨[[]]⟩ seat (fun _ => 0) V).readyAt [] a₀ &&
  none8 (laidData codes shp0 ⟨[[]]⟩ seat (fun _ => 0) V) a₀
-- AND IT IS SAID ALOUD: readyAt is false at such a message, true at the toy's own
#guard D.readyAt [] a₀ && !(laidData codes shp onPad seat (fun _ => 0) V).readyAt [] a₀ &&
  !(laidData codes shp twice seat (fun _ => 0) V).readyAt [] a₀
-- NEGATIVE TEST: a layout that is shorter than the shape: the segment looks like one without an
-- array (msgFits passes; nothing is laid): layFits fails, AND IT IS SAID ALOUD
#guard msgFits codes shp ⟨[]⟩ 0 0 && !layFits shp ⟨[]⟩ && layFits shp lay &&
  none8 (laidData codes shp ⟨[]⟩ seat (fun _ => 0) V) a₀ &&
  !(laidData codes shp ⟨[]⟩ seat (fun _ => 0) V).readyAt [] a₀
-- without the test the way back alone would lay "A" on the pad: so the test is what refuses
#guard (laidBack onPad 0 0 3 5).isSome
-- the k-th message of a moment
def sh : ReqShape :=
  { code := 0, maskCode := 0, atStart := [], answers := 1, last := [], choice := default
    link := [⟨0, [⟨{}, 0, 0, 0⟩, ⟨{}, 0, 1, 0⟩, ⟨{}, 0, 0, 0⟩, ⟨{}, 0, 2, 0⟩]⟩] }
#guard msgNo sh 0 0 0 == some 0 && msgNo sh 0 0 1 == some 2 && msgNo sh 0 0 2 == none &&
  msgNo sh 0 1 0 == some 1 && msgNo sh 0 2 0 == some 3 && msgNo sh 1 0 0 == none

end LaidDataToy

end ProofFile.Honest

#print axioms ProofFile.Honest.blockBack
#print axioms ProofFile.Honest.arrayBack
#print axioms ProofFile.Honest.laidBack
#print axioms ProofFile.Honest.msgNo
#print axioms ProofFile.Honest.msgFits
#print axioms ProofFile.Honest.layFits
#print axioms ProofFile.Honest.ArrayVals
#print axioms ProofFile.Honest.laidData
#print axioms ProofFile.Honest.ArrayVals.inside
#print axioms ProofFile.Honest.LaidDataToy.bA
#print axioms ProofFile.Honest.LaidDataToy.bB0
#print axioms ProofFile.Honest.LaidDataToy.bB1
#print axioms ProofFile.Honest.LaidDataToy.lay
#print axioms ProofFile.Honest.LaidDataToy.codes
#print axioms ProofFile.Honest.LaidDataToy.o₀
#print axioms ProofFile.Honest.LaidDataToy.shp
#print axioms ProofFile.Honest.LaidDataToy.a₀
#print axioms ProofFile.Honest.LaidDataToy.a₁
#print axioms ProofFile.Honest.LaidDataToy.seat
#print axioms ProofFile.Honest.LaidDataToy.R
#print axioms ProofFile.Honest.LaidDataToy.V
#print axioms ProofFile.Honest.LaidDataToy.D
#print axioms ProofFile.Honest.LaidDataToy.seeE
#print axioms ProofFile.Honest.LaidDataToy.bWide
#print axioms ProofFile.Honest.LaidDataToy.VB
#print axioms ProofFile.Honest.LaidDataToy.DB
#print axioms ProofFile.Honest.LaidDataToy.onPad
#print axioms ProofFile.Honest.LaidDataToy.twice
#print axioms ProofFile.Honest.LaidDataToy.none8
#print axioms ProofFile.Honest.LaidDataToy.shp0
#print axioms ProofFile.Honest.LaidDataToy.sh
