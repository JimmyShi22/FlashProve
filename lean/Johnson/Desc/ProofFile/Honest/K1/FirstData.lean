-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/FirstData.lean: THE DATA OF THE SEGMENTS' FIRST SENDINGS: the
arrays "M mu" of moment 0: a filling of RowData (Johnson/Desc/ProofFile/Honest/RowData.lean).
Definitions with code, and tests at the small example's sizes; no theorem.

What a first sending holds. By docs/format/11-1-machinery.md a segment commits, in its first
prover's message, to each matrix number mu of its list that no earlier segment has committed to, as
the array "M mu": three rows of cells in one element of the base field. The packing is packedCells
(Johnson/HonestTrace/Packed.lean); where an array's element lies in its oracle message is the public
item "layout" (laidData, Johnson/Desc/ProofFile/Honest/LaidData.lean).

  labelNo         the number mu off an array's name "M mu"; none for every other name
  cellsVals       the values of the arrays "M mu" of all segments: of Readers.cells alone
  firstSeat       the seat of the first segment's opening (the place 1 / 0 / 1 of the kind K1): its
                  first messages are the segment's own of moment 0, in the list's order
  momentSeat      the seat of a sending that holds the messages of one moment of one segment, from a
                  number on
  firstData       THE FILLING, at a seat

It reads no challenge, no weight and no coin: of the readers the cells alone.

WHICH SENDINGS THESE ARE. At the full-size example's plan
(Johnson/Desc/ProofFile/Law/Skel/Full/Data.lean) 25 segments have a first sending. ONE stands at a
place of the kind K1: the first segment's opening. The other 24 stand at places of the kind K2 (1 /
l / 1 for l from 1 to 23; the output head's at 1 / 24 / 2), which send the carrying message, then
the kept messages, then the segment's own: the data of the segment's own messages is this same
function; at which number of that sending they begin is that kind's to say (momentSeat's parameter
"from").

WHAT ELSE A FIRST SENDING HOLDS, AND THIS FILLING DOES NOT LAY. The fold's fresh mask and the
messages at the start (no data: coins) · the carrying message (RowData.lean: not this function's) ·
THE ARRAYS OF EARLIER SEGMENTS THAT ARE KEPT: by docs/format/11-1-machinery.md a matrix that an
earlier segment has committed to has no array in this segment; the earlier segment's array is kept
and sent again in this segment's first prover's message: its data is that of the message that bore
it, under the new address (RowData.comap): the kind's that sends it anew.

Limits. packedCells returns 0 outside a matrix's packed shape: cellsVals.inside is the test with
code that the layout's arrays are as large as the packed shapes; with the plan's own test (msgFits,
inside "lays"), by which every laid block lies inside its array, no such place is laid: tested at
the toy, not proved. That the programs pack so, and that a layout file's arrays bear these names, is
not proved. The toy lays one whole array of the small example's output head; no whole layout file is
run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.LaidData
import Johnson.HonestTrace.Packed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes.Params (LaidBlock ReqArray ReqLayout ReqShape)
open OnBytes.HonestTrace (Sz packedCells arrayLabel)
open OnBytes.Slice (toF ofE)

/-- The number mu off an array's name "M mu": just the names that arrayLabel makes are read. -/
def labelNo (name : String) : Option Nat :=
  (if name.startsWith "M" then (name.drop 1).toNat? else none).bind fun mu =>
    if arrayLabel mu == name then some mu else none

/-- **The arrays "M mu".** S: the sizes. A matrix that an earlier segment has committed to has no
array of this segment (Sz.arrayNo): none is served under its number. -/
def cellsVals (S : Sz) : ArrayVals :=
  { size := fun l name =>
      (labelNo name).bind fun mu => (S.matAt l mu).bind fun x =>
        if (S.arrayNo x.1 x.2).isSome then some (S.packedShape l mu) else none
    val := fun R _ l name i c =>
      match labelNo name with
      | some mu => .inl (packedCells S R.cells.cell l mu i c)
      | none => .inl (toF 0) }

/-- The seat of a sending at the address "sender" whose messages from the number "from" on are the
messages of moment t of segment l, in the list's order. -/
def momentSeat (s : ReqShape) (sender : Addr) (l t «from» : Nat) (a : MsgAddr) :
    Option (Nat × Nat) :=
  if a.sender == sender ∧ «from» ≤ a.msg then (msgNo s l t (a.msg - «from»)).map fun m => (l, m)
  else none

/-- The seat of the first segment's opening. part: the part's number at that place. -/
def firstSeat (s : ReqShape) (part : Nat) : MsgAddr → Option (Nat × Nat) :=
  momentSeat s ⟨⟨1, some 0, 1, .K1⟩, part⟩ 0 0 0

/-- **THE FILLING.** -/
def firstData (S : Sz) (codes : OnBytes.Codes) (s : ReqShape) (lay : ReqLayout)
    (seat : MsgAddr → Option (Nat × Nat)) (heard : MsgAddr → Nat) : RowData :=
  laidData codes s lay seat heard (cellsVals S)

/-! ### Tests at the small example's sizes -/

namespace FirstDataToy

#guard labelNo "M0" == some 0 && labelNo "M12" == some 12 && labelNo "U3" == none &&
  labelNo "M" == none && labelNo "Mx" == none && labelNo (arrayLabel 7) == some 7
-- NEGATIVE TESTS: no second spelling of a number is read
#guard labelNo "M01" == none && labelNo "M1_0" == none && labelNo "M 1" == none &&
  labelNo "M+1" == none && labelNo "m1" == none

/-- A cell: 1 + the row, in every matrix. -/
def R : Readers :=
  ⟨⟨fun _ _ r _ => toF (1 + r.toUInt64)⟩, ⟨fun _ _ => toF 0⟩,
    fun _ => ⟨fun _ _ => toF 0, fun _ _ => toF 0⟩⟩
/-- Every cell is 0. -/
def R₀ : Readers := { R with cells := ⟨fun _ _ _ _ => toF 0⟩ }

/-- At the small example's sizes the output head is segment 4; its matrix number 2 ("hr") has 4096
rows of cells and 2 columns: 1366 packed rows. A WHOLE LAYOUT OF THAT ARRAY, in a message of two
rows of 2048 places: six laid blocks, of 1024, 256, 64, 16, 4 and 2 packed rows. The message 1, of
moment 1, holds an array "U3". -/
def blocks : List LaidBlock :=
  [⟨0, 0, 0, 0, 10, 1, 0, 11, true⟩, ⟨1024, 0, 1, 0, 8, 1, 0, 9, true⟩,
   ⟨1280, 0, 1, 512, 6, 1, 0, 7, true⟩, ⟨1344, 0, 1, 640, 4, 1, 0, 5, true⟩,
   ⟨1360, 0, 1, 672, 2, 1, 0, 3, true⟩, ⟨1364, 0, 1, 680, 1, 1, 0, 2, true⟩]
def lay : ReqLayout :=
  ⟨[[], [], [], [],
    [⟨"M2", 0, 1366, 2, blocks⟩, ⟨"U3", 1, 1, 8, [⟨0, 0, 0, 0, 0, 3, 0, 3, true⟩]⟩]]⟩
def codes : OnBytes.Codes := { base := #[⟨13, 2048, 1⟩] }
def o : OnBytes.OracleShape :=
  { code := 0, mainRows := 2, mainDeg := 1, maskRows := 0, answers := 1 }
def sh : ReqShape :=
  { code := 0, maskCode := 0, atStart := [], answers := 1, last := [], choice := default
    link := [⟨0, [⟨o, 0, 0, 0⟩]⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨0, [⟨o, 0, 0, 0⟩, ⟨o, 0, 1, 0⟩]⟩] }
/-- A sending whose message 0 is another's (a carrying message); the segment's own begin at 1. -/
def seat : MsgAddr → Option (Nat × Nat) := momentSeat sh (toyTo 0) 4 0 1
def D : RowData := firstData Sz.small codes sh lay seat fun _ => 0
def at_ (k : Nat) : MsgAddr := ⟨toyTo 0, k⟩
def seeE (x : Option (Cb.Gl.F ⊕ Cb.Gl.E)) : UInt64 × UInt64 × UInt64 := ofE (asE x)

-- the sizes, and the plan's own test on the message's arrays
#guard Sz.small.shapeNo 4 2 == (4096, 2) && Sz.small.packedShape 4 2 == (1366, 2)
#guard (cellsVals Sz.small).inside lay 4 && msgFits codes sh lay 4 0
-- element (0, 0): the cells' rows 0, 1, 2: 1 + 2^20 * 2 + 2^40 * 3; element (1, 0): 4, 5, 6
#guard seeE (D.at_ R [] (at_ 1) 0 0) == ((1 + 2 ^ 20 * 2 + 2 ^ 40 * 3 : Nat).toUInt64, 0, 0)
#guard seeE (D.at_ R [] (at_ 1) 0 1) == ((4 + 2 ^ 20 * 5 + 2 ^ 40 * 6 : Nat).toUInt64, 0, 0)
-- the last element, (1365, 1), at row 1, place 683: the one row of cells 4095; the two beyond the
-- matrix count as 0 (the format's rule)
#guard seeE (D.at_ R [] (at_ 1) 1 683) == (4096, 0, 0)
-- as many places as elements: 2 * 1366
#guard ((List.range 2).map fun r => ((List.range 2048).filter fun j => D.lays (at_ 1) r j).length)
  == [2048, 684]
-- where all cells are 0: DATA STANDS THERE, and it is 0
#guard (D.at_ R₀ [] (at_ 1) 0 0).isSome && seeE (D.at_ R₀ [] (at_ 1) 0 0) == (0, 0, 0)
-- it is over the base field; the pad's places are clear
#guard ((D.at_ R [] (at_ 1) 0 0).any fun x => x.isLeft) && D.clear (at_ 1) 2048 o
-- NEGATIVE TESTS: nothing behind the last element; nothing at the sending's message 0 (another's)
-- or 2 (none of moment 0); nothing at another part; nothing at "U3"'s message, which is another
-- filling's, though the seat names it
#guard (D.at_ R [] (at_ 1) 1 684).isNone && (D.at_ R [] (at_ 0) 0 0).isNone &&
  (D.at_ R [] (at_ 2) 0 0).isNone && (D.at_ R [] ⟨toyTo 1, 1⟩ 0 0).isNone
#guard ((firstData Sz.small codes sh lay (momentSeat sh (toyTo 0) 4 1 0) fun _ => 0).at_ R []
  (at_ 0) 0 0).isNone
-- a layout whose array is a column wider than the packed shape: "inside" fails
#guard !(cellsVals Sz.small).inside ⟨[[], [], [], [], [⟨"M2", 0, 1366, 3, []⟩]]⟩ 4
-- a layout that lacks the last laid block does not cover its array: the plan's test fails, and
-- nothing is laid
#guard !msgFits codes sh ⟨[[], [], [], [], [⟨"M2", 0, 1366, 2, blocks.take 5⟩]]⟩ 4 0 &&
  ((firstData Sz.small codes sh ⟨[[], [], [], [], [⟨"M2", 0, 1366, 2, blocks.take 5⟩]]⟩ seat
    fun _ => 0).at_ R [] (at_ 1) 0 0).isNone
-- a name beyond the segment's list, and a segment beyond the proof, are no arrays of these; nor is
-- a borrowed matrix's number: the output head's last matrix (number 4) is an earlier segment's
#guard ((cellsVals Sz.small).size 4 "M99").isNone && ((cellsVals Sz.small).size 99 "M0").isNone &&
  (Sz.small.matAt 4 4).isSome && ((cellsVals Sz.small).size 4 "M4").isNone
-- the first segment's opening: its message 0 is the segment's own; none at another part or place
#guard firstSeat sh 0 ⟨⟨⟨1, some 0, 1, .K1⟩, 0⟩, 0⟩ == some (0, 0) &&
  firstSeat sh 0 ⟨⟨⟨1, some 0, 1, .K1⟩, 0⟩, 1⟩ == none &&
  firstSeat sh 0 ⟨⟨⟨1, some 0, 1, .K1⟩, 1⟩, 0⟩ == none &&
  firstSeat sh 0 ⟨⟨⟨1, some 0, 4, .K1⟩, 0⟩, 0⟩ == none

end FirstDataToy

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.labelNo
#print axioms ProofFile.Honest.K1.cellsVals
#print axioms ProofFile.Honest.K1.momentSeat
#print axioms ProofFile.Honest.K1.firstSeat
#print axioms ProofFile.Honest.K1.firstData
#print axioms ProofFile.Honest.K1.FirstDataToy.R
#print axioms ProofFile.Honest.K1.FirstDataToy.R₀
#print axioms ProofFile.Honest.K1.FirstDataToy.blocks
#print axioms ProofFile.Honest.K1.FirstDataToy.lay
#print axioms ProofFile.Honest.K1.FirstDataToy.codes
#print axioms ProofFile.Honest.K1.FirstDataToy.o
#print axioms ProofFile.Honest.K1.FirstDataToy.sh
#print axioms ProofFile.Honest.K1.FirstDataToy.seat
#print axioms ProofFile.Honest.K1.FirstDataToy.D
#print axioms ProofFile.Honest.K1.FirstDataToy.at_
#print axioms ProofFile.Honest.K1.FirstDataToy.seeE
