-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/Room.lean: how many entries of a vector have room in an oracle message, as a named
part of the description: THE TEST THAT THE HAND-WRITTEN PROGRAM's vectorRoom HIDES IN A NUMBER, BY
NAME, AND THE NUMBER.

The program's vectorRoom (OnBytes/Iop/Foldeq.lean) returns a number that is 0 in three cases, and a
caller's "n ≤ vectorRoom …" with 1 ≤ n refuses there: three tests that no clause names. Here they
are a test of their own.

  roomCan codes s rowsHigh
      THE MESSAGE CAN HOLD A VECTOR IN THIS LAYOUT. Three clauses: the rows' bits are the high ones,
      or the number of main rows is just 2 ^ rowBits, rowBits := ceilLog2 of that number (the other
      layout uses all 2 ^ rowBits rows from the first entries on); the table has at most 60 index
      bits; the message has no sample, or a row is long enough for the sample's pad (padMade
      returns): a MASK row where the shape has mask rows (the pad lies in the mask table then, and
      bounds nothing in the main table), else a main row.
  roomOf codes s rowsHigh
      THE NUMBER OF ENTRIES, FROM ENTRY 0 ON, THAT LIE IN REAL ROWS AND BEFORE EVERY PLACE OF THE
      PAD. 0 where roomCan says no; it can be 0 where roomCan says yes too (no main row; a place of
      the pad at entry 0).
How far the text is its own: roomOf is the program's text with padMade (Johnson/Desc/Own/Send.lean)
for Send.pad and the three cases gathered into roomCan. What is still called of the program's files
[their bodies read: OnBytes/Iop/Foldeq.lean: vectorLay; OnBytes/Iop/Tensor.lean: bits, entryAt]:
VectorLay.bits: a sum. entryAt: one of two formulas, by the layout. vectorLay: ceilLog2 of the rows
and the logarithm of the code's message length: IT READS THE CODE BY "getD … default": AT A CODE's
NUMBER THAT IS NOT IN THE LIST IT TAKES THE DEFAULT CODE AND SAYS NOTHING: whoever calls roomOf asks
by a clause of its own that the code is there (foldFits and linFits do). "IN REAL ROWS" IS NOT "AT
REAL PLACES": a row of the table has 2 ^ placeBits places, placeBits the least a with ell ≤ 2 ^ a:
where the code's message length ell is no power of two the places from ell on are no entries of the
message, AND roomOf COUNTS THEM. What shuts that is lengthsFit (Johnson/Desc/Own/Lin.lean) of the
same codes. The shared chain's "LIN point" asks both of the record's codes. NOT EVERY CALLER DOES: a
caller that asks "n ≤ roomOf" without lengthsFit beside has that gap at its own place.
RoomPlaces.lean: room_places shows it. The program's vectorRoom has the same
gap.
What "n ≤ roomOf" means, and that roomOf is vectorRoom at all arguments, is proved beside, in
Johnson/Desc/Own/RoomMeans.lean, which no block imports.
No theorem here. Nothing on soundness.

-/
import Johnson.Desc.Own.Send
import OnBytes.Iop.Foldeq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

/-- The message can hold a vector in this layout. -/
def roomCan (codes : Codes) (s : OracleShape) (rowsHigh : Bool) : Bool :=
  let lay := vectorLay codes s rowsHigh
  (rowsHigh || s.mainRows == 2 ^ lay.rowBits) && decide (lay.bits ≤ 60) &&
    (s.answers == 0 || (padMade codes s).isSome)

/-- The least of m and the entries' numbers at the places of the pad that lie in the main table. -/
def belowPad (lay : VectorLay) (places : List PadPlace) (m : Nat) : Nat :=
  places.foldl (fun m p => if p.part == .main then min m (lay.entryAt p.index) else m) m

/-- The number of entries, from entry 0 on, in real rows and before every place of the pad. -/
def roomOf (codes : Codes) (s : OracleShape) (rowsHigh : Bool) : Nat :=
  let lay := vectorLay codes s rowsHigh
  if roomCan codes s rowsHigh then
    belowPad lay (if s.answers == 0 then [] else (padMade codes s).getD [])
      (s.mainRows * 2 ^ lay.placeBits)
  else 0

end VerifiableInference.Desc.Own
