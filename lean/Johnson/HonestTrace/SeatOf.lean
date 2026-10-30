-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/SeatOf.lean

In which oracle message's main rows an array of a later moment of a segment is laid: the seat of
that message, made of a description's public data, with tests on public data at the seat.
Definitions with code. No theorem.

The item "layout" of a proof's parameters lists, for each segment, its arrays; an array names the
oracle message of the segment into whose main rows it is placed, and its blocks say where each
element lies (docs/format/10-proof-file.md, R14.5; OnBytes/Params/Items.lean: LaidBlock, ReqArray).
NO ELEMENT's PLACE IN A TABLE IS RECKONED HERE, and no array's value.

Main definitions:
* "inSending L m": the moment of the segment's message number m, and its number among the messages
  of that moment.
* "Seat", "seatOf", "seatsOf", "seatAt": in which oracle message's main rows an array is laid: the
  segment, its messages and arrays, the array, its message's shape and length, the message's
  address, the number of rounds of the first chain in front of its sending.
* "seatWhy", "seatFits", "allSeated": THE TESTS ON PUBLIC DATA AT A SEAT. By this file's reckoning,
  with no theorem: under "seatFits" every element of the array has one place in the message's main
  rows, no place holds two elements, of this array or of another of the same message, and no
  element stands on the pad. They reject every layout at which "seatOf" would take the first of two
  arrays of the name, or a way back from a place OF THIS ARRAY the first of two arrays or of two
  blocks. Two other arrays of the message that share a place are not seen. NOT COVERED: two seats of
  one address ("seatAt" takes the first); two places or two steps of one name ("seatOf",
  "Pub.roundsBefore?" take the first).

THE MESSAGES COME BY MOMENT. A message's number in its sending is taken to be its number among the
segment's messages of its moment. That is its number in the list that the sending announces if the
segment's messages come by moment: the plan's own test "reqMomentsOk" (OnBytes/Iop/Req.lean), which
"seatWhy" asks.

"seatWhy" beside the plan's own test on a message's arrays, "Own.reqMessageLaid"
(Johnson/Desc/Own/Req.lean). By reading, at a code whose message length is a power of two that test
asks the eight tests of "seatWhy" on blocks, and more (each block's four first numbers are
multiples of its sides); it does not ask that the segment's layout has just one array of the name.
This file holds no theorem that compares the two.

Where the numbers come from. The sender of a segment's moment t is taken to be the segment's place
number t, from 0, among its places of the kinds K1 and K2, and the sending to be part 0 of the row
there: the rule of "sendersOf" and "sentBy" of Johnson/Desc/ProofFile/Honest/K2/Seat.lean, which is
imported for "sendersOf" alone. That file has a "seatOf" of its own (ProofFile.Honest.K2.seatOf: of an
address the segment and the message's number: what "pairOf" of Johnson/HonestTrace/RowOfArray.lean
yields off our seats); in this file "seatOf" is OnBytes.HonestTrace.seatOf throughout. The number of
rounds in front is "Pub.roundsBefore?" at the name of the first step of that place. No number of
rounds is typed; the part's number 0 is.

Limits. MOMENTS FROM 1 ON ALONE: in a segment's first sending other messages stand in front of the
segment's own, so a message's number there is not its number among the messages of its moment;
"seatOf" yields nothing for an array of moment 0. No test of this file holds the rule on senders
against a description's own list of sub-protocols, nor the number of rounds against "roundsInFront"
(Johnson/Desc/ProofFile/Honest/ForKinds.lean). A segment without a seat lays nothing, without a
word: "allSeated" rejects that. A law on a filling that is seated here will take "seatFits" as a
premise. The layout and the shape are read off G, the steps off Z: no test of this file holds that
the two belong together. "seatWhy" does not ask that the segment's first message is of moment 0.
Nothing on any property of the protocol.

Not claimed: anything on a prover, a verifier or a property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K2.Seat
import Johnson.Desc.ProofFile.Honest.RowData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.HonestTrace

open ProofFile (Pub Ground Spot spotsOf)
open ProofFile.Honest (Addr MsgAddr padInMain)
open ProofFile.Honest.K2 (sendersOf)
open OnBytes.Params (LaidBlock ReqArray ReqLink)

/-! ## In which oracle message's main rows an array is laid -/

/-- The moment of a segment's message number m, and its number among the messages of that
moment. -/
def inSending (L : ReqLink) (m : Nat) : Option (Nat × Nat) :=
  (L.messages[m]?).map fun M =>
    (M.moment, ((L.messages.take m).filter fun N => N.moment == M.moment).length)

/-- **In which oracle message's main rows an array is laid.** All fields are public data. -/
structure Seat where
  /-- the segment's number, from 0 -/
  seg : Nat
  /-- the segment's oracle messages, as the request's shape has them -/
  link : ReqLink
  /-- the segment's arrays, as the layout has them -/
  layout : List ReqArray
  /-- the array -/
  array : ReqArray
  /-- the shape of the oracle message that holds it -/
  shape : OnBytes.OracleShape
  /-- the message length of the code of its main rows -/
  ell : Nat
  /-- that message's address -/
  addr : MsgAddr
  /-- how many rounds of the first chain stand in front of its sending -/
  heard : Nat

/-- The seat of the array of a name at a segment. sps: the first chain's places. Nothing where the
segment has no such array, where its message is of moment 0, or where a code, a place or a step
lacks. -/
def seatOf (Z : Pub) (G : Ground) (sps : List Spot) (name : String) (seg : Nat) : Option Seat := do
  let layout := G.first.layout.link.getD seg []
  let a ← layout.find? fun a => a.name == name
  let L ← G.first.shape.link[seg]?
  let M ← L.messages[a.message]?
  let x ← inSending L a.message
  let code ← G.first.codes.base[M.shape.code]?
  if x.1 == 0 then none
  else
    let pl ← (sendersOf sps seg)[x.1]?
    let sp ← sps.find? fun sp => sp.place == pl
    let c ← sp.cuts.head?
    let n ← Z.roundsBefore? c.look
    pure ⟨seg, L, layout, a, M.shape, code.ell, ⟨⟨pl, 0⟩, x.2⟩, n⟩

/-- The seats of the array of a name at all segments that have one. -/
def seatsOf (Z : Pub) (G : Ground) (name : String) : List Seat :=
  match spotsOf Z.cuts with
  | some sps => (List.range G.first.shape.link.length).filterMap (seatOf Z G sps name)
  | none => []

/-- The seat with an address. -/
def seatAt (seats : List Seat) (a : MsgAddr) : Option Seat := seats.find? fun s => s.addr == a

/-! ## The tests on public data at a seat -/

/-- Two stretches of numbers, each by its first number and its length, have no number in common. -/
def stretchesApart (a n b m : Nat) : Bool := decide (a + n ≤ b) || decide (b + m ≤ a)

/-- Two blocks' rectangles in a message's table have no place in common. -/
def tablesApart (B C : LaidBlock) : Bool :=
  stretchesApart B.firstRow (2 ^ B.rowBits) C.firstRow (2 ^ C.rowBits) ||
    stretchesApart B.firstPlace (2 ^ B.placeBits) C.firstPlace (2 ^ C.placeBits)

/-- Two blocks of one array have no element in common. -/
def elementsApart (B C : LaidBlock) : Bool :=
  stretchesApart B.firstI (2 ^ B.bitsI) C.firstI (2 ^ C.bitsI) ||
    stretchesApart B.firstC (2 ^ B.bitsC) C.firstC (2 ^ C.bitsC)

/-- A test on every pair of different members of a list. -/
def pairwise {α : Type} (f : α → α → Bool) : List α → Bool
  | [] => true
  | x :: l => l.all (f x) && pairwise f l

/-- A block's rectangle holds the place j of main row r. -/
def holds (B : LaidBlock) (r j : Nat) : Bool :=
  decide (B.firstRow ≤ r) && decide (r < B.firstRow + 2 ^ B.rowBits) &&
    decide (B.firstPlace ≤ j) && decide (j < B.firstPlace + 2 ^ B.placeBits)

/-- **Why a seat does not fit**; nothing if it does. -/
def seatWhy (s : Seat) : Option String :=
  let bs := s.array.blocks
  let others := (s.layout.filter fun a =>
    a.message == s.array.message && a.name != s.array.name).flatMap (·.blocks)
  if !OnBytes.reqMomentsOk 0 s.link.messages then
    some "the seat: the segment's messages do not come by moment"
  else if (s.layout.filter fun a => a.name == s.array.name).length != 1 then
    some "the seat: the segment's layout has not just one array of the name"
  else if !bs.all fun B => B.rowBits + B.placeBits == B.bitsI + B.bitsC then
    some "the seat: a block's rectangle has not as many places as the block has elements"
  else if !bs.all fun B => decide (B.firstI + 2 ^ B.bitsI ≤ s.array.sizeI) &&
      decide (B.firstC + 2 ^ B.bitsC ≤ s.array.sizeC) then
    some "the seat: a block is not inside its array"
  else if !pairwise elementsApart bs then some "the seat: two blocks hold one element"
  else if (bs.map fun B => 2 ^ (B.bitsI + B.bitsC)).sum != s.array.sizeI * s.array.sizeC then
    some "the seat: the blocks do not hold every element of the array"
  else if !bs.all fun B => decide (B.firstRow + 2 ^ B.rowBits ≤ s.shape.mainRows) &&
      decide (B.firstPlace + 2 ^ B.placeBits ≤ s.ell) then
    some "the seat: a block is not inside the message's main rows"
  else if !pairwise tablesApart bs then some "the seat: two blocks of the array share a place"
  else if !bs.all fun B => others.all (tablesApart B) then
    some "the seat: a block shares a place with a block of another array of the message"
  else if !(padInMain s.ell s.shape).all fun p =>
      bs.all fun B => !holds B p.1 p.2 then
    some "the seat: an element stands on the pad"
  else none

/-- **The test on public data at a seat.** -/
def seatFits (s : Seat) : Bool := (seatWhy s).isNone

/-- Each of the n segments of the first chain has a seat, in order. n: the number of segments, as
the request's shape has it (G.first.shape.link.length). -/
def allSeated (n : Nat) (seats : List Seat) : Bool := seats.map (·.seg) == List.range n

end OnBytes.HonestTrace
