-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/RowOfArray.lean

From the values of arrays of a later moment to the main rows of the oracle messages that hold them:
the one call of "laidData" (Johnson/Desc/ProofFile/Honest/LaidData.lean) at the seats of
Johnson/HonestTrace/SeatOf.lean. Definitions with code. No theorem.

NO PLACE OF A TABLE IS RECKONED HERE. Beside the codes, the shape and the layout, "laidData" takes
two public parameters: of a message's address the segment and the message's number in the segment's
list, and the number of challenges heard when its sending begins. This file makes these two of a
list of seats.

Main definitions:
* "pairOf seats", "heardOf seats": the two parameters.
* "laidRows G seats V": THE CALL.
* "mineOf seats": the addresses of the seats, for "RowData.join". WHERE TWO ARRAYS LIE IN ONE
  MESSAGE IT IS TRUE OF THE WHOLE ADDRESS: such fillings are joined by place ("RowData.over").

Limits. At an address that is no seat's "pairOf" yields nothing, so nothing is laid there, "heardOf"
is 0 AND "RowData.readyAt" ACCEPTS: it is no test that an address is a seat's ("mineOf" is).
"laidRows" reads codes, shape and layout off G and of a seat the segment, the array's message, the
address and the number of rounds alone: no test of this file holds that the seats were made off
that G. Nothing on any property of the protocol.

Not claimed: anything on a prover, a verifier or a property of the protocol.
-/
import Johnson.HonestTrace.SeatOf
import Johnson.Desc.ProofFile.Honest.LaidData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.HonestTrace

open ProofFile (Ground)
open ProofFile.Honest (MsgAddr RowData ArrayVals laidData)

/-- The addresses of the seats. -/
def mineOf (seats : List Seat) (a : MsgAddr) : Bool := (seatAt seats a).isSome

/-- Of a seat's address: the segment, and the message's number in the segment's list. -/
def pairOf (seats : List Seat) (a : MsgAddr) : Option (Nat × Nat) :=
  (seatAt seats a).map fun s => (s.seg, s.array.message)

/-- Of a seat's address: how many challenges have been heard when the sending begins; 0 at an
address that is no seat's. -/
def heardOf (seats : List Seat) (a : MsgAddr) : Nat := ((seatAt seats a).map (·.heard)).getD 0

/-- **The data of the main rows of the seats' messages**, of the arrays' values. These are the rows'
data before encoding: with which coins they are encoded is not said here; the address is the seat's
(Johnson/HonestTrace/SeatOf.lean). -/
def laidRows (G : Ground) (seats : List Seat) (V : ArrayVals) : RowData :=
  laidData G.first.codes G.first.shape G.first.layout (pairOf seats) (heardOf seats) V

end OnBytes.HonestTrace
