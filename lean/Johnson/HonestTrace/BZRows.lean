-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/BZRows.lean

The array BZ of a segment's smallness test as data of the main rows of the oracle message that holds
it: its values as the structure ArrayVals (Johnson/Desc/ProofFile/Honest/LaidData.lean), and the
filling of the structure RowData (Johnson/Desc/ProofFile/Honest/RowData.lean) that laidData makes of
them: it lays BZ alone, at every segment. Definitions with code. No theorem.

The values and the two tests on them are Johnson/HonestTrace/BZVals.lean's. The seats are
Johnson/HonestTrace/SeatOf.lean's (Seat, seatsOf, seatFits, allSeated); laidRows is
Johnson/HonestTrace/RowOfArray.lean's. The way from (main row, place) to the array's (row, column)
is laidData's. This file joins them and types none.

Main definitions:
* "bzValsAt at_": THE VALUES AS ArrayVals, of each segment's BzAt. "bzFitsOne at_ s", "bzFitsAt
  seats at_": seatFits and BzAt.fits at a seat; at every seat. "bzWithFits seats at_ D": D with
  bzFitsOne laid into its field ready.
* "bzVals Z G mats", "bzRows Z G mats", "bzFits Z G mats": the values, the filling and the test off
  a description's public part Z and the segments' plans G. mats is a parameter: no definition here
  makes it.

Which message. At the two examples' layout files ZZ and BZ lie in one oracle message, so the two
have one address. This filling lays BZ's places alone; it is meant to be joined with a filling of ZZ
by RowData.over, not by RowData.join.

Limits. Those of the files that it joins. At a segment that has no BzAt nothing is laid; the test on
what was heard rejects there, and bzFitsAt if the segment has a seat. ArrayVals.ready goes by the
segment alone: so the seats that are handed to laidData with these values must be of BZ's message
alone, as in bzRows: at an earlier message's address "ready" would reject, though nothing of BZ is
laid there. This file holds no #guard. Johnson/HonestTrace/BZRowsToy.lean runs bzValsAt under
laidData, bzWithFits over it, and bzFitsAt. bzRows and bzFits, which want a description's public
part, are evaluated, on public data alone, in
Johnson/HonestTrace/BZRowsAtSmall.lean. At a seat's address bzRows' field ready asks layFits and
that seat's share of bzFits (seatFits, BzAt.fits, msgFits): not the other seats', and not allSeated:
a segment without a seat has no address at which it could reject. A law on bzRows is to take bzFits,
and RowData.readyAt at the address, as premises.

Not claimed: that a prover's program sends these entries; that a verifier accepts them; completeness
of the protocol; anything on what the entries reveal.
-/
import Johnson.HonestTrace.RowOfArray
import Johnson.HonestTrace.BZVals

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open ProofFile (Pub Ground)
open ProofFile.Honest (RowData ArrayVals msgFits layFits)

/-- **BZ's values as ArrayVals**, of each segment's public data. It has the array "BZ" alone, at the
segments that have such data: 32 rows and the plan's number of columns. At a segment without such
data it has no array, and the test on what was heard rejects. "val" DOES NOT READ THE NAME: under
any name it yields BZ's formula, and 0 at a segment without such data; "size" is what keeps both
from being laid. "ready" GOES BY THE SEGMENT ALONE: hand laidData, with these values, seats of the
message that holds BZ alone; at the address of an earlier message of the segment it would reject.
ITS "ready" ASKS NO TEST ON A SEAT AND NONE ON PUBLIC DATA (seatFits, BzAt.fits): bzRows lays these
into the filling's. As at zzOf (Johnson/Desc/ProofFile/Honest/K8/Digits.lean): "This is the array
before encoding: which part sends it, with which coins, is not said here." -/
def bzValsAt (at_ : Nat → Option BzAt) : ArrayVals :=
  { size := fun seg name =>
      if name == "BZ" then (at_ seg).map fun b => (32, b.tl.bzColumns) else none
    val := fun R heard seg _ =>
      match at_ seg with
      | some b => let v := b.entry R.cells heard; fun i c => .inl (v i c)
      | none => fun _ _ => .inl (OnBytes.Slice.toF 0)
    ready := fun heard seg => (at_ seg).any fun b => b.ready heard }

/-- **The test on public data at one seat**: the seat passes seatFits, its segment has its public
data, and these pass BzAt.fits. -/
def bzFitsOne (at_ : Nat → Option BzAt) (s : Seat) : Bool :=
  seatFits s && (at_ s.seg).any fun b => b.fits s.heard s.array.sizeI s.array.sizeC

/-- **The test on public data at all seats**: bzFitsOne at each. -/
def bzFitsAt (seats : List Seat) (at_ : Nat → Option BzAt) : Bool := seats.all (bzFitsOne at_)

/-- **A filling with the test on public data laid into its field ready**: at a seat's address
"ready" also asks bzFitsOne at that seat. At an address that is no seat's nothing turns. -/
def bzWithFits (seats : List Seat) (at_ : Nat → Option BzAt) (D : RowData) : RowData :=
  let fit := seats.map fun s => (s.addr, bzFitsOne at_ s)
  { D with ready := fun h a => D.ready h a && (fit.find? fun x => x.1 == a).all (·.2) }

/-- **THE VALUES**, off a description's public part and the segments' plans. As at zzOf
(Johnson/Desc/ProofFile/Honest/K8/Digits.lean): "This is the array before encoding: which part sends
it, with which coins, is not said here." mats is a parameter, which nothing here ties to matsOf
(Johnson/HonestTrace/DigitsAtTrace.lean): "the entries are the trace's only at mats := matsOf X k
(cellsAtOf_matsOf)". -/
def bzVals (Z : Pub) (G : Ground) (mats : Nat → List (Nat × String × Nat)) : ArrayVals :=
  bzValsAt (bzAtOf Z G mats)

/-- **THE FILLING**: the values, laid by laidData at the seats of "BZ", with bzFitsOne laid into the
field ready (bzWithFits). At a seat's address "ready" asks: layFits and msgFits (laidData's);
BzAt.ready; seatFits and BzAt.fits. These are the rows' data before encoding: with which coins they
are encoded is not said here; the address is the seat's (Johnson/HonestTrace/SeatOf.lean). mats is a
parameter, which nothing here ties to matsOf (Johnson/HonestTrace/DigitsAtTrace.lean): "the entries
are the trace's only at mats := matsOf X k (cellsAtOf_matsOf)". -/
def bzRows (Z : Pub) (G : Ground) (mats : Nat → List (Nat × String × Nat)) : RowData :=
  bzWithFits (seatsOf Z G "BZ") (bzAtOf Z G mats) (laidRows G (seatsOf Z G "BZ") (bzVals Z G mats))

/-- **The test on public data beside it**: every segment has a seat; the layout has as many lists of
arrays as the shape has segments (layFits); bzFitsAt accepts; at every seat the plan's own test on
the message's arrays (msgFits) accepts. mats is a parameter, which nothing here ties to matsOf
(Johnson/HonestTrace/DigitsAtTrace.lean): "the entries are the trace's only at mats := matsOf X k
(cellsAtOf_matsOf)". -/
def bzFits (Z : Pub) (G : Ground) (mats : Nat → List (Nat × String × Nat)) : Bool :=
  allSeated G.first.shape.link.length (seatsOf Z G "BZ") &&
    layFits G.first.shape G.first.layout && bzFitsAt (seatsOf Z G "BZ") (bzAtOf Z G mats) &&
    (seatsOf Z G "BZ").all fun s =>
      msgFits G.first.codes G.first.shape G.first.layout s.seg s.array.message

end OnBytes.HonestTrace
