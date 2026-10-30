-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Carrying.lean: the honest prover of the code switch between two segments:
WHAT THE MAIN ROWS OF ITS ORACLE MESSAGES HOLD. The kind's text: Johnson/Top/H0/Tw/K2C/Kind.lean.
This file defines part of the honest prover. Definitions with code; no theorem. It hangs on no
frame: no coin, no round and no challenge is typed here.

What a switch sends (OnBytes/Iop/Cs.lean, first section; OnBytes/Iop/Req.lean, `first` and
`finish`). One prover's message holds, in this order: the carrying message g; a fresh copy of each
kept member of the group that was closed; the next segment's own oracle messages of moment 0; the
fresh mask of the next fold. Of these, three sorts have main rows, and this file says what stands in
them, but for the pads:
  g          the folded main row's message in one block of rows; in a second block "the rest": the
             messages of the old and the fresh mask row, the tail of the folded main row, the tails
             of the kept rows, the tails of the two mask rows, the kept members' old pads. Between
             two segments the entries that these leave free are 0
  a copy     the kept member's main table as it was sent before
  an own message   what the caller says
At the places of a message's pad nothing is said here: whoever encodes the message lays the pad
there, and what these functions return at such a place is not meant to be read. Tails, pads and
mask rows of the NEW messages are coins, and no matter of this file.

  `Held`       main rows in full, with their tails, as a prover holds them
  `Left`       what the fold that closed a group leaves with the prover
  `Sizes`      what is public at a switch, as far as these functions read it; `Sizes.serves`
  `rest`       the rest, as one list, in the order of `switchParts` (OnBytes/Iop/Cs.lean)
  `numberIn`   the number that an entry has in a block of rows: the inverse of `cutIndex`
  `carrying`, `carryingAt`   g's two tables, by row and place; by index. General in the target; what
               stands in the free room is an argument
  `mainRows`   the main rows of the message number k of a sending between two segments

Elements. All entries are typed in the extension field. An entry of a row over the base field is
that element with two zeros behind it, and whoever encodes such a row reads the first coordinate.

Limits. `mainRows` serves a target whose rest lies in MAIN rows (`Sizes.serves`), as every target
between two segments and in front of the last proximity test does (`reqGroupAt`,
OnBytes/Iop/Req.lean). A switch inside a proximity test lays the rest in mask rows and fills the
free room with sampled elements: `carrying` is typed for that too, and no function here calls it
so. Nothing holds `Sizes` against a statement; that `rest` has the
order and the lengths of `switchParts`, and that `numberIn` undoes `cutIndex` and
`SwitchPlaces.get`, is not shown here. Nothing on soundness, completeness or any other property.

-/
import OnBytes.Iop.Cs
import OnBytes.Slice.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes

/-- The field's 0, written so that it has code. -/
def zeroG : Cb.Gl.E := OnBytes.Slice.toE (0, 0, 0)

/-- **Main rows in full**, as a prover holds them. -/
structure Held where
  /-- the entry in row b at place j of the row's message, a pad's entries among them -/
  main : Nat → Nat → Cb.Gl.E
  /-- entry q of row b's tail -/
  tail : Nat → Nat → Cb.Gl.E

/-- The entry at an index of the main table of a message of the shape s: the row's number is in the
low bits of the index. -/
def Held.entry (H : Held) (s : OracleShape) (index : Nat) : Cb.Gl.E :=
  H.main (index % 2 ^ ceilLog2 s.mainRows) (index / 2 ^ ceilLog2 s.mainRows)

/-- **What the fold that closed a group leaves with the prover**: the rows of the complex of single
rows (`SingleRows`, OnBytes/Iop/Fold.lean), each as a message and a tail. -/
structure Left where
  /-- the folded main row's message -/
  main : Nat → Cb.Gl.E
  /-- its tail -/
  mainTail : Nat → Cb.Gl.E
  /-- the message of mask row j: 0 the fold of the group's mask rows, 1 that of the fresh mask's -/
  mask : Nat → Nat → Cb.Gl.E
  /-- the tail of mask row j -/
  maskTail : Nat → Nat → Cb.Gl.E
  /-- the kept member number i, in the order of sending: as it was sent -/
  kept : Nat → Held

/-- **What is public at a switch**, as far as the main rows hang on it. -/
structure Sizes where
  codes : Codes
  /-- the closed group's main code and mask code, by their numbers in the lists -/
  code : Nat
  maskCode : Nat
  /-- the shapes of the closed group's kept members, in the order of sending. In a request's chain
  of segments a member's copy has the member's own shape (`reqGroupAt`, OnBytes/Iop/Req.lean) -/
  kept : List OracleShape
  /-- where the switch leads -/
  target : SwitchTarget

/-- `mainRows` serves the place: the rest lies in main rows, and there is a target for each kept
member. -/
def Sizes.serves (Z : Sizes) : Bool :=
  Z.target.rest.part == .main && Z.target.main.part == .main &&
    Z.target.kept.size == Z.kept.length

/-- **The rest**, as one list. -/
def rest (Z : Sizes) (W : Left) : List Cb.Gl.E :=
  let c := Z.codes.base.getD Z.code default
  let zk := Z.codes.mask.getD Z.maskCode default
  ((List.range 2).flatMap fun j => (List.range zk.ell).map (W.mask j)) ++
    (List.range c.r).map W.mainTail ++
    (Z.kept.zipIdx.flatMap fun x =>
      (List.range x.1.mainRows).flatMap fun b => (List.range c.r).map ((W.kept x.2).tail b)) ++
    ((List.range 2).flatMap fun j => (List.range zk.r).map (W.maskTail j)) ++
    Z.kept.zipIdx.flatMap fun x =>
      (padPlaces Z.codes x.1).map fun p => (W.kept x.2).entry x.1 p.index

/-- The number, in the order in which a block of rows is filled, of the entry in row b at place j;
nothing if the row is not in the block. -/
def numberIn (cut : RowCut) (b j : Nat) : Option Nat :=
  if decide (cut.firstRow ≤ b) && decide (b < cut.firstRow + 2 ^ cut.bits) then
    some (b - cut.firstRow + j * 2 ^ cut.bits)
  else none

/-- **The carrying message's two tables**: table, row b, place j. The rest steps over the pad's
entries, as `SwitchPlaces.get` does. free: what stands where neither vector has an entry; it is
asked at the pad's places too, where its value is not meant to be read. -/
def carrying (Z : Sizes) (W : Left) (free : Part → Nat → Nat → Cb.Gl.E) :
    Part → Nat → Nat → Cb.Gl.E :=
  let ell := (Z.codes.base.getD Z.code default).ell
  let pad := (SwitchPlaces.make Z.codes Z.target).pad
  let v := (rest Z W).toArray
  fun part b j =>
    match (if part == .main then numberIn Z.target.main b j else none) with
    | some n => if n < ell then W.main n else free part b j
    | none =>
      match (if part == Z.target.rest.part then numberIn Z.target.rest b j else none) with
      | some n =>
        let i := n - (pad.filter (· < n)).length
        if pad.contains n || decide (v.size ≤ i) then free part b j else v.getD i zeroG
      | none => free part b j

/-- The same by the table's index: the row's number in the low bits. -/
def carryingAt (Z : Sizes) (W : Left) (free : Part → Nat → Nat → Cb.Gl.E) (part : Part)
    (index : Nat) : Cb.Gl.E :=
  carrying Z W free part (index % 2 ^ switchRowBits Z.target part)
    (index / 2 ^ switchRowBits Z.target part)

/-- **The main rows of the message number k of a sending between two segments**, in the order in
which the switch announces them. The carrying message's free room holds 0. own: the next segment's
own messages of moment 0, by their number among these. A message without main rows (the fresh mask)
is handed whatever `own` returns there: it is not read. -/
def mainRows (Z : Sizes) (W : Left) (own : Nat → Nat → Nat → Cb.Gl.E) (k : Nat) :
    Nat → Nat → Cb.Gl.E :=
  if k == 0 then carrying Z W (fun _ _ _ => zeroG) .main
  else if k ≤ Z.kept.length then (W.kept (k - 1)).main
  else own (k - 1 - Z.kept.length)

end VerifiableInference.Desc.K2.Honest
