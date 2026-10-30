-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/ZzData.lean: the honest side of the smallness test (K8): THE ARRAY
OF DIGITS ZZ AS ONE `ArrayVals` (Johnson/Desc/ProofFile/Honest/LaidData.lean), and the filling of
`RowData` (Johnson/Desc/ProofFile/Honest/RowData.lean) that `laidData` makes of it: the data of the
main rows of the oracle message that bears ZZ, as a function of the witness's cells, of what was
heard, and of the message's address. It defines part of the honest prover. Definitions with code; no
theorem. Tests at a toy: Johnson/Desc/ProofFile/Honest/K8/ZzDataToy.lean [not in this library; so
here read: not tested in this library].

The element is `zzOf` (Honest/K8/Digits.lean). WHERE IT STANDS IN THE MESSAGE's ROWS IS NOT TYPED
HERE: that is `laidData`'s way back off the public item "layout". The drawn matrix is read off the
challenges heard at the number of the segment's round "RNG" (`drawnAt`, Honest/K2/Rounds.lean).
  `ZzPub`           PUBLIC DATA, as letters: `tl`: the plan's state of the test, by segment ·
                    `mats`: for each matrix of a segment's list its owner's segment, its name
                    there, its first column there · `rng`: the numbers of the rounds "RNG", by
                    segment
  `columnsOf`       the columns of all matrices of a segment's list
  `zzVals`          THE VALUES. `size`: under the name "ZZ" alone: tau rows, and twice the rows of
                    cells of all matrices as columns (`allRows`, Johnson/Desc/K8/Honest/Window.lean:
                    the number by which `zzOf` counts) · `val`: `zzOf`, of the base field; of the
                    readers it reads the cells alone · `ready`: see below
  `bearsZz`         a seat cut to the messages in which the layout lays the array "ZZ"
  `zzData`          THE FILLING: `laidData` at that cut seat. `seat` (an address ↦ the segment and
                    the message's number in the segment's list) IS A LETTER, of the type that
                    `laidData` takes. AT A MESSAGE THAT BEARS NO ZZ IT SAYS NOTHING, whatever the
                    seat names: `heardAt` 0, `lays` no, `ready` yes: so that a join by place
                    (`RowData.over`) asks of that message's sender nothing on ZZ's account. At
                    the message that bears ZZ `heardAt` is the number of the segment's round
                    "RNG" plus 1: all that `val` reads of what was heard
  `zzSeated`        A PUBLIC TEST BESIDE THE FILLING, for the seat: see below
  `zzPubOf`, `zzDataAt`   the public data, and the filling, off the ground
NO STAND-IN VALUE GOES UNMARKED. `ready` says no: where the plan's state lacks (nothing is laid
then) · where the segment's round lacks or has not been heard · where it drew another number of
entries than the matrices' columns times tau · where the list `mats` has another length than the
state's list · where the layout's "ZZ" has another shape than ZZ (`ArrayVals.inside`) · where the
message's arrays fail the plan's own test, among it that the laid blocks lie inside their arrays and
cover them (`msgFits`: nothing is laid then) · where the layout has not one list of arrays for each
segment of the shape (`layFits`), at an address that still bears ZZ. ONE MISFIT THE FILLING CANNOT
MARK, SINCE THE SEAT IS CUT BY THE LAYOUT ITSELF: a layout that has no "ZZ" for a segment whose plan
has a state of the test (a layout that ends in front of the segment among them): there no address
bears ZZ, and `ready` says yes everywhere. `zzSeated` is the test with code on public data that says
no there, AT THE SEGMENTS OF THE SHAPE ALONE: A PREMISE AT THE SEAT.
READ IT THROUGH `RowData.at_` ALONE, as `laidData`'s head says. What stands where the layout lays
nothing, and the format's rule for it: that head.
BZ lies in the same oracle message wherever the layout says so; it is another writer's `ArrayVals`:
the two fillings are joined by `RowData.over`, and `RowData.apart` tests that no place is laid
twice.
Limits. `seat` and `mats` are letters: nothing holds them against the format's pages. BZ is not
laid. NOTHING HERE TIES THE NUMBER OF SEGMENTS AT WHICH THE PLAN HAS A STATE (at `zzPubOf`: the
ground's built segments) TO THE SHAPE's COUNT: beyond that count `zzSeated` asks nothing. `zzPubOf`
takes the rounds named "RNG" in the chain's order: entry l of `rng` is segment l's round only where
each segment up to l has just one such round: not held here.
That one challenge stands in the list for each round of the chain, and that no round lies
between the round "RNG" and the sending, is not held against the table of steps: so neither that
`heardAt` is the number of rounds in front of the sending as whoever pays the seat counts it.
`ready` does not ask that the drawn entries are -1, 0 or 1. The entries give a combination back only
where it lies in its window (Johnson/Desc/K8/Honest/DigitsLaw.lean). That `allRows` is the state's
mz: Honest/K8/AddressLaw.lean, `mz_allRows`, under its premise. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.LaidData
import Johnson.Desc.ProofFile.Honest.K2.Rounds
import Johnson.Desc.ProofFile.Honest.K8.Digits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes.Params (ReqLayout ReqShape)
open OnBytes.Slice (toF)
open ProofFile.Honest.K2 (drawnAt roundNumbers)
open VerifiableInference.Desc.First.K8.Honest (allRows)

/-- Public data, as letters. -/
structure ZzPub where
  /-- the plan's state of the smallness test at a segment -/
  tl : Nat → Option OnBytes.Model.HTailF2
  /-- for each matrix of a segment's list: its owner's segment, its name there, its first column -/
  mats : Nat → List (Nat × String × Nat)
  /-- the numbers, among the chain's rounds, of the rounds "RNG": read as: entry l is segment l's -/
  rng : List Nat

/-- The columns of all matrices of a segment's list. -/
def columnsOf (tl : OnBytes.Model.HTailF2) : Nat := (tl.mats.toList.map (·.k)).sum

/-- **THE VALUES.** These are the main rows' data before encoding: which part sends them, with which
coins, is not said here. At a name in mats that is no label the cells are what the reader yields
there. -/
def zzVals (Z : ZzPub) : ArrayVals :=
  { size := fun l name =>
      if name == "ZZ" then (Z.tl l).map fun tl => (tl.tau, 2 * allRows (parOfTail tl)) else none
    val := fun R heard l name i c =>
      match name == "ZZ", Z.tl l, (drawnAt Z.rng heard l).toOption with
      | true, some tl, some t => .inl (zzOf tl (Z.mats l) R.cells t i c)
      | _, _, _ => .inl (toF 0)
    ready := fun heard l =>
      (Z.tl l).any fun tl =>
        (Z.mats l).length == tl.NM &&
          (drawnAt Z.rng heard l).toOption.any fun t => t.length == columnsOf tl * tl.tau }

/-- A seat cut to the messages in which the layout lays the array "ZZ". -/
def bearsZz (lay : ReqLayout) (seat : MsgAddr → Option (Nat × Nat)) (a : MsgAddr) :
    Option (Nat × Nat) :=
  (seat a).filter fun x => (lay.link.getD x.1 []).any fun y => y.name == "ZZ" && y.message == x.2

/-- **THE FILLING.** Where the plan's state lacks, `inside` is true by emptiness (the values have no
array then) and it is the values' own `ready` that says no. WHOEVER SEATS THIS FILLING NAMES
`zzSeated` AS A PUBLIC PREMISE: without it a law on what the sending holds can hold emptily.
A TERM, to the letter: "zzSeated BY NAME, AND BESIDE IT A PUBLIC PREMISE
THAT TIES THE TWO COUNTS (no state of the test at a segment number at or beyond the shape's count:
at zzPubOf: the ground's built segments are as many as the shape's), wherever zzData | zzDataAt is
seated". -/
def zzData (codes : OnBytes.Codes) (s : ReqShape) (lay : ReqLayout)
    (seat : MsgAddr → Option (Nat × Nat)) (Z : ZzPub) : RowData :=
  let base := laidData codes s lay (bearsZz lay seat)
    (fun a =>
      match (bearsZz lay seat a).bind fun x => Z.rng[x.1]? with
      | some n => n + 1
      | none => 0)
    (zzVals Z)
  { base with
    ready := fun heard a =>
      base.ready heard a && (bearsZz lay seat a).all fun x => (zzVals Z).inside lay x.1 }

/-- **A public test beside the filling**, for the seat: the layout has a list of arrays for each
segment of the shape (`layFits`); and each segment OF THE SHAPE (each number below the shape's count
of segments) at which the plan has a state of the test has, among the addresses handed in, one whose
message bears "ZZ". WHAT THE FILLING CANNOT SAY ADDRESS BY ADDRESS: where this fails for a segment,
no address bears its ZZ, `lays` says no and `ready` says yes everywhere: all of that segment's
digits would be lost in silence. NOT ASKED: a segment number at or beyond the shape's count: if the
plan has a state there the test still says yes, and that segment's digits are lost in silence. -/
def zzSeated (s : ReqShape) (lay : ReqLayout) (seat : MsgAddr → Option (Nat × Nat)) (Z : ZzPub)
    (addrs : List MsgAddr) : Bool :=
  layFits s lay && (List.range s.link.length).all fun l =>
    (Z.tl l).isNone || addrs.any fun a => (bearsZz lay seat a).any (·.1 == l)

/-- The public data off the ground. D: the chain's rounds. -/
def zzPubOf (G : Ground) (D : List Fmt.DeclaredRound) (mats : Nat → List (Nat × String × Nat)) :
    ZzPub :=
  { tl := fun seg => (G.built[seg]?).map (·.tl), mats := mats, rng := roundNumbers D "RNG" }

/-- The filling off the ground. Whoever seats it names `zzSeated` as a public premise, as at
`zzData`.
A TERM, to the letter: "zzSeated BY NAME, AND BESIDE IT A PUBLIC PREMISE
THAT TIES THE TWO COUNTS (no state of the test at a segment number at or beyond the shape's count:
at zzPubOf: the ground's built segments are as many as the shape's), wherever zzData | zzDataAt is
seated". -/
def zzDataAt (G : Ground) (D : List Fmt.DeclaredRound) (seat : MsgAddr → Option (Nat × Nat))
    (mats : Nat → List (Nat × String × Nat)) : RowData :=
  zzData G.first.codes G.first.shape G.first.layout seat (zzPubOf G D mats)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.ZzPub
#print axioms ProofFile.Honest.K8.columnsOf
#print axioms ProofFile.Honest.K8.zzVals
#print axioms ProofFile.Honest.K8.bearsZz
#print axioms ProofFile.Honest.K8.zzData
#print axioms ProofFile.Honest.K8.zzSeated
#print axioms ProofFile.Honest.K8.zzPubOf
#print axioms ProofFile.Honest.K8.zzDataAt
