-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/SmallPlaces.lean: six small example places of the honest sender, with executable
checks of the sender and its simulator against values written by hand from the small examples of the
general model. This head also defines the terms of all examples and tests under
Johnson/SendSim/At/.
Terms: Johnson/SendSim/At/Sim.lean; for the examples and tests, the paragraph "Terms" below. Limits
of the folder: Johnson/SendSim/Defs.lean.

What this file has. Definitions and #guard checks; no theorem. The following is checked by #guard
when the file is compiled, (1) to (5) at each of the six places listed under "The places".
  (1) The job fits its place (sendFits). K1's test on the plan accepts (K1.planOk: every oracle
      message has an admitted shape, the trees can be made, and some oracle message is sampled). The
      sender's number of coins (dueR) is 3, 4, 4, 6, 5, 7 coins of the extension field, the counts
      of the matching examples of the general model (matched by inspection). Each place has one tree
      and one seed, of two coordinates and a factor.
  (2) Which coin is placed where (coinNumbers): with coin number i set to the value i + 1 and no
      data, each tail and each entry holds the expected number. The expected numbers are written by
      hand from the description of the matching example.
  (3) At concrete coins, seeds and queried positions the simulator (sendSim) outputs exactly shownR
      at no data (tellsOk). The honest sender (sendPart), executed by the framework's play at
      concrete data, discloses exactly shownR at these data (showsOk). At placePadAlone 1 the two
      values are checked to differ.
  (4) The same at a side whose sub-protocol is K1.send and whose row is the sender with its
      simulator (sideOk). This checks at concrete values what Spec.showsAt and Spec.tellsAt state
      for Seated sides; this file does not prove that the side is Seated. One case is a job that
      does not fit its place, a table sent along at a sampled oracle message: there both outputs are
      the error value. The concrete challenge is one that the side's rounds can sample (drawsFit);
      with the factor 0 it is not.
  (5) Formulas. At concrete data, shownR has for each row the symbol written by hand from the
      matching example: the tail, then powers of the point times the row's message, at the
      position's evaluation point in the row's own code. With the seed (z₀, z₁, β), its answer has
      the weights (1 - z₁)(1 - z₀) and (1 - z₁) z₀ on the two data entries, z₁ (1 - z₀) on the free
      entry and β on the pad. At placePadAndRider the row that is sent along holds its three coins
      in the order second, third, first, then 0, and the answer does not read that row.
  (6) A mask row is read at the position modulo the number of positions of its own code. The
      positions 1 and 5 have one point in a code of 4 positions and two points in a code of 8, so
      they give one mask symbol and two main symbols.
  (7) The checks can fail. Seven of them are repeated with one thing modified, and the two sides
      then differ: the order of the three coins, a weight, two coins exchanged, the mask row's
      point, the tail's position in the symbol, the pad's weight, two coins' numbers exchanged.

Limits.
The checks are evaluations at concrete values; no distribution is named. Each uses one family of
coins, data and seeds, and lists of at most three queried positions.
The expected values were written by the same hand as the small examples with which they are
compared, so they are not an independent check.
That the rows, coins, symbols and answer of a small example of the general model are those of the
honest sender at the place of the matching name is by inspection, not proved.

Terms.
  small example place   a concrete P : K1.Par (the public parameters of one sending), made by
                 smallPar, with a concrete ride. The numbers are synthetic. None is a place of the
                 release's protocol.
  small example book   a concrete Book for such a place (bookWith,
                 Johnson/SendSim/At/FilledBooks.lean). None is a book of the release's protocol.
  code           written (a, l, r): 2 ^ a positions, a message of l entries, a tail of r entries.
  concrete       given as a closed Lean term. A statement "at concrete constants" has no premise
                 left; its name often has the word closed.
  negative test  a theorem that the equation of a main statement is false, mostly at a small example
                 at which one premise is violated. A companion of a negative test, where there is
                 one, is a theorem that the other premises hold there. Parameter values at which the
                 equation may still
                 hold are excluded by premises of the test.
  modified sender   a sender with a map on the coins applied before shownR:
                 a coin is set to 0,
                 or one coin is used in two places.
  differ, false  "the two distributions differ", "the equation is false": one distribution can take
                 a value that the other cannot. Nothing says how far the
                 two distributions are from each other.
  control        a case that differs from a negative test in one thing, where the equation is proved
                 to hold. Where all premises hold there, it is a case of the general theorem: a
                 corollary, no new equation between distributions. Not every negative test has one.
  #guard         a check that Lean's evaluator, not its kernel, runs when the file is compiled. It
                 leaves no theorem.

What the examples count for. Small examples, negative tests and controls count as nothing toward any
goal of the release. A negative test, together with its companion, proves that the statement is
false once that one premise is dropped. It does not prove that a weaker premise would fail. A
control at which all premises are proved to hold proves that they can be met together at a place of
that shape. A control at which a premise is violated proves that the equation can hold beyond that
premise.

The places. Files named without a path are in Johnson/SendSim/At/. Unless said otherwise a place has
one oracle message (smallMsg m): one main row over the extension field with two data entries, m mask
rows, one answer. No table is sent along (noRide).
  placePadAlone rM    main code (3, 2, rM), mask code (2, 1, 1), one mask row: only the pad.
  placePadAndFree     mask code (2, 2, 1): a free entry, then the pad. Main code (3, 2, 1).
  placePadAndFreeTwo  the same with tails of two entries: main code (3, 2, 2), mask code (3, 2, 2).
  placeFreeApart      as placePadAlone 1 with two mask rows: the free entry's row, the pad's row.
  placePadAndRider    main code (4, 2, 1), mask codes (3, 1, 1) and (3, 4, 1): the oracle message of
                      placePadAlone, and one of one mask row (riderMsg) that is sent along (oneRide)
                      at (k, h) = (1, 0): one round, one row, three coins.
The six places of this file are these, with placePadAlone at rM = 1 and 2. The other places of At/:
  placePadInMain (SmallPlaceBase.lean)   one main row over the base field, no mask row, the pad in
                      the main row.
  placeThreeFree, placeTwoRowsFree, placeTwoRowsMainTwo, placeBaseMain, placeRiderFirst
                      (FilledBooks.lean)   three free entries; two mask rows of two entries; the
                      same with a main tail of two; a main row over the base field with a mask row;
                      the table that is sent along is the first oracle message (riderFirst).

How it fits. Spec.showsAt and Spec.tellsAt are stated in Johnson/SendSim/At/Member.lean and proved
in Johnson/SendSim/At/Shows.lean. The places serve Johnson/SendSim/At/FilledBooks.lean and
Johnson/SendSim/Seat/LotsTestTie.lean.

The other names.
  countCoins, writtenCoins, coinAt   two concrete families of coins; coin number i of the second.
  writtenData, datumZero, datumOne   the concrete data: two entries of oracle message 0's main row.
  smallSeeds, seedZ0, seedZ1, seedFactor, smallAddr   the concrete challenge; a concrete address.
  jobAt, jobIn, sideAt, smallStand   the job at the concrete data; the side of (4); the state in
                 which nothing has been heard or sent, and columns are handed, none of them opened
                 yet (opened = some []).
  pointE, onData, expectedShown   a position's evaluation point; the data's contribution to the
                 answer; the expected value of shownR in (5).
-/
import Johnson.SendSim.At.Member

set_option autoImplicit false

namespace OnBytes.SendSim.At.Small
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

/-! ## The places -/

/-- The shape of an oracle message with one main row over the extension field, m mask rows and one
answer. -/
def smallMsg (m : Nat) : OracleShape :=
  { code := 0, mainRows := 1, mainDeg := 3, maskRows := m, maskCode := 0, answers := 1 }

/-- The shape of an oracle message with one mask row at the second mask code, no main row and no
answer. -/
def riderMsg : OracleShape :=
  { code := 0, mainRows := 0, mainDeg := 1, maskRows := 1, maskCode := 1, answers := 0 }

/-- The public parameters of a small example place, from its codes and its oracle messages'
shapes. -/
def smallPar (codes : Codes) (shapes : List OracleShape) : K1.Par :=
  { place := ⟨1, none, 0, .K1⟩, codes := codes, gp := ⟨1, 0⟩, work := 0
    parts := [("small", (shapes.map fun s => ({ shape := s } : OracleNotice)).toArray)] }

/-- The mask row holds only the pad; the main row's tail has rM entries. -/
def placePadAlone (rM : Nat) : K1.Par := smallPar ⟨#[⟨3, 2, rM⟩], #[⟨2, 1, 1⟩]⟩ [smallMsg 1]
/-- The mask row holds a free entry, then the pad. -/
def placePadAndFree : K1.Par := smallPar ⟨#[⟨3, 2, 1⟩], #[⟨2, 2, 1⟩]⟩ [smallMsg 1]
/-- As placePadAndFree, with tails of two entries. -/
def placePadAndFreeTwo : K1.Par := smallPar ⟨#[⟨3, 2, 2⟩], #[⟨3, 2, 2⟩]⟩ [smallMsg 1]
/-- Two mask rows: the first holds the free entry, the second the pad. -/
def placeFreeApart : K1.Par := smallPar ⟨#[⟨3, 2, 1⟩], #[⟨2, 1, 1⟩]⟩ [smallMsg 2]
/-- The oracle message of placePadAlone, then one of one mask row, which oneRide sends along. -/
def placePadAndRider : K1.Par :=
  smallPar ⟨#[⟨4, 2, 1⟩], #[⟨3, 1, 1⟩, ⟨3, 4, 1⟩]⟩ [smallMsg 1, riderMsg]

/-- No table is sent along. -/
def noRide : Nat → Option Ride := fun _ => none
/-- Oracle message 1 is a table that is sent along, at (k, h) = (1, 0). -/
def oneRide : Nat → Option Ride := fun k => if k == 1 then some ⟨1, 0⟩ else none

/-! ## The jobs fit their places; the numbers of coins -/

#guard sendFits (placePadAlone 1) noRide && K1.planOk (placePadAlone 1)
#guard sendFits (placePadAlone 2) noRide && K1.planOk (placePadAlone 2)
#guard sendFits placePadAndFree noRide && K1.planOk placePadAndFree
#guard sendFits placePadAndFreeTwo noRide && K1.planOk placePadAndFreeTwo
#guard sendFits placeFreeApart noRide && K1.planOk placeFreeApart
#guard sendFits placePadAndRider oneRide && K1.planOk placePadAndRider
#guard dueR (placePadAlone 1) noRide == ⟨0, 3⟩
#guard dueR (placePadAlone 2) noRide == ⟨0, 4⟩
#guard dueR placePadAndFree noRide == ⟨0, 4⟩
#guard dueR placePadAndFreeTwo noRide == ⟨0, 6⟩
#guard dueR placeFreeApart noRide == ⟨0, 5⟩
#guard dueR placePadAndRider oneRide == ⟨0, 7⟩
-- each place has one tree, and one seed of two coordinates and a factor
#guard [placePadAlone 1, placePadAlone 2, placePadAndFree, placePadAndFreeTwo, placeFreeApart,
  placePadAndRider].all fun P => P.trees.length == 1 && P.seeds == 1 && P.coordinates == 2

/-! ## Which coin is placed where -/

/-- The coins in which coin number i of either field has the value i + 1. -/
def countCoins (d : Due) : Cs d :=
  ⟨fun i => toF (i.val + 1).toUInt64, fun i => toE ((i.val + 1).toUInt64, 0, 0)⟩
def firstWord (x : GE) : Nat := (ofE x).1.toNat
def listOfN {α : Type} (n : Nat) (f : Nat → α) : List α := (List.range n).map f
/-- Oracle message k at no data and the coins countCoins, as numbers: the main row's tail (rM
entries), the main row (l entries), the m mask rows (l' entries each) and their tails (r' each). An
entry that holds only coin number n reads n + 1; an entry without a coin reads 0. -/
def coinNumbers (P : K1.Par) (ride : Nat → Option Ride) (k rM l m l' r' : Nat) :
    List Nat × List Nat × List (List Nat) × List (List Nat) :=
  let V := rowsR P ride (fun _ _ _ => none) (countCoins _) k
  (listOfN rM fun q => firstWord (V.mainTlE 0 q), listOfN l fun j => firstWord (V.mainE 0 j),
    listOfN m fun r => listOfN l' fun j => firstWord (V.mask r j),
    listOfN m fun r => listOfN r' fun q => firstWord (V.maskTl r q))

-- the main row's tail; no coin in the main row; the pad alone; its row's tail
#guard coinNumbers (placePadAlone 1) noRide 0 1 2 1 1 1 == ([1], [0, 0], [[2]], [[3]])
#guard coinNumbers (placePadAlone 2) noRide 0 2 2 1 1 1 == ([1, 2], [0, 0], [[3]], [[4]])
-- the free entry, then the pad
#guard coinNumbers placePadAndFree noRide 0 1 2 1 2 1 == ([1], [0, 0], [[2, 3]], [[4]])
#guard coinNumbers placePadAndFreeTwo noRide 0 2 2 1 2 2 == ([1, 2], [0, 0], [[3, 4]], [[5, 6]])
-- the free entry's row and the pad's row
#guard coinNumbers placeFreeApart noRide 0 1 2 2 1 1 == ([1], [0, 0], [[2], [3]], [[4], [5]])
-- the first oracle message as at placePadAlone 1; the row that is sent along: the values 4, 5, 6 in
-- the order second, third, first, then 0; its tail
#guard coinNumbers placePadAndRider oneRide 0 1 2 1 1 1 == ([1], [0, 0], [[2]], [[3]])
#guard coinNumbers placePadAndRider oneRide 1 0 0 1 4 1 == ([], [], [[5, 6, 4, 0]], [[7]])

/-! ## Concrete coins, data and seeds -/

/-- Coin number i of the extension field in writtenCoins. -/
def coinAt (i : Nat) : GE :=
  toE ((500 + 11 * i).toUInt64, (i + 3).toUInt64, (2 * i + 1).toUInt64)
/-- A concrete family of coins. -/
def writtenCoins (d : Due) : Cs d :=
  ⟨fun i => toF (300 + 7 * i.val).toUInt64, fun i => coinAt i.val⟩

def datumZero : GE := toE (1000, 4, 1)
def datumOne : GE := toE (1011, 5, 2)
/-- The concrete data: datumZero and datumOne at entries 0 and 1 of oracle message 0's main row. -/
def writtenData : Nat → Nat → Nat → Option (GF ⊕ GE) := fun k r j =>
  if k == 0 && r == 0 then
    (if j == 0 then some (.inr datumZero) else if j == 1 then some (.inr datumOne) else none)
  else none

def seedZ0 : Fmt.Ext3 := (3, 5, 7)
def seedZ1 : Fmt.Ext3 := (4, 7, 8)
def seedFactor : Fmt.Ext3 := (5, 9, 9)
/-- The concrete challenges of the two rounds: one seed (seedZ0, seedZ1, seedFactor), then
nothing. -/
def smallSeeds : List Fmt.Drawn :=
  [⟨[seedZ0, seedZ1, seedFactor], [], [], none⟩, ⟨[], [], [], none⟩]

def smallAddr : Addr := ⟨⟨1, none, 0, .K1⟩, 0⟩

/-! ## The simulator outputs shownR at no data; the sender discloses shownR at its data -/

/-- At the concrete coins and seeds, the simulator outputs shownR at no data. -/
def tellsOk (P : K1.Par) (ride : Nat → Option Ride) (asks : List (List (List Nat))) : Bool :=
  (sendSim (Pb := Unit) P 0 ride smallAddr).tell () ⟨[], []⟩ smallSeeds asks (writtenCoins _) ==
    some (shownR P 0 ride (fun _ _ _ => none) smallSeeds asks (writtenCoins _))

/-- The job at P with the concrete data. -/
def jobAt (P : K1.Par) (ride : Nat → Option Ride) : SendJob Unit Unit :=
  ⟨P, 0, ride, fun _ _ => writtenData⟩

/-- At the concrete coins and seeds, the sender, executed by the framework's play, discloses shownR
at the concrete data. -/
def showsOk (P : K1.Par) (ride : Nat → Option Ride) (asks : List (List (List Nat))) : Bool :=
  ((play ((sendPart (V := Empty) (jobAt P ride)).steps "" smallAddr (roundsOf P) none
      (writtenCoins _, (), ())) smallSeeds [] standIn).toOption.map fun y => shownOf y.1 asks) ==
    some (shownR P 0 ride writtenData smallSeeds asks (writtenCoins _))

#guard [[[[5]], []], [[[1, 5]], []], [[[0, 3, 3]], []], [[[]], []], []].all fun asks =>
  tellsOk (placePadAlone 1) noRide asks && showsOk (placePadAlone 1) noRide asks &&
  tellsOk (placePadAlone 2) noRide asks && showsOk (placePadAlone 2) noRide asks &&
  tellsOk placePadAndFree noRide asks && showsOk placePadAndFree noRide asks &&
  tellsOk placePadAndFreeTwo noRide asks && showsOk placePadAndFreeTwo noRide asks &&
  tellsOk placeFreeApart noRide asks && showsOk placeFreeApart noRide asks &&
  tellsOk placePadAndRider oneRide asks && showsOk placePadAndRider oneRide asks
-- shownR differs between the concrete data and no data
#guard shownR (placePadAlone 1) 0 noRide writtenData smallSeeds [[[5]], []] (writtenCoins _) !=
  shownR (placePadAlone 1) 0 noRide (fun _ _ _ => none) smallSeeds [[[5]], []] (writtenCoins _)

/-! ## The same at a side: the sub-protocol K1.send, with the sender and its simulator as its row -/

abbrev SmallIn : Type := Local Unit Unit Unit Unit
/-- The job at P with the concrete data, at the input type of a side. -/
def jobIn (P : K1.Par) (ride : Nat → Option Ride) : SendJob SmallIn Unit :=
  ⟨P, 0, ride, fun _ _ => writtenData⟩
/-- The side whose sub-protocol is K1.send P and whose row is the sender with its simulator. -/
def sideAt (P : K1.Par) (ride : Nat → Option Ride) :
    Side (K1.Owing (_root_.Desc.Plain.DState (Array Nat))) Unit SmallIn SmallIn Unit Unit :=
  { block := K1.send P
    row := [(sendPart (jobIn P ride), sendSim P 0 ride ⟨P.place, 0⟩)] }
/-- The state in which nothing has been heard or sent, and columns are handed, none of them opened
yet (opened = some []): at the front ⟨[], []⟩ that is what the front holds for the reads of every
pre. -/
def smallStand : Mid SmallIn Unit := ⟨⟨⟨(), (), (), ()⟩, [], ()⟩, [], [], some []⟩

/-- At the concrete coins and seeds: the side fits; its rounds can sample the challenges; the sender
discloses, and the simulator outputs, what Spec.showsAt and Spec.tellsAt
(Johnson/SendSim/At/Member.lean) state. -/
def sideOk (P : K1.Par) (ride : Nat → Option Ride) (asks : List (List (List Nat))) : Bool :=
  (sideAt P ride).fits && drawsFit (sideAt P ride).block.rounds smallSeeds &&
  ((sideAt P ride).shows Face.own (memberAt (sideAt P ride) (jobIn P ride))
      (writtenCoins _, (), ()) smallStand smallSeeds asks ==
    if sendFits P ride then
      some (shownR P 0 ride ((jobIn P ride).data smallStand.st.input (frontOf smallStand))
        smallSeeds asks (writtenCoins _))
    else none) &&
  ((memberAt (sideAt P ride) (jobIn P ride)).tells Face.own (writtenCoins _) ⟨(), (), (), ()⟩
      ⟨[], []⟩ smallSeeds asks ==
    if sendFits P ride then
      some (shownR P 0 ride (fun _ _ _ => none) smallSeeds asks (writtenCoins _))
    else none)

#guard [[[[5]], []], [[[1, 5]], []], [[[0, 3, 3]], []], []].all fun asks =>
  sideOk (placePadAlone 1) noRide asks && sideOk (placePadAlone 2) noRide asks &&
  sideOk placePadAndFree noRide asks && sideOk placePadAndFreeTwo noRide asks &&
  sideOk placeFreeApart noRide asks && sideOk placePadAndRider oneRide asks
-- a job that does not fit its place (a table sent along at a sampled oracle message): both outputs
-- are the error value
#guard !sendFits (placePadAlone 1) (fun _ => some ⟨1, 0⟩)
#guard sideOk (placePadAlone 1) (fun _ => some ⟨1, 0⟩) [[[5]], []]
#guard (sideAt (placePadAlone 1) (fun _ => some ⟨1, 0⟩)).shows Face.own
    (memberAt (sideAt (placePadAlone 1) (fun _ => some ⟨1, 0⟩))
      (jobIn (placePadAlone 1) (fun _ => some ⟨1, 0⟩)))
    (writtenCoins _, (), ()) smallStand smallSeeds [[[5]], []] == none
-- the rounds cannot sample a challenge whose factor is 0
#guard !drawsFit (sideAt (placePadAlone 1) noRide).block.rounds
  [⟨[seedZ0, seedZ1, (0, 0, 0)], [], [], none⟩, ⟨[], [], [], none⟩]

/-! ## The formulas -/

/-- The evaluation point of position x in a code of 2 ^ a positions, in the extension field. -/
def pointE (a x : Nat) : GE := algebraMap GF GE (toF (Fmt.M1.point a x))
def wordsOfE (l : List GE) : List UInt64 := l.flatMap fun e => [(ofE e).1, (ofE e).2.1, (ofE e).2.2]
def fieldZ0 : GE := toE seedZ0
def fieldZ1 : GE := toE seedZ1
def fieldFactor : GE := toE seedFactor
/-- The contribution of the two data entries to the answer. -/
def onData : GE := (1 - fieldZ1) * (1 - fieldZ0) * datumZero + (1 - fieldZ1) * fieldZ0 * datumOne
/-- The expected value of shownR: at each position in xs the rows' symbols syms x; then the answer
y. -/
def expectedShown (xs : List Nat) (syms : Nat → List GE) (y : GE) : List Shown :=
  [⟨[], [xs.map fun x => (x, wordsOfE (syms x))]⟩, ⟨[(Said.answer y).got], []⟩]

-- the pad alone, a main tail of one entry; the coins in order: t p t'
#guard shownR (placePadAlone 1) 0 noRide writtenData smallSeeds [[[5, 1]], []] (writtenCoins _) ==
  expectedShown [5, 1] (fun x =>
    [coinAt 0 + pointE 3 x * datumZero + pointE 3 x ^ 2 * datumOne,
      coinAt 2 + pointE 2 x * coinAt 1])
    (onData + fieldFactor * coinAt 1)
-- a main tail of two entries; the coins in order: t₀ t₁ p t'
#guard shownR (placePadAlone 2) 0 noRide writtenData smallSeeds [[[5, 1]], []] (writtenCoins _) ==
  expectedShown [5, 1] (fun x =>
    [coinAt 0 + pointE 3 x * coinAt 1 + pointE 3 x ^ 2 * datumZero + pointE 3 x ^ 3 * datumOne,
      coinAt 3 + pointE 2 x * coinAt 2])
    (onData + fieldFactor * coinAt 2)
-- a free entry next to the pad; the coins in order: t u p t'
#guard shownR placePadAndFree 0 noRide writtenData smallSeeds [[[6]], []] (writtenCoins _) ==
  expectedShown [6] (fun x =>
    [coinAt 0 + pointE 3 x * datumZero + pointE 3 x ^ 2 * datumOne,
      coinAt 3 + pointE 2 x * coinAt 1 + pointE 2 x ^ 2 * coinAt 2])
    (onData + fieldZ1 * (1 - fieldZ0) * coinAt 1 + fieldFactor * coinAt 2)
-- tails of two entries; the coins in order: t₀ t₁ u p t'₀ t'₁
#guard shownR placePadAndFreeTwo 0 noRide writtenData smallSeeds [[[6, 3]], []] (writtenCoins _) ==
  expectedShown [6, 3] (fun x =>
    [coinAt 0 + pointE 3 x * coinAt 1 + pointE 3 x ^ 2 * datumZero + pointE 3 x ^ 3 * datumOne,
      coinAt 4 + pointE 3 x * coinAt 5 + pointE 3 x ^ 2 * coinAt 2 + pointE 3 x ^ 3 * coinAt 3])
    (onData + fieldZ1 * (1 - fieldZ0) * coinAt 2 + fieldFactor * coinAt 3)
-- the free entry and the pad in rows of their own; the coins in order: t u p t'₀ t'₁
#guard shownR placeFreeApart 0 noRide writtenData smallSeeds [[[7]], []] (writtenCoins _) ==
  expectedShown [7] (fun x =>
    [coinAt 0 + pointE 3 x * datumZero + pointE 3 x ^ 2 * datumOne,
      coinAt 3 + pointE 2 x * coinAt 1,
      coinAt 4 + pointE 2 x * coinAt 2])
    (onData + fieldZ1 * (1 - fieldZ0) * coinAt 1 + fieldFactor * coinAt 2)
-- with a row that is sent along; the coins in order: t p t' c₀ c₁ c₂ t''
#guard shownR placePadAndRider 0 oneRide writtenData smallSeeds [[[9]], []] (writtenCoins _) ==
  expectedShown [9] (fun x =>
    [coinAt 0 + pointE 4 x * datumZero + pointE 4 x ^ 2 * datumOne,
      coinAt 2 + pointE 3 x * coinAt 1,
      coinAt 6 + pointE 3 x * coinAt 4 + pointE 3 x ^ 2 * coinAt 5 + pointE 3 x ^ 3 * coinAt 3])
    (onData + fieldFactor * coinAt 1)
/-! ## The checks above can fail: each again with one thing modified -/

-- the three coins of the row that is sent along, in the order first, second, third
#guard shownR placePadAndRider 0 oneRide writtenData smallSeeds [[[9]], []] (writtenCoins _) !=
  expectedShown [9] (fun x =>
    [coinAt 0 + pointE 4 x * datumZero + pointE 4 x ^ 2 * datumOne,
      coinAt 2 + pointE 3 x * coinAt 1,
      coinAt 6 + pointE 3 x * coinAt 3 + pointE 3 x ^ 2 * coinAt 4 + pointE 3 x ^ 3 * coinAt 5])
    (onData + fieldFactor * coinAt 1)
-- the weight on the free entry: z₁ z₀ for z₁ (1 - z₀)
#guard shownR placePadAndFree 0 noRide writtenData smallSeeds [[[6]], []] (writtenCoins _) !=
  expectedShown [6] (fun x =>
    [coinAt 0 + pointE 3 x * datumZero + pointE 3 x ^ 2 * datumOne,
      coinAt 3 + pointE 2 x * coinAt 1 + pointE 2 x ^ 2 * coinAt 2])
    (onData + fieldZ1 * fieldZ0 * coinAt 1 + fieldFactor * coinAt 2)
-- the free entry and the pad exchanged
#guard shownR placePadAndFree 0 noRide writtenData smallSeeds [[[6]], []] (writtenCoins _) !=
  expectedShown [6] (fun x =>
    [coinAt 0 + pointE 3 x * datumZero + pointE 3 x ^ 2 * datumOne,
      coinAt 3 + pointE 2 x * coinAt 2 + pointE 2 x ^ 2 * coinAt 1])
    (onData + fieldZ1 * (1 - fieldZ0) * coinAt 2 + fieldFactor * coinAt 1)
-- the mask row read at the tree's point, not at its own code's
#guard shownR (placePadAlone 1) 0 noRide writtenData smallSeeds [[[5]], []] (writtenCoins _) !=
  expectedShown [5] (fun x =>
    [coinAt 0 + pointE 3 x * datumZero + pointE 3 x ^ 2 * datumOne,
      coinAt 2 + pointE 3 x * coinAt 1])
    (onData + fieldFactor * coinAt 1)
-- the tail as the highest coefficients of the symbol, not the lowest
#guard shownR (placePadAlone 1) 0 noRide writtenData smallSeeds [[[5]], []] (writtenCoins _) !=
  expectedShown [5] (fun x =>
    [datumZero + pointE 3 x * datumOne + pointE 3 x ^ 2 * coinAt 0,
      coinAt 2 + pointE 2 x * coinAt 1])
    (onData + fieldFactor * coinAt 1)
-- the answer gives the pad's entry its weight under z as well
#guard shownR (placePadAlone 1) 0 noRide writtenData smallSeeds [[[5]], []] (writtenCoins _) !=
  expectedShown [5] (fun x =>
    [coinAt 0 + pointE 3 x * datumZero + pointE 3 x ^ 2 * datumOne,
      coinAt 2 + pointE 2 x * coinAt 1])
    (onData + (fieldFactor + fieldZ1 * (1 - fieldZ0)) * coinAt 1)
-- two coins' numbers exchanged
#guard coinNumbers placePadAndFree noRide 0 1 2 1 2 1 != ([1], [0, 0], [[3, 2]], [[4]])

-- two positions that differ by the mask code's length: one point of the mask code, two of the main
-- code
#guard pointE 2 5 == pointE 2 1 && pointE 3 5 != pointE 3 1

end OnBytes.SendSim.At.Small

#print axioms OnBytes.SendSim.At.Small.smallMsg
#print axioms OnBytes.SendSim.At.Small.riderMsg
#print axioms OnBytes.SendSim.At.Small.smallPar
#print axioms OnBytes.SendSim.At.Small.placePadAlone
#print axioms OnBytes.SendSim.At.Small.placePadAndFree
#print axioms OnBytes.SendSim.At.Small.placePadAndFreeTwo
#print axioms OnBytes.SendSim.At.Small.placeFreeApart
#print axioms OnBytes.SendSim.At.Small.placePadAndRider
#print axioms OnBytes.SendSim.At.Small.noRide
#print axioms OnBytes.SendSim.At.Small.oneRide
#print axioms OnBytes.SendSim.At.Small.countCoins
#print axioms OnBytes.SendSim.At.Small.firstWord
#print axioms OnBytes.SendSim.At.Small.listOfN
#print axioms OnBytes.SendSim.At.Small.coinNumbers
#print axioms OnBytes.SendSim.At.Small.coinAt
#print axioms OnBytes.SendSim.At.Small.writtenCoins
#print axioms OnBytes.SendSim.At.Small.datumZero
#print axioms OnBytes.SendSim.At.Small.datumOne
#print axioms OnBytes.SendSim.At.Small.writtenData
#print axioms OnBytes.SendSim.At.Small.seedZ0
#print axioms OnBytes.SendSim.At.Small.seedZ1
#print axioms OnBytes.SendSim.At.Small.seedFactor
#print axioms OnBytes.SendSim.At.Small.smallSeeds
#print axioms OnBytes.SendSim.At.Small.smallAddr
#print axioms OnBytes.SendSim.At.Small.tellsOk
#print axioms OnBytes.SendSim.At.Small.jobAt
#print axioms OnBytes.SendSim.At.Small.showsOk
#print axioms OnBytes.SendSim.At.Small.SmallIn
#print axioms OnBytes.SendSim.At.Small.jobIn
#print axioms OnBytes.SendSim.At.Small.sideAt
#print axioms OnBytes.SendSim.At.Small.smallStand
#print axioms OnBytes.SendSim.At.Small.sideOk
#print axioms OnBytes.SendSim.At.Small.pointE
#print axioms OnBytes.SendSim.At.Small.wordsOfE
#print axioms OnBytes.SendSim.At.Small.fieldZ0
#print axioms OnBytes.SendSim.At.Small.fieldZ1
#print axioms OnBytes.SendSim.At.Small.fieldFactor
#print axioms OnBytes.SendSim.At.Small.onData
#print axioms OnBytes.SendSim.At.Small.expectedShown
