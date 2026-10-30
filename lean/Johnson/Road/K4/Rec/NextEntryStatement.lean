-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/NextEntryStatement.lean: THE STATEMENT, AND NO PROOF: "AT AN UNMARKED STATEMENT
INSIDE THE TABLE OF JOINTS' PROMISE AT A BORDER, THE NUMBER OF THE INDEX MASKS' MESSAGE, AND THE
ENTRY THAT ITS LEDGER HANDS OUT NEXT, ARE TWO NUMBERS OF THE PUBLIC PARAMETERS". Definitions alone;
two of them tests with code. The proof stands beside: Johnson/Road/K4/Rec/NextEntry.lean.

A TEST THAT ASKS THE FOUR ITEMS IN `pubSets` ALONE IS FALSE AT EVERY LIST OF EXTRA PUBLIC
TESTS M: it asks all four items in `pubSets M links ps`, and the first,
indexIs, stands in none: it is tied to the item pinI (`pubOfItems`, Johnson/Desc/First/Borders.lean)
and is asked by the promise through the open items. Under such a test `NextEntryIs` is true and its
premise is met nowhere. SO `openNextB` asks each of the four in `heldAt M links ps j`: THE VERY LIST
OVER WHICH THE PROMISE's CLAUSE `pubHeld` RUNS at border j: an item counts as open exactly where the
promise asks it. (By the kernel at one M: `indexIs_in_no_set`, OpenNextAt.lean; else by reading.)

WHO SPENDS IT. The line wo of K4's row (Johnson/Road/K4/K4LinesWo.lean) has a premise hname: at
every unmarked statement b inside the promise behind K4's block: b's number of the index masks'
message is im₀, and whatever entry that message's ledger in b hands out next is v: im₀ and v fixed
in front of "for all b". `NextEntryIs`' conclusion is that premise to the letter, at a border j.

THE CHAIN, item by item. "indexIs": the number is the table's N.indexNo. "K12.msgShapes", with the
promise's clause on the book: the message's WHOLE shape (mask rows, mask code, answers among its six
fields) is the plan's. "In order": the statement's codes are the plan's: so the count of free
entries of a fresh ledger is a number of the public parameters. "K13.pileWithin": every ledger in
the statement is that of some number k of takes since it was made (`LedgerAt`,
Johnson/Desc/K13/Law/LedgerWithin.lean): what is left and k make that count. "pile.room" at segment
m: what is left is that count less the segments in front of m that leave a row. So k is the number
of these segments, and the entry handed out next has the k-th number given (`takeEntry_no`,
Johnson/Desc/K13/Law/LedgerNo.lean).

  `EIndexIs`, `ERoom`: EQUATIONS of the meaning's field pub at two items (the first's test written
    out: `indexIsC`, Johnson/Desc/K13/PubK13.lean). `EWithin`: AN IMPLICATION: a yes of
    "K13.pileWithin" gives `LedgersFit` (Johnson/Desc/K13/Law/OwedLedgers.lean).
  `heldAt M links ps j`: the public items that the promise asks at border j: those of `pubSets`
    and those tied to an open item.
  `nextItems m`, `openNextB M links ps j m`: the four items; A TEST: each stands in `heldAt`.
  `nextFitsB cs M n im free0 fvs m`: A TEST: the plan's list has a shape at number im below n; free0
    is the count of free entries at that shape and the plan's codes; the segments in front of m that
    leave a row are at most free0.
  `nextNoP M n im fvs m`: THE NUMBER: `takenNo` (OnBytes/Iop/LedgerPlaces.lean) at that shape's mask
    rows and the number of these segments.
  **`NextEntryIs`**.

OBJECT: none of its own. USER: meant: K4LinesWo.lean's hname, at j := k + 1, im₀ := N.indexNo, v :=
`nextNoP …`. LETTERS, filled by nobody: N, Mg, Z, links, ps, j, m, M, cs, free0, fvs.

Limits. A SENTENCE: NOTHING IS PROVED HERE. THE FIVE PREMISES ON THE MEANING ARE SHOWN AT NO TERM.
`EWithin` IS NO EQUATION: it follows from the equation "the item's test is `pileWithinC`" and from
"`ledgersFitC` says yes just where `LedgersFit` holds", which is stated as `OwedLedgersC`
(Johnson/Desc/K13/Law/OwedWithin.lean) and proved as `ledgersC`
(Johnson/Desc/K13/Law/LedgersC.lean). `openNextB` HAS BEEN EVALUATED AT TWO LISTS OF EXTRA PUBLIC
TESTS, by Lean's kernel, behind K4's sub-protocol at its twelve places: at the wider meaning's list
it accepts, at the composed meaning's own it rejects (Johnson/Road/K4/Rec/OpenNextWide.lean; its
half on pinI: Johnson/Road/K4/Rec/OpenNextAt.lean). By a run at one honest proof of each of two
sizes what is left in that ledger is 255 less the bearing segments in front. Where the ledger has
nothing to hand out the second half holds for nothing. K04_law, the law of K4's sub-protocol itself,
IS NOT PROVED BY THIS. Nothing on soundness.
-/
import Johnson.Desc.K13.Law.LedgerNo
import Johnson.Desc.K13.Law.OwedLedgers
import Johnson.Top.H0.Walk.FrameEntriesDefs
import Johnson.Road.K4.Rec.Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart Pub More Meaning Numbers pubSets pubOfItems openSets
  start)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.K13.Law (LedgersFit)
open VerifiableInference.Desc.Sound (Frame onQ)
open Johnson.Desc.First.Walk.Law (ledgerAt)
open Johnson.Desc.First.Walk.Tied (roomIsB rowsBefore)

section
variable {P W : Type}

/-- What the item indexIs says. -/
def EIndexIs (Mg : Meaning P W) (n : ℕ) : Prop :=
  ∀ a : P × S, Mg.pub .indexIs a = (a.2.out.indexMasks == n)

/-- What the item pile.room says. -/
def ERoom (Mg : Meaning P W) (free0 : ℕ) (fvs : List Bool) : Prop :=
  ∀ (m : ℕ) (a : P × S), Mg.pub (.more (some m) "pile.room") a = roomIsB free0 fvs m a.2

/-- What a yes of the item K13.pileWithin gives. -/
def EWithin (Mg : Meaning P W) : Prop :=
  ∀ a : P × S, Mg.pub (.more none "K13.pileWithin") a = true → LedgersFit a.2.st

end

/-- The four public items that are spent. -/
def nextItems (m : ℕ) : List Pub :=
  [.indexIs, .more none "K12.msgShapes", .more none "K13.pileWithin", .more (some m) "pile.room"]

/-- The public items that the promise asks at border j: the list over which `pubHeld` runs there.
M: the list of extra public tests. -/
def heldAt (M : More) (links : List ModelPart) (ps : List Place) (j : ℕ) : List Pub :=
  (pubSets M links ps)[j]?.getD [] ++ pubOfItems ((openSets links ps (start links))[j]?.getD [])

/-- A TEST: the promise asks each of the four at border j. -/
def openNextB (M : More) (links : List ModelPart) (ps : List Place) (j m : ℕ) : Bool :=
  (nextItems m).all fun q => (heldAt M links ps j).contains q

/-- A TEST: the plan has a shape at number im; free0 is its count of free entries; the bearing
segments in front of m are at most so many. -/
def nextFitsB (cs : Codes) (M : List OracleShape) (n im free0 : ℕ) (fvs : List Bool) (m : ℕ) :
    Bool :=
  match (M.take n)[im]? with
  | none => false
  | some sh =>
    decide (free0 =
      Send.freeMaskEntries sh.maskRows (cs.mask.getD sh.maskCode default).ell sh.answers) &&
      decide (rowsBefore fvs m ≤ free0)

/-- THE NUMBER of the entry that is handed out next. -/
def nextNoP (M : List OracleShape) (n im : ℕ) (fvs : List Bool) (m : ℕ) : ℕ :=
  takenNo ((((M.take n)[im]?).map (·.maskRows)).getD 0) (rowsBefore fvs m)

/-- **THE STATEMENT.** -/
def NextEntryIs : Prop :=
  ∀ (P W : Type) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (Z : P) (links : List ModelPart)
    (ps : List Place) (j m : ℕ) (M : List OracleShape) (cs : Codes) (free0 : ℕ)
    (fvs : List Bool),
    EIndexIs Mg N.indexNo → EShapes Mg M → ECodes Mg cs → EWithin Mg → ERoom Mg free0 fvs →
    openNextB Mg.more links ps j m = true →
    nextFitsB cs M (N.msgsAt ps[j]?) N.indexNo free0 fvs m = true →
    ∀ b : S × Fr.E.Str, onQ N Mg links ps (fun s => (Z, s)) j b → b.1.failed = none →
      b.1.out.indexMasks = N.indexNo ∧
        ∀ l c l', ledgerAt b.1 = some l → takeEntry l = some (c, l') →
          c = nextNoP M (N.msgsAt ps[j]?) N.indexNo fvs m

end OnBytes.Road.K4.Rec
