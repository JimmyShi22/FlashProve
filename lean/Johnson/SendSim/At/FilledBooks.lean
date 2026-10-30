-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/FilledBooks.lean: small example places of the honest sender, each with a concrete
book that leaves no free entry unused (a filled book), and the executable test of the premise on the
book evaluated at these books and at modified ones.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean; for the small
examples, Johnson/SendSim/At/SmallPlaces.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file has. Definitions (five places, the filled books), one theorem, and checks by #guard
when the file is compiled. The places and the words "filled book" are explained under "Terms" below.
  budAt_iff_test   Proved in Lean, for all P and asks: the bound on queried positions (budAt) holds
        if and only if the executable test budTest returns true.
What the #guard lines check.
  - Each place that is defined here passes sendFits and K1.planOk, K1's public test that every
    oracle message has an admitted shape, that the trees can be made and that some oracle message is
    sampled. Its number of coins, and numbers that the premise on the book reads (among maskStart,
    padNo, maskTailNo, freeNo), equal the listed values. So does the coin at each entry
    (coinNumbers), at all of these places but placeBaseMain.
  - At each unmodified book spenderClearB, the executable test of SpenderClear, accepts at the last
    spender. At placeThreeFree it also accepts at the other two. bookClearB accepts at
    placeThreeFree, placeTwoRowsFree and placeRiderFirst.
  - With one clause violated spenderClearB rejects at the last spender: the pad is known; the tail
    of the spent entry's row, or of the pad's row, is known; a coin is spent twice by one part, or
    by two parts; the pad, a mask tail's coin, the main tail or a coin of the base field is spent.
    Where the table's coefficients are spent: its tail is known; one coefficient too few is spent.
  - With a change that violates no clause it accepts: the main tail is known; the pad is carried to
    a part later than the last spender; at placePadAndRider, where the table's coefficients are
    spent, the sampled oracle message is known whole; at placeRiderFirst the table's tail, or its
    whole row, is known.
  - With a run beyond the sender's number of coins bookClearB rejects.
  - budTest accepts the position 6 at placeThreeFree and placeTwoRowsFree, and rejects the pair 6, 2
    at the first and the pair 6, 1 at the second. At placeTwoRowsMainTwo it accepts the positions 1
    and 5 = 1 + 2 ^ 2, which are one position modulo the mask code's 2 ^ 2 positions. It rejects 1
    and 2, which differ modulo 2 ^ 2, although the main row's tail has room for two, and it rejects
    1, 5 and 3.
  - shownR at placeThreeFree and placeTwoRowsFree, at concrete coins, data, seeds and one position,
    equals explicit formulas: each symbol, and the answer with the weight of a seed of three
    coordinates on each free entry.

Limits.
Most #guard lines evaluate a test on the numbers of coins; the last two compare shownR with explicit
formulas. No distribution is named: nothing here says that the equation FreshRowsEq holds or fails
at these books. (FreshRowsEq: the equation that Spec.rowsFreshWide concludes,
Johnson/SendSim/At/FreshWide.lean.)
A #guard leaves no theorem. spenderClearB accepts exactly where SpenderClear holds
(spenderClearB_iff, Johnson/SendSim/At/BookTest.lean).
Whoever wrote the expected values also wrote the places, so the checks are not independent.

Terms.
  filled book   a book in which every free entry of the place is spent by some part or, in some
        modified books, carried to the last spender and so known there. In filledAt a b c three
        parts in order (spenderOne, spenderTwo, spenderThree) spend one coin each. The premise on
        the book (SpenderClear; Johnson/SendSim/At/Fresh.lean, "clear") is tested at the last of
        them (clearAt), where the runs of the other two are known.
  why filled   A free entry that nobody spends and that is not known is one more uniform coin in the
        answer and in its row's symbols. It can act as a second pad: the equation FreshRowsEq may
        then hold although a clause is violated, and the violation would go unnoticed (argued, not
        proved). At the unmodified filled books, except at placeRiderFirst (see Notes), the sender
        has exactly as many coins as there are values disclosed, spent and known. The counts below
        are by inspection, not proved.
The places. A code is written (a, l, r): 2 ^ a positions, a message of l entries, a tail of r.
Unless said otherwise a place has one oracle message, with one main row over the extension field and
one answer.
  placeThreeFree      main code (3, 2, 1), mask code (3, 4, 1), one mask row: three free entries and
                      the pad. 6 coins = 3 values disclosed at one position (main symbol, mask
                      symbol, answer) + 3 free entries.
  placeTwoRowsFree    main code (3, 2, 1), mask code (2, 2, 1), two mask rows: three free entries
                      and the pad. The last spent entry's row and the pad's row have tails of their
                      own. 7 coins = 4 values (three symbols, answer) + 3 free entries.
  placeBaseMain       placeThreeFree with the main row over the base field: one coin of that field.
  placeRiderFirst     a table of one row that is sent along, then a sampled oracle message with
                      three free entries. The table's row has more entries (8) than coefficients
                      (3).
  placePadAndRider    (Johnson/SendSim/At/SmallPlaces.lean) the sampled oracle message first, then
                      the table.
  placeTwoRowsMainTwo   placeTwoRowsFree with a main tail of two entries. The main code has twice as
                      many positions as the mask code. At the positions 1 and 5: 8 coins = 2 main
                      symbols + 2 mask symbols + 1 answer + 3 free entries.

How it fits. budAt_iff_test decides budAt at concrete positions.

Notes. At placeRiderFirst the books filledAt 5 6 7 give the table's three coefficients to nobody:
they are neither spent nor known, so the 10 coins are more than what is disclosed, spent and known.
Two modified books also leave a coin to nobody. filledAt 1 2 2 leaves the third free entry. The book
that spends only two of the table's three coefficients leaves the third.
-/
import Johnson.SendSim.At.SmallPlaces
import Johnson.SendSim.At.BookTest

set_option autoImplicit false

namespace OnBytes.SendSim.At.Small
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

/-! ## The places -/

/-- One mask row of four entries: three free entries and the pad. -/
def placeThreeFree : K1.Par := smallPar ⟨#[⟨3, 2, 1⟩], #[⟨3, 4, 1⟩]⟩ [smallMsg 1]
/-- Two mask rows of two entries each: three free entries and the pad. -/
def placeTwoRowsFree : K1.Par := smallPar ⟨#[⟨3, 2, 1⟩], #[⟨2, 2, 1⟩]⟩ [smallMsg 2]
/-- placeThreeFree with the main row over the base field. -/
def placeBaseMain : K1.Par :=
  smallPar ⟨#[⟨3, 2, 1⟩], #[⟨3, 4, 1⟩]⟩
    [{ code := 0, mainRows := 1, mainDeg := 1, maskRows := 1, maskCode := 0, answers := 1 }]
/-- Oracle message 0 is a table of one row that is sent along (riderFirst); oracle message 1 is
sampled and has three free entries. -/
def placeRiderFirst : K1.Par :=
  smallPar ⟨#[⟨4, 2, 1⟩], #[⟨4, 4, 1⟩, ⟨4, 8, 1⟩]⟩ [riderMsg, smallMsg 1]
/-- Oracle message 0 is sent along, for a folding step with k = 1 and h = 0: one row, three
coefficients. -/
def riderFirst : Nat → Option Ride := fun k => if k == 0 then some ⟨1, 0⟩ else none

#guard sendFits placeThreeFree noRide && K1.planOk placeThreeFree
#guard sendFits placeTwoRowsFree noRide && K1.planOk placeTwoRowsFree
#guard sendFits placeBaseMain noRide && K1.planOk placeBaseMain
#guard sendFits placeRiderFirst riderFirst
#guard K1.planOk placeRiderFirst
#guard dueR placeThreeFree noRide == ⟨0, 6⟩
#guard dueR placeTwoRowsFree noRide == ⟨0, 7⟩
#guard dueR placeBaseMain noRide == ⟨1, 5⟩
#guard dueR placeRiderFirst riderFirst == ⟨0, 10⟩

-- which coin is at which entry (coinNumbers prints a coin's number + 1, and 0 where no coin is)
#guard coinNumbers placeThreeFree noRide 0 1 2 1 4 1 == ([1], [0, 0], [[2, 3, 4, 5]], [[6]])
-- two mask rows: the coins are numbered entry by entry, and within an entry row by row
#guard coinNumbers placeTwoRowsFree noRide 0 1 2 2 2 1 ==
  ([1], [0, 0], [[2, 4], [3, 5]], [[6], [7]])
#guard coinNumbers placeRiderFirst riderFirst 0 0 0 1 8 1 ==
  ([], [], [[2, 3, 1, 0, 0, 0, 0, 0]], [[4]])
#guard coinNumbers placeRiderFirst riderFirst 1 1 2 1 4 1 == ([5], [0, 0], [[6, 7, 8, 9]], [[10]])

-- the numbers that the premise on the book reads (coins are counted from 0)
#guard maskStart placeThreeFree noRide 0 == 1 && padNo placeThreeFree noRide 0 0 == 4 &&
  maskTailNo placeThreeFree noRide 0 0 0 == 5 && freeNo placeThreeFree noRide 0 == {1, 2, 3}
#guard maskStart placeTwoRowsFree noRide 0 == 1 && padNo placeTwoRowsFree noRide 0 0 == 4 &&
  maskTailNo placeTwoRowsFree noRide 0 0 0 == 5 && maskTailNo placeTwoRowsFree noRide 0 1 0 == 6 &&
  freeNo placeTwoRowsFree noRide 0 == {1, 2, 3}
#guard maskStart placeBaseMain noRide 0 == 0 && padNo placeBaseMain noRide 0 0 == 3 &&
  maskTailNo placeBaseMain noRide 0 0 0 == 4 && freeNo placeBaseMain noRide 0 == {0, 1, 2}
#guard maskStart placeRiderFirst riderFirst 0 == 0 &&
  maskTailNo placeRiderFirst riderFirst 0 0 0 == 3 &&
  maskStart placeRiderFirst riderFirst 1 == 5 && padNo placeRiderFirst riderFirst 1 0 == 8 &&
  maskTailNo placeRiderFirst riderFirst 1 0 0 == 9 &&
  freeNo placeRiderFirst riderFirst 1 == {5, 6, 7}
-- As defined, freeNo at the table that is sent along reaches into the next oracle message's coins.
-- MaskSpender reads freeNo only at oracle messages that are not sent along.
#guard freeNo placeRiderFirst riderFirst 0 == {0, 1, 2, 3, 4, 5, 6, 7}

/-! ## The books -/

/-- The address of part number 1 at the small examples' place, next after the sender (smallAddr,
part number 0). spenderTwo and spenderThree are the parts number 2 and 3 there. -/
def spenderOne : Addr := ⟨⟨1, none, 0, .K1⟩, 1⟩
def spenderTwo : Addr := ⟨⟨1, none, 0, .K1⟩, 2⟩
def spenderThree : Addr := ⟨⟨1, none, 0, .K1⟩, 3⟩

/-- The entry by which p spends n of the sender's coins of the extension field, from number s on. -/
def spendE (name : String) (s n : Nat) (p : Addr) : Ahead :=
  ⟨name, smallAddr, ⟨0, s⟩, ⟨0, n⟩, p, true⟩
/-- The same run, carried to p and not spent, so known at p. -/
def carryE (name : String) (s n : Nat) (p : Addr) : Ahead :=
  ⟨name, smallAddr, ⟨0, s⟩, ⟨0, n⟩, p, false⟩
/-- The book that has the entries es and nothing else. -/
def bookWith (es : List Ahead) : ProverCoinCounts :=
  { first := [], shared := [], second := [], cuts := [], ahead := es }

/-- The entries by which spenderOne, spenderTwo and spenderThree spend the coins number a, b and c
of the extension field, one coin each. -/
def filledAt (a b c : Nat) : List Ahead :=
  [spendE "first" a 1 spenderOne, spendE "second" b 1 spenderTwo, spendE "third" c 1 spenderThree]

/-- The executable test of SpenderClear (spenderClearB) at the book with the entries es, at the
empty order and at the last spender, spenderThree. -/
def clearAt (P : K1.Par) (ride : Nat → Option Ride) (es : List Ahead) : Bool :=
  spenderClearB P ride (bookWith es) [] smallAddr spenderThree
/-- Each entry's start and length in the extension field. -/
def startsCounts (l : List Ahead) : List (Nat × Nat) := l.map fun e => (e.start.e, e.count.e)

-- what the last spender spends, and what is known there: the runs of the other two spenders
#guard startsCounts ((bookWith (filledAt 1 2 3)).spentBy smallAddr spenderThree) == [(3, 1)]
#guard startsCounts ((bookWith (filledAt 1 2 3)).knownBy [] smallAddr spenderThree) ==
  [(1, 1), (2, 1)]
-- nothing is known at the first spender
#guard startsCounts ((bookWith (filledAt 1 2 3)).knownBy [] smallAddr spenderOne) == []

/-! ## Three free entries in one mask row -/

-- unmodified: accepted at each spender, and by the test on the whole book
#guard clearAt placeThreeFree noRide (filledAt 1 2 3)
#guard spenderClearB placeThreeFree noRide (bookWith (filledAt 1 2 3)) [] smallAddr spenderOne &&
  spenderClearB placeThreeFree noRide (bookWith (filledAt 1 2 3)) [] smallAddr spenderTwo &&
  bookClearB placeThreeFree noRide (bookWith (filledAt 1 2 3)) [] smallAddr
-- the pad is known
#guard !clearAt placeThreeFree noRide (filledAt 1 2 3 ++ [carryE "pad" 4 1 spenderThree])
-- the pad is carried to an earlier part, so it is known at the last spender too
#guard !clearAt placeThreeFree noRide (filledAt 1 2 3 ++ [carryE "pad" 4 1 spenderOne])
-- the mask row's tail is known
#guard !clearAt placeThreeFree noRide (filledAt 1 2 3 ++ [carryE "tail" 5 1 spenderThree])
-- a coin is spent twice by one part
#guard !clearAt placeThreeFree noRide (filledAt 1 2 3 ++ [spendE "again" 3 1 spenderThree])
-- a coin is spent by two parts
#guard !clearAt placeThreeFree noRide (filledAt 1 2 2)
-- the pad, the mask tail's coin, the main tail is spent; the third free entry is carried to the
-- spender, so that the book stays filled
#guard !clearAt placeThreeFree noRide (filledAt 1 2 4 ++ [carryE "free" 3 1 spenderThree])
#guard !clearAt placeThreeFree noRide (filledAt 1 2 5 ++ [carryE "free" 3 1 spenderThree])
#guard !clearAt placeThreeFree noRide (filledAt 1 2 0 ++ [carryE "free" 3 1 spenderThree])
-- a run beyond the sender's number of coins: rejected by the test on the whole book
#guard !bookClearB placeThreeFree noRide
  (bookWith [spendE "first" 1 1 spenderOne, spendE "long" 3 4 spenderThree]) [] smallAddr
-- no clause is violated: the main tail is known
#guard clearAt placeThreeFree noRide (filledAt 1 2 3 ++ [carryE "main" 0 1 spenderThree])
-- no clause is violated: the pad is carried to a part later than the last spender
#guard clearAt placeThreeFree noRide
  (filledAt 1 2 3 ++ [carryE "pad" 4 1 ⟨⟨1, none, 0, .K1⟩, 4⟩])

/-! ## Two mask rows: the spent entry and the pad are in different rows -/

-- coin number 3, which the last spender spends, is in row 0; the pad is in row 1
#guard clearAt placeTwoRowsFree noRide (filledAt 1 2 3) &&
  bookClearB placeTwoRowsFree noRide (bookWith (filledAt 1 2 3)) [] smallAddr
-- the tail of the spent entry's row, the tail of the pad's row, the pad is known
#guard !clearAt placeTwoRowsFree noRide (filledAt 1 2 3 ++ [carryE "tail" 5 1 spenderThree])
#guard !clearAt placeTwoRowsFree noRide (filledAt 1 2 3 ++ [carryE "tail" 6 1 spenderThree])
#guard !clearAt placeTwoRowsFree noRide (filledAt 1 2 3 ++ [carryE "pad" 4 1 spenderThree])
-- no clause is violated: the main tail is known
#guard clearAt placeTwoRowsFree noRide (filledAt 1 2 3 ++ [carryE "main" 0 1 spenderThree])

/-! ## A coin of the base field -/

#guard clearAt placeBaseMain noRide (filledAt 0 1 2)
-- the spent run also holds the main tail, a coin of the base field
#guard !clearAt placeBaseMain noRide
  [spendE "first" 0 1 spenderOne, spendE "second" 1 1 spenderTwo,
    ⟨"third", smallAddr, ⟨0, 2⟩, ⟨1, 1⟩, spenderThree, true⟩]

/-! ## A table that is sent along -/

-- the table comes after the sampled oracle message: one part spends its three coefficients
#guard clearAt placePadAndRider oneRide [spendE "table" 3 3 spenderThree]
-- its tail is known; one coefficient too few is spent
#guard !clearAt placePadAndRider oneRide
  [spendE "table" 3 3 spenderThree, carryE "tail" 6 1 spenderThree]
#guard !clearAt placePadAndRider oneRide [spendE "table" 3 2 spenderThree]
-- no clause is violated: the other oracle message is known whole (main tail, pad, mask tail)
#guard clearAt placePadAndRider oneRide
  [spendE "table" 3 3 spenderThree, carryE "other" 0 3 spenderThree]
-- the table comes before a sampled oracle message whose three free entries are spent: unmodified
#guard clearAt placeRiderFirst riderFirst (filledAt 5 6 7) &&
  bookClearB placeRiderFirst riderFirst (bookWith (filledAt 5 6 7)) [] smallAddr
-- no clause is violated: the table's tail is known; its coefficients and its tail are known
#guard clearAt placeRiderFirst riderFirst (filledAt 5 6 7 ++ [carryE "tail" 3 1 spenderThree])
#guard clearAt placeRiderFirst riderFirst (filledAt 5 6 7 ++ [carryE "row" 0 4 spenderThree])
-- rejected, as at placeThreeFree: the sampled oracle message's own pad, or its mask tail, is known
#guard !clearAt placeRiderFirst riderFirst (filledAt 5 6 7 ++ [carryE "pad" 8 1 spenderThree])
#guard !clearAt placeRiderFirst riderFirst (filledAt 5 6 7 ++ [carryE "tail" 9 1 spenderThree])

/-! ## The bound on queried positions -/

/-- The bound on queried positions (budAt, Johnson/SendSim/At/Sim.lean) as an executable test. -/
def budTest (P : K1.Par) (asks : List (List (List Nat))) : Bool :=
  (List.range P.sent.size).all fun k =>
    match ((Own.treesMade P.codes P.sent).getD {}).tree[k]? with
    | none => true
    | some τ =>
      (decide ((shapeAt P k).mainRows = 0) ||
        decide (((asked asks τ).map
            (· % 2 ^ (P.codes.base.getD (shapeAt P k).code default).logN)).toFinset.card
          ≤ (P.codes.base.getD (shapeAt P k).code default).r)) &&
      (decide ((shapeAt P k).maskRows = 0) ||
        decide (((asked asks τ).map
            (· % 2 ^ (P.codes.mask.getD (shapeAt P k).maskCode default).logN)).toFinset.card
          ≤ (P.codes.mask.getD (shapeAt P k).maskCode default).r))

/-- The bound budAt holds if and only if budTest returns true, for all P and asks. -/
theorem budAt_iff_test (P : K1.Par) (asks : List (List (List Nat))) :
    budAt P asks ↔ budTest P asks = true := by
  unfold budAt budTest
  rw [List.all_eq_true]
  constructor
  · intro h k hk
    split
    · rfl
    · rename_i τ e
      obtain ⟨h1, h2⟩ := h k τ (List.mem_range.1 hk) e
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
      exact ⟨(Classical.em _).imp id h1, (Classical.em _).imp id h2⟩
  · intro h k τ hk e
    have h0 := h k (List.mem_range.2 hk)
    simp only [e, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h0
    exact ⟨fun m => h0.1.resolve_left m, fun m => h0.2.resolve_left m⟩

/-- A main row with a tail of two entries in a code of length 2 ^ 3; two mask rows with tails of one
entry in a code of length 2 ^ 2. -/
def placeTwoRowsMainTwo : K1.Par := smallPar ⟨#[⟨3, 2, 2⟩], #[⟨2, 2, 1⟩]⟩ [smallMsg 2]

#guard sendFits placeTwoRowsMainTwo noRide && K1.planOk placeTwoRowsMainTwo &&
  dueR placeTwoRowsMainTwo noRide == ⟨0, 8⟩
#guard coinNumbers placeTwoRowsMainTwo noRide 0 2 2 2 2 1 ==
  ([1, 2], [0, 0], [[3, 5], [4, 6]], [[7], [8]])
#guard maskStart placeTwoRowsMainTwo noRide 0 == 2 && padNo placeTwoRowsMainTwo noRide 0 0 == 5 &&
  freeNo placeTwoRowsMainTwo noRide 0 == {2, 3, 4}
#guard clearAt placeTwoRowsMainTwo noRide (filledAt 2 3 4)
-- one position, at two of the other places: within the bound
#guard budTest placeThreeFree [[[6]], []] && budTest placeTwoRowsFree [[[6]], []]
-- two positions there: beyond the bound
#guard !budTest placeThreeFree [[[6, 2]], []] && !budTest placeTwoRowsFree [[[6, 1]], []]
-- the positions p and p + 2 ^ a, where a is the mask code's log-length: two positions for the main
-- row, whose tail has two entries, and one for the mask rows, so within the bound.
-- 8 coins = 2 + 2 symbols, an answer, 3 free entries
#guard budTest placeTwoRowsMainTwo [[[1, 5]], []]
-- beyond the bound only for the mask rows: two positions for the main row, two for the mask rows
#guard !budTest placeTwoRowsMainTwo [[[1, 2]], []]
-- three positions: beyond the bound for both
#guard !budTest placeTwoRowsMainTwo [[[1, 5, 3]], []]

/-! ## What the sender discloses at placeThreeFree and placeTwoRowsFree, as explicit formulas -/

/-- The concrete seed's third coordinate, as three words; fieldZ2 is its value in the extension
field. -/
def seedZ2 : Fmt.Ext3 := (6, 2, 5)
def fieldZ2 : GE := toE seedZ2
/-- The concrete challenges of the two rounds: one seed of three coordinates and a factor; then
nothing. -/
def seedsOfThree : List Fmt.Drawn :=
  [⟨[seedZ0, seedZ1, seedZ2, seedFactor], [], [], none⟩, ⟨[], [], [], none⟩]
/-- The contribution of the two data entries to the answer. The factor 1 - fieldZ2 is there because
the seed's third coordinate separates main entries from mask entries. -/
def onDataThree : GE :=
  (1 - fieldZ2) * ((1 - fieldZ1) * (1 - fieldZ0) * datumZero + (1 - fieldZ1) * fieldZ0 * datumOne)
/-- The weight of the concrete seed on free entry number j in the answer. -/
def freeWeight (j : Nat) : GE :=
  fieldZ2 * ((if j / 2 == 1 then fieldZ1 else 1 - fieldZ1) *
    (if j % 2 == 1 then fieldZ0 else 1 - fieldZ0))

#guard placeThreeFree.coordinates == 3 && placeTwoRowsFree.coordinates == 3
-- one mask row. The coins in order: main tail t, free entries u₀ u₁ u₂, pad p, mask tail t'
#guard shownR placeThreeFree 0 noRide writtenData seedsOfThree [[[6]], []] (writtenCoins _) ==
  expectedShown [6] (fun x =>
    [coinAt 0 + pointE 3 x * datumZero + pointE 3 x ^ 2 * datumOne,
      coinAt 5 + pointE 3 x * coinAt 1 + pointE 3 x ^ 2 * coinAt 2 + pointE 3 x ^ 3 * coinAt 3 +
        pointE 3 x ^ 4 * coinAt 4])
    (onDataThree + freeWeight 0 * coinAt 1 + freeWeight 1 * coinAt 2 + freeWeight 2 * coinAt 3 +
      fieldFactor * coinAt 4)
-- two mask rows. The coins in order: t u₀ u₁ u₂ p t'₀ t'₁; row 0 holds u₀ u₂, row 1 holds u₁ p
#guard shownR placeTwoRowsFree 0 noRide writtenData seedsOfThree [[[6]], []] (writtenCoins _) ==
  expectedShown [6] (fun x =>
    [coinAt 0 + pointE 3 x * datumZero + pointE 3 x ^ 2 * datumOne,
      coinAt 5 + pointE 2 x * coinAt 1 + pointE 2 x ^ 2 * coinAt 3,
      coinAt 6 + pointE 2 x * coinAt 2 + pointE 2 x ^ 2 * coinAt 4])
    (onDataThree + freeWeight 0 * coinAt 1 + freeWeight 1 * coinAt 2 + freeWeight 2 * coinAt 3 +
      fieldFactor * coinAt 4)

end OnBytes.SendSim.At.Small
