-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawBookRowsWritten.lean: AT THE LIBRARY's WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean) AND ITS WRITTEN SENDINGS (Johnson/G/SendsWritten.lean): WHATEVER
BOOK THE FRAME's bookRaw (Johnson/Desc/ProofFile/Honest/BookWhole.lean) RETURNS, AT ANY MERGES: ITS
ROWS ARE THREE WRITTEN LISTS OF 78, 5 AND 1, WITH THEIR COUNTS; AND THE FIRST AND THE THIRD OF THE
BOOK's OWN ELEVEN TESTS (ProverCoinCounts.clauses, Honest/Frame.lean) ACCEPT IT. Three definitions; statements
with their proofs.

  rawRowsFirstW, rawRowsSharedW, rawRowsSecondW   the three lists: rowsIn's written rows, the
                  switches' behind them, at the shared chain the own fresh table's row behind these
  rawBookRows_written   **W.first, W.shared and W.second are these**: no evaluation: by bookRaw_rows
                  (Honest/BookRawRows.lean), the six equations of Honest/BookWritten/ and
                  AtFullSide/K14/SwitchesWritten.lean, rawTail_written and rawOwnRow_written
                  (AtFullSide/K14/RawSmallWritten.lean). A weaker kin: rawRows_addrs
                  (AtFullSide/K14/RawRowsWritten.lean): the 84 addresses in one row
  raw1_test, clause1_written   **"a row stands at no place of its chain": no such row**
  raw3_test, clause3_written   **"a place states more mask words than its parts have coins": no
                  such place**
  raw1_bite, raw3_bite   THE TWO TESTS CAN FAIL: with a row of the shared chain laid in front of the
                  first chain's; with the first row's count 0

The two conclusions are, to the letter, the premises h1 and h3 of clauses_all_of_each
(Honest/BookWordOf.lean) at this book and WP. raw1_test and raw3_test are evaluations by Lean's
kernel at the written lists; the third walks the mask words that all sub-protocols of WP state.

No option is raised. The file lies in the side library because it imports files of it.

Limits. IMPLICATIONS FROM "bookRaw RETURNS W", AT ANY MERGES: that it returns is had at
mergesByName's merges alone (bookRaw_returns_written, AtFullSide/K14/RawReturnsWritten.lean): at
others these statements may say nothing. A fact on written values: WP's own limit and the written
sendings' stand. NOTHING AT ANY OTHER DESCRIPTION. 78, 5 and 1 are counts of written lists; no
statement. TWO OF ELEVEN TESTS: nothing on the others; THAT bookWhole RETURNS IS NOT SAID. What it
is good for that a test accepts is the frame's laws' to say. Nothing on soundness, on completeness
or on what is hidden; no property.
-/
import AtFullSide.K14.RawSmallWritten
import Johnson.Desc.ProofFile.Honest.BookRawRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **The first chain's 78 rows, written.** -/
def rawRowsFirstW : List (Addr × Due) := bookRowsFirstW ++ switchFirstW

/-- **The shared chain's five rows, written.** -/
def rawRowsSharedW : List (Addr × Due) :=
  rowsSharedW ++ switchSharedW ++ [(⟨⟨2, none, 10, .K12⟩, 0⟩, ⟨0, 161⟩)]

/-- **The second chain's one row, written.** -/
def rawRowsSecondW : List (Addr × Due) := [] ++ switchSecondW

/-- **WHATEVER BOOK bookRaw RETURNS AT THE WRITTEN DESCRIPTION: ITS ROWS, WITH THEIR COUNTS.**
CONDITIONAL: that it returns W. -/
theorem rawBookRows_written (M : Merges) (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2 M = .ok W) :
    W.first = rawRowsFirstW ∧ W.shared = rawRowsSharedW ∧ W.second = rawRowsSecondW := by
  obtain ⟨r0, r1, r2, s0, s1, s2, tail, hr0, hr1, hr2, hs0, hs1, hs2, ht, e1, e2, e3, -⟩ :=
    bookRaw_rows h
  obtain rfl : bookRowsFirstW = r0 := Except.ok.inj (rowsIn_first_written.symm.trans hr0)
  obtain rfl : rowsSharedW = r1 := Except.ok.inj (rowsIn_shared_written.symm.trans hr1)
  obtain rfl : [] = r2 := Except.ok.inj (rowsIn_second_written.symm.trans hr2)
  obtain rfl : switchFirstW = s0 := Except.ok.inj (switchRows_first_written.symm.trans hs0)
  obtain rfl : switchSharedW = s1 := Except.ok.inj (switchRows_shared_written.symm.trans hs1)
  obtain rfl : switchSecondW = s2 := Except.ok.inj (switchRows_second_written.symm.trans hs2)
  obtain rfl : 152 = tail := Except.ok.inj (rawTail_written.symm.trans ht)
  rw [rawOwnRow_written] at e2
  exact ⟨e1, e2, e3⟩

/-- The first test's Bool at the written rows. -/
theorem raw1_test :
    (rawRowsFirstW.all (fun r => (WP.first.blocksInOrder.map (·.place)).contains r.1.place) &&
      rawRowsSharedW.all (fun r => (WP.shared.blocksInOrder.map (·.place)).contains r.1.place) &&
      rawRowsSecondW.all fun r => (WP.second.blocksInOrder.map (·.place)).contains r.1.place) = true := by
  decide +kernel

/-- **THE FIRST TEST ACCEPTS THE RAW BOOK.** CONDITIONAL: that bookRaw returns W. -/
theorem clause1_written (M : Merges) (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2 M = .ok W) :
    (W.first.all (fun r => (WP.first.blocksInOrder.map (·.place)).contains r.1.place) &&
      W.shared.all (fun r => (WP.shared.blocksInOrder.map (·.place)).contains r.1.place) &&
      W.second.all fun r => (WP.second.blocksInOrder.map (·.place)).contains r.1.place) = true := by
  obtain ⟨e1, e2, e3⟩ := rawBookRows_written M W h
  rw [e1, e2, e3]
  exact raw1_test

/-- The third test's Bool at the written rows. -/
theorem raw3_test :
    (masksOk WP.first.blocksInOrder rawRowsFirstW && masksOk WP.shared.blocksInOrder rawRowsSharedW &&
      masksOk WP.second.blocksInOrder rawRowsSecondW) = true := by
  decide +kernel

/-- **THE THIRD TEST ACCEPTS THE RAW BOOK.** CONDITIONAL: that bookRaw returns W. -/
theorem clause3_written (M : Merges) (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2 M = .ok W) :
    (masksOk WP.first.blocksInOrder W.first && masksOk WP.shared.blocksInOrder W.shared &&
      masksOk WP.second.blocksInOrder W.second) = true := by
  obtain ⟨e1, e2, e3⟩ := rawBookRows_written M W h
  rw [e1, e2, e3]
  exact raw3_test

/-- **THE FIRST TEST CAN FAIL**: a row of the shared chain laid in front of the first chain's. -/
theorem raw1_bite :
    (((⟨⟨2, none, 9, .K12⟩, 1⟩, ⟨0, 1⟩) :: rawRowsFirstW).all
        (fun r => (WP.first.blocksInOrder.map (·.place)).contains r.1.place) &&
      rawRowsSharedW.all (fun r => (WP.shared.blocksInOrder.map (·.place)).contains r.1.place) &&
      rawRowsSecondW.all fun r => (WP.second.blocksInOrder.map (·.place)).contains r.1.place) = false := by
  decide +kernel

/-- **THE THIRD TEST CAN FAIL**: the first row's count 0. -/
theorem raw3_bite :
    (masksOk WP.first.blocksInOrder (((rawRowsFirstW.headD default).1, ⟨0, 0⟩) :: rawRowsFirstW.drop 1) &&
      masksOk WP.shared.blocksInOrder rawRowsSharedW && masksOk WP.second.blocksInOrder rawRowsSecondW) = false := by
  decide +kernel

end AtFullSide.K14

#print axioms AtFullSide.K14.rawBookRows_written
#print axioms AtFullSide.K14.raw1_test
#print axioms AtFullSide.K14.clause1_written
#print axioms AtFullSide.K14.raw3_test
#print axioms AtFullSide.K14.clause3_written
#print axioms AtFullSide.K14.raw1_bite
#print axioms AtFullSide.K14.raw3_bite
