-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookWritten/RowsFirst.lean: AT THE LIBRARY's WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean) AND ITS WRITTEN SENDINGS (Johnson/G/SendsWritten.lean): OF THE
FIRST CHAIN's SENDINGS THAT ARE NO SWITCH THE ROWS (rowsIn, Honest/BookRows.lean) ARE A SPELLED LIST
OF 77: FOR EACH THE PART THAT HOLDS ITS ROUND, AND ITS COINS. No premise.
Written by the authors of the honest side of the linear claim's shared rounds (K14), in the frame's
folder, not by the frame's authors; the makers are theirs.

  bookRowsFirstW  the spelled list
  rowsFirst_test  the public test rowsAre (Honest/BookWritten/Small.lean) accepts the list
  rowsIn_first_written   **the equation**; as "later" the maker is handed WP's second chain's
                  declared rounds, written out as the book's makers write them
  rowsFirst_bite  THE TEST CAN FAIL: it rejects the list with the last row dropped, with one count
                  greater by one, and with the first two rows swapped (behind the equation: the
                  maker is evaluated once in this file)

How the labels are read. The kernel does not get past String.splitOn by itself: the maker and
isSwitch are unfolded by name and the reader of labels is rewritten by the library's splitOn_eq
(Johnson/Unfolds/SplitOn.lean); then Lean's kernel evaluates. The way was found by the authors of
the honest side of the output head's own rounds (K6), in trials of theirs.

HOW THE SPELLED LIST CAME: it was printed by Lean's evaluator and laid into this file by a program;
THE EVALUATOR IS TRUSTED FOR NOTHING: the list is held against its maker by Lean's kernel.

Limits. A fact on written values: WP's own limit stands (its values were printed off the goals'
stored full-size public files); so does the written sendings' (Johnson/G/SendsWritten.lean: the
labels and the two entries of each sending rest on one print and on a test by Lean's evaluator; no
theorem): the maker sorts by labels. NOTHING AT ANY OTHER DESCRIPTION. THAT bookRaw OR bookWhole
RETURNS IS NOT SAID; nothing on any test of the book's own. THE MAKER LEAVES THE SWITCHES OUT: of
the first chain's 82 written sendings the five whose labels bear ", the code switch of stage " are
not here (read off the written labels: no statement here counts them). No option is raised. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookWritten.Small

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **The 77 rows of the first chain's sendings that are no switch, written.** -/
def bookRowsFirstW : List (Addr × Due) :=
  [(⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨25848, 8958⟩), (⟨⟨1, some 0, 4, .K1⟩, 0⟩, ⟨0, 220⟩),
   (⟨⟨1, some 0, 6, .K1⟩, 0⟩, ⟨6792, 0⟩), (⟨⟨1, some 1, 1, .K2⟩, 0⟩, ⟨11832, 9084⟩),
   (⟨⟨1, some 1, 4, .K1⟩, 0⟩, ⟨0, 220⟩), (⟨⟨1, some 1, 6, .K1⟩, 0⟩, ⟨3069, 0⟩),
   (⟨⟨1, some 2, 1, .K2⟩, 0⟩, ⟨26070, 9086⟩), (⟨⟨1, some 2, 4, .K1⟩, 0⟩, ⟨0, 220⟩),
   (⟨⟨1, some 2, 6, .K1⟩, 0⟩, ⟨6792, 0⟩), (⟨⟨1, some 3, 1, .K2⟩, 0⟩, ⟨11832, 9084⟩),
   (⟨⟨1, some 3, 4, .K1⟩, 0⟩, ⟨0, 220⟩), (⟨⟨1, some 3, 6, .K1⟩, 0⟩, ⟨3069, 0⟩),
   (⟨⟨1, some 4, 1, .K2⟩, 0⟩, ⟨26070, 9086⟩), (⟨⟨1, some 4, 4, .K1⟩, 0⟩, ⟨0, 220⟩),
   (⟨⟨1, some 4, 6, .K1⟩, 0⟩, ⟨6792, 0⟩), (⟨⟨1, some 5, 1, .K2⟩, 0⟩, ⟨11832, 9084⟩),
   (⟨⟨1, some 5, 4, .K1⟩, 0⟩, ⟨0, 220⟩), (⟨⟨1, some 5, 6, .K1⟩, 0⟩, ⟨3069, 0⟩),
   (⟨⟨1, some 6, 1, .K2⟩, 0⟩, ⟨26070, 9086⟩), (⟨⟨1, some 6, 4, .K1⟩, 0⟩, ⟨0, 220⟩),
   (⟨⟨1, some 6, 6, .K1⟩, 0⟩, ⟨6792, 0⟩), (⟨⟨1, some 7, 1, .K2⟩, 0⟩, ⟨11832, 9084⟩),
   (⟨⟨1, some 7, 4, .K1⟩, 0⟩, ⟨0, 220⟩), (⟨⟨1, some 7, 6, .K1⟩, 0⟩, ⟨3069, 0⟩),
   (⟨⟨1, some 8, 1, .K2⟩, 0⟩, ⟨26070, 9086⟩), (⟨⟨1, some 8, 4, .K1⟩, 0⟩, ⟨0, 220⟩),
   (⟨⟨1, some 8, 6, .K1⟩, 0⟩, ⟨6792, 0⟩), (⟨⟨1, some 9, 1, .K2⟩, 0⟩, ⟨11832, 9084⟩),
   (⟨⟨1, some 9, 4, .K1⟩, 0⟩, ⟨0, 220⟩), (⟨⟨1, some 9, 6, .K1⟩, 0⟩, ⟨3069, 0⟩),
   (⟨⟨1, some 10, 1, .K2⟩, 0⟩, ⟨26070, 9086⟩), (⟨⟨1, some 10, 4, .K1⟩, 0⟩, ⟨0, 220⟩),
   (⟨⟨1, some 10, 6, .K1⟩, 0⟩, ⟨6792, 0⟩), (⟨⟨1, some 11, 1, .K2⟩, 0⟩, ⟨11832, 9084⟩),
   (⟨⟨1, some 11, 4, .K1⟩, 0⟩, ⟨0, 220⟩), (⟨⟨1, some 11, 6, .K1⟩, 0⟩, ⟨3069, 0⟩),
   (⟨⟨1, some 12, 1, .K2⟩, 0⟩, ⟨26070, 9086⟩), (⟨⟨1, some 12, 4, .K1⟩, 0⟩, ⟨0, 220⟩),
   (⟨⟨1, some 12, 6, .K1⟩, 0⟩, ⟨6792, 0⟩), (⟨⟨1, some 13, 1, .K2⟩, 0⟩, ⟨11832, 9084⟩),
   (⟨⟨1, some 13, 4, .K1⟩, 0⟩, ⟨0, 220⟩), (⟨⟨1, some 13, 6, .K1⟩, 0⟩, ⟨3069, 0⟩),
   (⟨⟨1, some 14, 1, .K2⟩, 0⟩, ⟨26070, 9086⟩), (⟨⟨1, some 14, 4, .K1⟩, 0⟩, ⟨0, 220⟩),
   (⟨⟨1, some 14, 6, .K1⟩, 0⟩, ⟨6792, 0⟩), (⟨⟨1, some 15, 1, .K2⟩, 0⟩, ⟨11832, 9084⟩),
   (⟨⟨1, some 15, 4, .K1⟩, 0⟩, ⟨0, 220⟩), (⟨⟨1, some 15, 6, .K1⟩, 0⟩, ⟨3069, 0⟩),
   (⟨⟨1, some 16, 1, .K2⟩, 0⟩, ⟨26070, 9086⟩), (⟨⟨1, some 16, 4, .K1⟩, 0⟩, ⟨0, 220⟩),
   (⟨⟨1, some 16, 6, .K1⟩, 0⟩, ⟨6792, 0⟩), (⟨⟨1, some 17, 1, .K2⟩, 0⟩, ⟨11832, 9084⟩),
   (⟨⟨1, some 17, 4, .K1⟩, 0⟩, ⟨0, 220⟩), (⟨⟨1, some 17, 6, .K1⟩, 0⟩, ⟨3069, 0⟩),
   (⟨⟨1, some 18, 1, .K2⟩, 0⟩, ⟨26070, 9086⟩), (⟨⟨1, some 18, 4, .K1⟩, 0⟩, ⟨0, 220⟩),
   (⟨⟨1, some 18, 6, .K1⟩, 0⟩, ⟨6792, 0⟩), (⟨⟨1, some 19, 1, .K2⟩, 0⟩, ⟨11832, 9084⟩),
   (⟨⟨1, some 19, 4, .K1⟩, 0⟩, ⟨0, 220⟩), (⟨⟨1, some 19, 6, .K1⟩, 0⟩, ⟨3069, 0⟩),
   (⟨⟨1, some 20, 1, .K2⟩, 0⟩, ⟨26070, 9086⟩), (⟨⟨1, some 20, 4, .K1⟩, 0⟩, ⟨0, 220⟩),
   (⟨⟨1, some 20, 6, .K1⟩, 0⟩, ⟨6792, 0⟩), (⟨⟨1, some 21, 1, .K2⟩, 0⟩, ⟨11832, 9084⟩),
   (⟨⟨1, some 21, 4, .K1⟩, 0⟩, ⟨0, 220⟩), (⟨⟨1, some 21, 6, .K1⟩, 0⟩, ⟨3069, 0⟩),
   (⟨⟨1, some 22, 1, .K2⟩, 0⟩, ⟨26070, 9086⟩), (⟨⟨1, some 22, 4, .K1⟩, 0⟩, ⟨0, 220⟩),
   (⟨⟨1, some 22, 6, .K1⟩, 0⟩, ⟨6792, 0⟩), (⟨⟨1, some 23, 1, .K2⟩, 0⟩, ⟨11832, 9084⟩),
   (⟨⟨1, some 23, 4, .K1⟩, 0⟩, ⟨0, 220⟩), (⟨⟨1, some 23, 6, .K1⟩, 0⟩, ⟨3069, 0⟩),
   (⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 9086⟩), (⟨⟨1, some 24, 5, .K1⟩, 0⟩, ⟨0, 220⟩),
   (⟨⟨1, some 24, 7, .K1⟩, 0⟩, ⟨5259, 0⟩), (⟨⟨1, none, 1, .K2⟩, 0⟩, ⟨0, 661⟩),
   (⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 4003⟩)]

/-- The test accepts the written list. -/
theorem rowsFirst_test :
    rowsAre (rowsIn WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds)))
      bookRowsFirstW = true := by
  unfold rowsIn isSwitch
  simp only [Johnson.Unfolds.splitOn_eq]
  decide +kernel

/-- **THE EQUATION: THE ROWS OF THE FIRST CHAIN's SENDINGS THAT ARE NO SWITCH.** -/
theorem rowsIn_first_written :
    rowsIn WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds)) =
      .ok bookRowsFirstW :=
  rowsAre_eq rowsFirst_test

/-- **THE TEST CAN FAIL**: the last row dropped; the first row's count of the extension field
greater by one; the first two rows swapped. -/
theorem rowsFirst_bite :
    rowsAre (rowsIn WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds)))
        bookRowsFirstW.dropLast = false ∧
      rowsAre (rowsIn WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds)))
        (((bookRowsFirstW.headD default).1, { (bookRowsFirstW.headD default).2 with
          e := (bookRowsFirstW.headD default).2.e + 1 }) :: bookRowsFirstW.drop 1) = false ∧
      rowsAre (rowsIn WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds)))
        ((bookRowsFirstW.take 2).reverse ++ bookRowsFirstW.drop 2) = false := by
  rw [rowsIn_first_written]
  decide +kernel

end ProofFile.Honest

#print axioms ProofFile.Honest.rowsFirst_test
#print axioms ProofFile.Honest.rowsIn_first_written
#print axioms ProofFile.Honest.rowsFirst_bite
