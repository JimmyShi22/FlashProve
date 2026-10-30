-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookWritten/SentFirst.lean: AT THE LIBRARY's WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean) AND ITS WRITTEN SENDINGS (Johnson/G/SendsWritten.lean): OF THE
FIRST CHAIN's SENDINGS THAT ARE NO SWITCH THE MESSAGES (sentIn, Honest/BookCarry.lean) ARE A SPELLED
LIST OF 189; AMONG THEM THERE ARE MESSAGES UNDER THE LABEL "W". No premise.
Written by the authors of the honest side of the linear claim's shared rounds (K14), in the frame's
folder, not by the frame's authors; the makers are theirs.

  sentFirstW      the spelled list: label; round; sender; number in the sending; where its coins
                  begin; how many; a fold's fresh table; mask rows alone with a sample
  sentFirstIs     a public test: the maker's answer against a list, through sentView
                  (Honest/BookWritten/Small.lean)
  sentFirst_test  it accepts the list
  sentIn_first_written   **the equation**; as "later" the maker is handed WP's second chain's
                  declared rounds, written out as the book's makers write them
  sentFirst_w     the written list's messages under the label "W" are not none: what bookRaw asks
                  behind this step; sentFirst_w_bite: under the label "w" they are none
  sentFirst_bite  THE TEST CAN FAIL: it rejects the list with the last message dropped, with one
                  count greater by one, with the first two messages swapped, and with one letter
                  more at the first label (sentFirstHeadW: the list's first message); behind the
                  equation: the maker is evaluated once in this file

How the labels are read. The kernel does not get past String.splitOn by itself: the test, the maker
and isSwitch are unfolded by name and the reader of labels is rewritten by the library's splitOn_eq
(Johnson/Unfolds/SplitOn.lean); then Lean's kernel evaluates. The way was found by the authors of
the honest side of the output head's own rounds (K6), in trials of theirs.

HOW THE SPELLED LIST CAME: it was printed by Lean's evaluator and laid into this file by a program;
THE EVALUATOR IS TRUSTED FOR NOTHING: the list is held against its maker by Lean's kernel.

Limits. A fact on written values: WP's own limit stands (its values were printed off the goals'
stored full-size public files); so does the written sendings' (Johnson/G/SendsWritten.lean: the
labels and the two entries of each sending rest on one print and on a test by Lean's evaluator; no
theorem): the maker sorts by labels, and the list spells each message's. NOTHING AT ANY OTHER
DESCRIPTION. THAT bookRaw OR bookWhole RETURNS IS NOT SAID; nothing on any test of the book's own.
THE MAKER LEAVES THE SWITCHES OUT: of the first chain's 82 written sendings the five whose labels
bear ", the code switch of stage " are not here (read off the written labels: no statement here
counts them). No option is raised. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookWritten.RowsFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **The 189 messages of the first chain's sendings that are no switch, written.** -/
def sentFirstW : List SentMsg :=
  [⟨"link 0, moment 0", 0, ⟨⟨1, some 0, 1, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨23214, 8411⟩, false, false⟩,
   ⟨"link 0, moment 0", 0, ⟨⟨1, some 0, 1, .K1⟩, 0⟩, 1, ⟨23214, 8411⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 0, moment 0", 0, ⟨⟨1, some 0, 1, .K1⟩, 0⟩, 2, ⟨25188, 8411⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 0, moment 0", 0, ⟨⟨1, some 0, 1, .K1⟩, 0⟩, 3, ⟨25848, 8411⟩, ⟨0, 236⟩, true, false⟩,
   ⟨"link 0, moment 0", 0, ⟨⟨1, some 0, 1, .K1⟩, 0⟩, 4, ⟨25848, 8647⟩, ⟨0, 311⟩, false, true⟩,
   ⟨"link 0, moment 1", 1218, ⟨⟨1, some 0, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 0, moment 2", 1221, ⟨⟨1, some 0, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨6792, 0⟩, false, false⟩,
   ⟨"link 1, moment 0", 1980, ⟨⟨1, some 1, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 1, moment 0", 1980, ⟨⟨1, some 1, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 1, moment 0", 1980, ⟨⟨1, some 1, 1, .K2⟩, 0⟩, 2, ⟨1974, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 1, moment 0", 1980, ⟨⟨1, some 1, 1, .K2⟩, 0⟩, 3, ⟨2634, 439⟩, ⟨9198, 8411⟩, false, false⟩,
   ⟨"link 1, moment 0", 1980, ⟨⟨1, some 1, 1, .K2⟩, 0⟩, 4, ⟨11832, 8850⟩, ⟨0, 234⟩, true, false⟩,
   ⟨"link 1, moment 1", 3128, ⟨⟨1, some 1, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 1, moment 2", 3131, ⟨⟨1, some 1, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨3069, 0⟩, false, false⟩,
   ⟨"link 2, moment 0", 3859, ⟨⟨1, some 2, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 2, moment 0", 3859, ⟨⟨1, some 2, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 2, moment 0", 3859, ⟨⟨1, some 2, 1, .K2⟩, 0⟩, 2, ⟨660, 439⟩, ⟨22776, 8411⟩, false, false⟩,
   ⟨"link 2, moment 0", 3859, ⟨⟨1, some 2, 1, .K2⟩, 0⟩, 3, ⟨23436, 8850⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 2, moment 0", 3859, ⟨⟨1, some 2, 1, .K2⟩, 0⟩, 4, ⟨25410, 8850⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 2, moment 0", 3859, ⟨⟨1, some 2, 1, .K2⟩, 0⟩, 5, ⟨26070, 8850⟩, ⟨0, 236⟩, true, false⟩,
   ⟨"link 2, moment 1", 5075, ⟨⟨1, some 2, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 2, moment 2", 5078, ⟨⟨1, some 2, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨6792, 0⟩, false, false⟩,
   ⟨"link 3, moment 0", 5837, ⟨⟨1, some 3, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 3, moment 0", 5837, ⟨⟨1, some 3, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 3, moment 0", 5837, ⟨⟨1, some 3, 1, .K2⟩, 0⟩, 2, ⟨1974, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 3, moment 0", 5837, ⟨⟨1, some 3, 1, .K2⟩, 0⟩, 3, ⟨2634, 439⟩, ⟨9198, 8411⟩, false, false⟩,
   ⟨"link 3, moment 0", 5837, ⟨⟨1, some 3, 1, .K2⟩, 0⟩, 4, ⟨11832, 8850⟩, ⟨0, 234⟩, true, false⟩,
   ⟨"link 3, moment 1", 6985, ⟨⟨1, some 3, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 3, moment 2", 6988, ⟨⟨1, some 3, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨3069, 0⟩, false, false⟩,
   ⟨"link 4, moment 0", 7716, ⟨⟨1, some 4, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 4, moment 0", 7716, ⟨⟨1, some 4, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 4, moment 0", 7716, ⟨⟨1, some 4, 1, .K2⟩, 0⟩, 2, ⟨660, 439⟩, ⟨22776, 8411⟩, false, false⟩,
   ⟨"link 4, moment 0", 7716, ⟨⟨1, some 4, 1, .K2⟩, 0⟩, 3, ⟨23436, 8850⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 4, moment 0", 7716, ⟨⟨1, some 4, 1, .K2⟩, 0⟩, 4, ⟨25410, 8850⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 4, moment 0", 7716, ⟨⟨1, some 4, 1, .K2⟩, 0⟩, 5, ⟨26070, 8850⟩, ⟨0, 236⟩, true, false⟩,
   ⟨"link 4, moment 1", 8932, ⟨⟨1, some 4, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 4, moment 2", 8935, ⟨⟨1, some 4, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨6792, 0⟩, false, false⟩,
   ⟨"link 5, moment 0", 9694, ⟨⟨1, some 5, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 5, moment 0", 9694, ⟨⟨1, some 5, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 5, moment 0", 9694, ⟨⟨1, some 5, 1, .K2⟩, 0⟩, 2, ⟨1974, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 5, moment 0", 9694, ⟨⟨1, some 5, 1, .K2⟩, 0⟩, 3, ⟨2634, 439⟩, ⟨9198, 8411⟩, false, false⟩,
   ⟨"link 5, moment 0", 9694, ⟨⟨1, some 5, 1, .K2⟩, 0⟩, 4, ⟨11832, 8850⟩, ⟨0, 234⟩, true, false⟩,
   ⟨"link 5, moment 1", 10842, ⟨⟨1, some 5, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 5, moment 2", 10845, ⟨⟨1, some 5, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨3069, 0⟩, false, false⟩,
   ⟨"link 6, moment 0", 11573, ⟨⟨1, some 6, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 6, moment 0", 11573, ⟨⟨1, some 6, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 6, moment 0", 11573, ⟨⟨1, some 6, 1, .K2⟩, 0⟩,
     2, ⟨660, 439⟩, ⟨22776, 8411⟩, false, false⟩,
   ⟨"link 6, moment 0", 11573, ⟨⟨1, some 6, 1, .K2⟩, 0⟩, 3, ⟨23436, 8850⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 6, moment 0", 11573, ⟨⟨1, some 6, 1, .K2⟩, 0⟩, 4, ⟨25410, 8850⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 6, moment 0", 11573, ⟨⟨1, some 6, 1, .K2⟩, 0⟩, 5, ⟨26070, 8850⟩, ⟨0, 236⟩, true, false⟩,
   ⟨"link 6, moment 1", 12789, ⟨⟨1, some 6, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 6, moment 2", 12792, ⟨⟨1, some 6, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨6792, 0⟩, false, false⟩,
   ⟨"link 7, moment 0", 13551, ⟨⟨1, some 7, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 7, moment 0", 13551, ⟨⟨1, some 7, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 7, moment 0", 13551, ⟨⟨1, some 7, 1, .K2⟩, 0⟩, 2, ⟨1974, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 7, moment 0", 13551, ⟨⟨1, some 7, 1, .K2⟩, 0⟩,
     3, ⟨2634, 439⟩, ⟨9198, 8411⟩, false, false⟩,
   ⟨"link 7, moment 0", 13551, ⟨⟨1, some 7, 1, .K2⟩, 0⟩, 4, ⟨11832, 8850⟩, ⟨0, 234⟩, true, false⟩,
   ⟨"link 7, moment 1", 14699, ⟨⟨1, some 7, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 7, moment 2", 14702, ⟨⟨1, some 7, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨3069, 0⟩, false, false⟩,
   ⟨"link 8, moment 0", 15430, ⟨⟨1, some 8, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 8, moment 0", 15430, ⟨⟨1, some 8, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 8, moment 0", 15430, ⟨⟨1, some 8, 1, .K2⟩, 0⟩,
     2, ⟨660, 439⟩, ⟨22776, 8411⟩, false, false⟩,
   ⟨"link 8, moment 0", 15430, ⟨⟨1, some 8, 1, .K2⟩, 0⟩, 3, ⟨23436, 8850⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 8, moment 0", 15430, ⟨⟨1, some 8, 1, .K2⟩, 0⟩, 4, ⟨25410, 8850⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 8, moment 0", 15430, ⟨⟨1, some 8, 1, .K2⟩, 0⟩, 5, ⟨26070, 8850⟩, ⟨0, 236⟩, true, false⟩,
   ⟨"link 8, moment 1", 16646, ⟨⟨1, some 8, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 8, moment 2", 16649, ⟨⟨1, some 8, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨6792, 0⟩, false, false⟩,
   ⟨"link 9, moment 0", 17408, ⟨⟨1, some 9, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 9, moment 0", 17408, ⟨⟨1, some 9, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 9, moment 0", 17408, ⟨⟨1, some 9, 1, .K2⟩, 0⟩, 2, ⟨1974, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 9, moment 0", 17408, ⟨⟨1, some 9, 1, .K2⟩, 0⟩,
     3, ⟨2634, 439⟩, ⟨9198, 8411⟩, false, false⟩,
   ⟨"link 9, moment 0", 17408, ⟨⟨1, some 9, 1, .K2⟩, 0⟩, 4, ⟨11832, 8850⟩, ⟨0, 234⟩, true, false⟩,
   ⟨"link 9, moment 1", 18556, ⟨⟨1, some 9, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 9, moment 2", 18559, ⟨⟨1, some 9, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨3069, 0⟩, false, false⟩,
   ⟨"link 10, moment 0", 19287, ⟨⟨1, some 10, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 10, moment 0", 19287, ⟨⟨1, some 10, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 10, moment 0", 19287, ⟨⟨1, some 10, 1, .K2⟩, 0⟩,
     2, ⟨660, 439⟩, ⟨22776, 8411⟩, false, false⟩,
   ⟨"link 10, moment 0", 19287, ⟨⟨1, some 10, 1, .K2⟩, 0⟩,
     3, ⟨23436, 8850⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 10, moment 0", 19287, ⟨⟨1, some 10, 1, .K2⟩, 0⟩,
     4, ⟨25410, 8850⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 10, moment 0", 19287, ⟨⟨1, some 10, 1, .K2⟩, 0⟩, 5, ⟨26070, 8850⟩, ⟨0, 236⟩, true, false⟩,
   ⟨"link 10, moment 1", 20503, ⟨⟨1, some 10, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 10, moment 2", 20506, ⟨⟨1, some 10, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨6792, 0⟩, false, false⟩,
   ⟨"link 11, moment 0", 21265, ⟨⟨1, some 11, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 11, moment 0", 21265, ⟨⟨1, some 11, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 11, moment 0", 21265, ⟨⟨1, some 11, 1, .K2⟩, 0⟩, 2, ⟨1974, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 11, moment 0", 21265, ⟨⟨1, some 11, 1, .K2⟩, 0⟩,
     3, ⟨2634, 439⟩, ⟨9198, 8411⟩, false, false⟩,
   ⟨"link 11, moment 0", 21265, ⟨⟨1, some 11, 1, .K2⟩, 0⟩, 4, ⟨11832, 8850⟩, ⟨0, 234⟩, true, false⟩,
   ⟨"link 11, moment 1", 22413, ⟨⟨1, some 11, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 11, moment 2", 22416, ⟨⟨1, some 11, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨3069, 0⟩, false, false⟩,
   ⟨"link 12, moment 0", 23144, ⟨⟨1, some 12, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 12, moment 0", 23144, ⟨⟨1, some 12, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 12, moment 0", 23144, ⟨⟨1, some 12, 1, .K2⟩, 0⟩,
     2, ⟨660, 439⟩, ⟨22776, 8411⟩, false, false⟩,
   ⟨"link 12, moment 0", 23144, ⟨⟨1, some 12, 1, .K2⟩, 0⟩,
     3, ⟨23436, 8850⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 12, moment 0", 23144, ⟨⟨1, some 12, 1, .K2⟩, 0⟩,
     4, ⟨25410, 8850⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 12, moment 0", 23144, ⟨⟨1, some 12, 1, .K2⟩, 0⟩, 5, ⟨26070, 8850⟩, ⟨0, 236⟩, true, false⟩,
   ⟨"link 12, moment 1", 24360, ⟨⟨1, some 12, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 12, moment 2", 24363, ⟨⟨1, some 12, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨6792, 0⟩, false, false⟩,
   ⟨"link 13, moment 0", 25122, ⟨⟨1, some 13, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 13, moment 0", 25122, ⟨⟨1, some 13, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 13, moment 0", 25122, ⟨⟨1, some 13, 1, .K2⟩, 0⟩, 2, ⟨1974, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 13, moment 0", 25122, ⟨⟨1, some 13, 1, .K2⟩, 0⟩,
     3, ⟨2634, 439⟩, ⟨9198, 8411⟩, false, false⟩,
   ⟨"link 13, moment 0", 25122, ⟨⟨1, some 13, 1, .K2⟩, 0⟩, 4, ⟨11832, 8850⟩, ⟨0, 234⟩, true, false⟩,
   ⟨"link 13, moment 1", 26270, ⟨⟨1, some 13, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 13, moment 2", 26273, ⟨⟨1, some 13, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨3069, 0⟩, false, false⟩,
   ⟨"link 14, moment 0", 27001, ⟨⟨1, some 14, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 14, moment 0", 27001, ⟨⟨1, some 14, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 14, moment 0", 27001, ⟨⟨1, some 14, 1, .K2⟩, 0⟩,
     2, ⟨660, 439⟩, ⟨22776, 8411⟩, false, false⟩,
   ⟨"link 14, moment 0", 27001, ⟨⟨1, some 14, 1, .K2⟩, 0⟩,
     3, ⟨23436, 8850⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 14, moment 0", 27001, ⟨⟨1, some 14, 1, .K2⟩, 0⟩,
     4, ⟨25410, 8850⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 14, moment 0", 27001, ⟨⟨1, some 14, 1, .K2⟩, 0⟩, 5, ⟨26070, 8850⟩, ⟨0, 236⟩, true, false⟩,
   ⟨"link 14, moment 1", 28217, ⟨⟨1, some 14, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 14, moment 2", 28220, ⟨⟨1, some 14, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨6792, 0⟩, false, false⟩,
   ⟨"link 15, moment 0", 28979, ⟨⟨1, some 15, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 15, moment 0", 28979, ⟨⟨1, some 15, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 15, moment 0", 28979, ⟨⟨1, some 15, 1, .K2⟩, 0⟩, 2, ⟨1974, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 15, moment 0", 28979, ⟨⟨1, some 15, 1, .K2⟩, 0⟩,
     3, ⟨2634, 439⟩, ⟨9198, 8411⟩, false, false⟩,
   ⟨"link 15, moment 0", 28979, ⟨⟨1, some 15, 1, .K2⟩, 0⟩, 4, ⟨11832, 8850⟩, ⟨0, 234⟩, true, false⟩,
   ⟨"link 15, moment 1", 30127, ⟨⟨1, some 15, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 15, moment 2", 30130, ⟨⟨1, some 15, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨3069, 0⟩, false, false⟩,
   ⟨"link 16, moment 0", 30858, ⟨⟨1, some 16, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 16, moment 0", 30858, ⟨⟨1, some 16, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 16, moment 0", 30858, ⟨⟨1, some 16, 1, .K2⟩, 0⟩,
     2, ⟨660, 439⟩, ⟨22776, 8411⟩, false, false⟩,
   ⟨"link 16, moment 0", 30858, ⟨⟨1, some 16, 1, .K2⟩, 0⟩,
     3, ⟨23436, 8850⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 16, moment 0", 30858, ⟨⟨1, some 16, 1, .K2⟩, 0⟩,
     4, ⟨25410, 8850⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 16, moment 0", 30858, ⟨⟨1, some 16, 1, .K2⟩, 0⟩, 5, ⟨26070, 8850⟩, ⟨0, 236⟩, true, false⟩,
   ⟨"link 16, moment 1", 32074, ⟨⟨1, some 16, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 16, moment 2", 32077, ⟨⟨1, some 16, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨6792, 0⟩, false, false⟩,
   ⟨"link 17, moment 0", 32836, ⟨⟨1, some 17, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 17, moment 0", 32836, ⟨⟨1, some 17, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 17, moment 0", 32836, ⟨⟨1, some 17, 1, .K2⟩, 0⟩, 2, ⟨1974, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 17, moment 0", 32836, ⟨⟨1, some 17, 1, .K2⟩, 0⟩,
     3, ⟨2634, 439⟩, ⟨9198, 8411⟩, false, false⟩,
   ⟨"link 17, moment 0", 32836, ⟨⟨1, some 17, 1, .K2⟩, 0⟩, 4, ⟨11832, 8850⟩, ⟨0, 234⟩, true, false⟩,
   ⟨"link 17, moment 1", 33984, ⟨⟨1, some 17, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 17, moment 2", 33987, ⟨⟨1, some 17, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨3069, 0⟩, false, false⟩,
   ⟨"link 18, moment 0", 34715, ⟨⟨1, some 18, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 18, moment 0", 34715, ⟨⟨1, some 18, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 18, moment 0", 34715, ⟨⟨1, some 18, 1, .K2⟩, 0⟩,
     2, ⟨660, 439⟩, ⟨22776, 8411⟩, false, false⟩,
   ⟨"link 18, moment 0", 34715, ⟨⟨1, some 18, 1, .K2⟩, 0⟩,
     3, ⟨23436, 8850⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 18, moment 0", 34715, ⟨⟨1, some 18, 1, .K2⟩, 0⟩,
     4, ⟨25410, 8850⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 18, moment 0", 34715, ⟨⟨1, some 18, 1, .K2⟩, 0⟩, 5, ⟨26070, 8850⟩, ⟨0, 236⟩, true, false⟩,
   ⟨"link 18, moment 1", 35931, ⟨⟨1, some 18, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 18, moment 2", 35934, ⟨⟨1, some 18, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨6792, 0⟩, false, false⟩,
   ⟨"link 19, moment 0", 36693, ⟨⟨1, some 19, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 19, moment 0", 36693, ⟨⟨1, some 19, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 19, moment 0", 36693, ⟨⟨1, some 19, 1, .K2⟩, 0⟩, 2, ⟨1974, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 19, moment 0", 36693, ⟨⟨1, some 19, 1, .K2⟩, 0⟩,
     3, ⟨2634, 439⟩, ⟨9198, 8411⟩, false, false⟩,
   ⟨"link 19, moment 0", 36693, ⟨⟨1, some 19, 1, .K2⟩, 0⟩, 4, ⟨11832, 8850⟩, ⟨0, 234⟩, true, false⟩,
   ⟨"link 19, moment 1", 37841, ⟨⟨1, some 19, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 19, moment 2", 37844, ⟨⟨1, some 19, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨3069, 0⟩, false, false⟩,
   ⟨"link 20, moment 0", 38572, ⟨⟨1, some 20, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 20, moment 0", 38572, ⟨⟨1, some 20, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 20, moment 0", 38572, ⟨⟨1, some 20, 1, .K2⟩, 0⟩,
     2, ⟨660, 439⟩, ⟨22776, 8411⟩, false, false⟩,
   ⟨"link 20, moment 0", 38572, ⟨⟨1, some 20, 1, .K2⟩, 0⟩,
     3, ⟨23436, 8850⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 20, moment 0", 38572, ⟨⟨1, some 20, 1, .K2⟩, 0⟩,
     4, ⟨25410, 8850⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 20, moment 0", 38572, ⟨⟨1, some 20, 1, .K2⟩, 0⟩, 5, ⟨26070, 8850⟩, ⟨0, 236⟩, true, false⟩,
   ⟨"link 20, moment 1", 39788, ⟨⟨1, some 20, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 20, moment 2", 39791, ⟨⟨1, some 20, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨6792, 0⟩, false, false⟩,
   ⟨"link 21, moment 0", 40550, ⟨⟨1, some 21, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 21, moment 0", 40550, ⟨⟨1, some 21, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 21, moment 0", 40550, ⟨⟨1, some 21, 1, .K2⟩, 0⟩, 2, ⟨1974, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 21, moment 0", 40550, ⟨⟨1, some 21, 1, .K2⟩, 0⟩,
     3, ⟨2634, 439⟩, ⟨9198, 8411⟩, false, false⟩,
   ⟨"link 21, moment 0", 40550, ⟨⟨1, some 21, 1, .K2⟩, 0⟩, 4, ⟨11832, 8850⟩, ⟨0, 234⟩, true, false⟩,
   ⟨"link 21, moment 1", 41698, ⟨⟨1, some 21, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 21, moment 2", 41701, ⟨⟨1, some 21, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨3069, 0⟩, false, false⟩,
   ⟨"link 22, moment 0", 42429, ⟨⟨1, some 22, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 22, moment 0", 42429, ⟨⟨1, some 22, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 22, moment 0", 42429, ⟨⟨1, some 22, 1, .K2⟩, 0⟩,
     2, ⟨660, 439⟩, ⟨22776, 8411⟩, false, false⟩,
   ⟨"link 22, moment 0", 42429, ⟨⟨1, some 22, 1, .K2⟩, 0⟩,
     3, ⟨23436, 8850⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 22, moment 0", 42429, ⟨⟨1, some 22, 1, .K2⟩, 0⟩,
     4, ⟨25410, 8850⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 22, moment 0", 42429, ⟨⟨1, some 22, 1, .K2⟩, 0⟩, 5, ⟨26070, 8850⟩, ⟨0, 236⟩, true, false⟩,
   ⟨"link 22, moment 1", 43645, ⟨⟨1, some 22, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 22, moment 2", 43648, ⟨⟨1, some 22, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨6792, 0⟩, false, false⟩,
   ⟨"link 23, moment 0", 44407, ⟨⟨1, some 23, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 23, moment 0", 44407, ⟨⟨1, some 23, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨1974, 0⟩, false, false⟩,
   ⟨"link 23, moment 0", 44407, ⟨⟨1, some 23, 1, .K2⟩, 0⟩, 2, ⟨1974, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 23, moment 0", 44407, ⟨⟨1, some 23, 1, .K2⟩, 0⟩,
     3, ⟨2634, 439⟩, ⟨9198, 8411⟩, false, false⟩,
   ⟨"link 23, moment 0", 44407, ⟨⟨1, some 23, 1, .K2⟩, 0⟩, 4, ⟨11832, 8850⟩, ⟨0, 234⟩, true, false⟩,
   ⟨"link 23, moment 1", 45555, ⟨⟨1, some 23, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 23, moment 2", 45558, ⟨⟨1, some 23, 6, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨3069, 0⟩, false, false⟩,
   ⟨"link 24, moment 0", 46287, ⟨⟨1, some 24, 2, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 24, moment 0", 46287, ⟨⟨1, some 24, 2, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨660, 0⟩, false, false⟩,
   ⟨"link 24, moment 0", 46287, ⟨⟨1, some 24, 2, .K2⟩, 0⟩,
     2, ⟨660, 439⟩, ⟨22557, 8411⟩, false, false⟩,
   ⟨"link 24, moment 0", 46287, ⟨⟨1, some 24, 2, .K2⟩, 0⟩, 3, ⟨23217, 8850⟩, ⟨0, 236⟩, true, false⟩,
   ⟨"link 24, moment 1", 47451, ⟨⟨1, some 24, 5, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 220⟩, false, false⟩,
   ⟨"link 24, moment 2", 47454, ⟨⟨1, some 24, 7, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨5259, 0⟩, false, false⟩,
   ⟨"link 25, moment 0", 48235, ⟨⟨1, none, 1, .K2⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 439⟩, false, false⟩,
   ⟨"link 25, moment 0", 48235, ⟨⟨1, none, 1, .K2⟩, 0⟩, 1, ⟨0, 439⟩, ⟨0, 222⟩, true, false⟩,
   ⟨"W", 48290, ⟨⟨1, none, 4, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 3882⟩, false, false⟩,
   ⟨"W", 48290, ⟨⟨1, none, 4, .K1⟩, 0⟩, 1, ⟨0, 3882⟩, ⟨0, 121⟩, true, false⟩]

/-- The written list's first message: it serves the negative line sentFirst_bite alone. -/
def sentFirstHeadW : SentMsg :=
  sentFirstW.headD ⟨"", 0, default, 0, default, default, false, false⟩

/-- A public test: the messages of the first chain's sendings that are no switch against a list of
pairs of tuples. -/
def sentFirstIs (t : List ((String × Nat × Addr × Nat) × (Due × Due × Bool × Bool))) : Bool :=
  match sentIn WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds)) with
  | .ok l => decide (l.map sentView = t)
  | .error _ => false

/-- It accepts the written list's pairs of tuples. -/
theorem sentFirst_test : sentFirstIs (sentFirstW.map sentView) = true := by
  unfold sentFirstIs sentIn isSwitch
  simp only [Johnson.Unfolds.splitOn_eq]
  decide +kernel

/-- **THE EQUATION: THE MESSAGES OF THE FIRST CHAIN's SENDINGS THAT ARE NO SWITCH.** -/
theorem sentIn_first_written :
    sentIn WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds)) = .ok sentFirstW := by
  have h := sentFirst_test
  unfold sentFirstIs at h
  cases hs : sentIn WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds)) with
  | error w =>
    rw [hs] at h
    cases h
  | ok l =>
    rw [hs] at h
    exact congrArg Except.ok (List.map_injective_iff.2 sentView_inj (of_decide_eq_true h))

/-- **The written list has messages under the label "W".** -/
theorem sentFirst_w : (sentFirstW.filter fun m => m.label == "W").isEmpty = false := by
  decide +kernel

/-- **That question can be answered the other way**: under the label "w", which no member bears,
the written list has no message. -/
theorem sentFirst_w_bite : (sentFirstW.filter fun m => m.label == "w").isEmpty = true := by
  decide +kernel

/-- **THE TEST CAN FAIL**: the last message dropped; the first message's count of the base field
greater by one; the first two swapped; one letter more at the first label. -/
theorem sentFirst_bite :
    sentFirstIs (sentFirstW.map sentView).dropLast = false ∧
      sentFirstIs (sentView { sentFirstHeadW with
        count := ⟨sentFirstHeadW.count.f + 1, sentFirstHeadW.count.e⟩ } ::
          (sentFirstW.map sentView).drop 1) = false ∧
      sentFirstIs (((sentFirstW.map sentView).take 2).reverse ++
        (sentFirstW.map sentView).drop 2) = false ∧
      sentFirstIs (sentView { sentFirstHeadW with label := sentFirstHeadW.label ++ "x" } ::
        (sentFirstW.map sentView).drop 1) = false := by
  unfold sentFirstIs
  rw [sentIn_first_written]
  decide +kernel

end ProofFile.Honest

#print axioms ProofFile.Honest.sentFirst_test
#print axioms ProofFile.Honest.sentIn_first_written
#print axioms ProofFile.Honest.sentFirst_w
#print axioms ProofFile.Honest.sentFirst_w_bite
#print axioms ProofFile.Honest.sentFirst_bite
