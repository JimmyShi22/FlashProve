-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/FoldsWritten.lean: AT THE LIBRARY's WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean) AND ITS WRITTEN SENDINGS (Johnson/G/SendsWritten.lean): THE
ENTRIES BY WHICH FOLDS SPEND THE FRESH TABLES THAT THE FIRST CHAIN's SENDINGS SEND AHEAD (the
frame's foldEntries, Johnson/Desc/ProofFile/Honest/BookFolds.lean) ARE A SPELLED LIST OF 27, NAMES
AND ALL; AT THE SECOND CHAIN THE MAKER RETURNS THE EMPTY LIST. No premise. Definitions and
statements, each with its proof.

  foldsFirstW     the spelled list: name; owner; start; count; the part that is handed the run;
                  true: spent
  foldsAre, foldsAre_eq   a public test: a maker's answer against a list of tuples, through
                  aheadView (Johnson/Desc/ProofFile/Honest/K14/SharedAheadWritten.lean: the frame's
                  Ahead derives no test of equality); what its yes says
  foldsFirst_test   it accepts the written list's tuples: THE ONE DEAR EVALUATION
  foldEntries_first_written   **the equation at the first chain**; "later" is the second chain's
                  plan, as the book's maker hands it
  foldEntries_second_written   **the equation at the second chain**: IT SAYS LITTLE: see Limits
  foldsFirst_bite   THE TEST CAN FAIL: it rejects the list with the last entry dropped, with one
                  start greater by one, with the first two entries swapped, and with one letter
                  more at the first name (behind the equation: the maker is evaluated once)

NO OPTION IS RAISED. WHY THE FILE LIES IN THE SIDE LIBRARY: as far as seen, its one dear evaluation
wants a larger stack than the main library's files are compiled with. In trials the same sentence in
form, in modules compiled with that smaller stack, failed; with maxRecDepth and maxHeartbeats raised
it failed there with Lean's words "deep recursion was detected at 'expression equality test'
(potential solution: increase elaboration stack size using the `lean --tstack` flag)"; the same
bytes compiled with the stack that this side library's files get (lakefile.toml: --tstack=131072)
went through; so did they with either option alone, and so does this file with neither. Why the
recursion is deep (a reading, not shown): the first chain has 48,293 rounds, and the maker takes a
round's number off a walk along all rounds in front of it.

How the labels are read. The kernel does not get past String.splitOn by itself: the maker and
isSwitch are unfolded by name and the reader of labels is rewritten by the library's splitOn_eq
(Johnson/Unfolds/SplitOn.lean); then Lean's kernel evaluates.

HOW THE SPELLED LIST CAME: it was printed by Lean's evaluator and laid into this file by a program;
THE EVALUATOR IS TRUSTED FOR NOTHING: the list is held against its maker by Lean's kernel.

Limits. A fact on written values: WP's own limit stands (its values were printed off the goals'
stored full-size public files); so does the written sendings' (the labels and the two entries of
each sending rest on one print and on a test by Lean's evaluator; no theorem): the maker leaves out
the sendings whose labels are switches'. NOTHING AT ANY OTHER DESCRIPTION. THAT spendingBook,
bookRaw OR bookWhole RETURNS IS NOT SAID; nothing on any test of the book's own. THE EQUATION AT THE
SECOND CHAIN SAYS LITTLE: all four written sendings of that chain are switches' (read off their
labels: no statement here counts them), so the maker's loop is never entered: what is shown is that
the sendings are as many as the chain's rounds "SEND seed". WHICH FOLD SPENDS A FRESH TABLE IS THE
MAKER's OWN TAKING: the first fold behind its sending. foldEntries_second_written has no negative
line. Nothing on soundness, on completeness or on what is hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.SharedAheadWritten
import Johnson.Desc.ProofFile.Honest.BookWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **The 27 entries by which folds spend the first chain's fresh tables, written.** -/
def foldsFirstW : List Ahead :=
  [⟨"the fold's fresh mask to 1.0.11.0: fold", ⟨⟨1, some 0, 1, .K1⟩, 0⟩,
     ⟨25848, 8411⟩, ⟨0, 17⟩, ⟨⟨1, some 0, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.1.11.0: fold", ⟨⟨1, some 1, 1, .K2⟩, 0⟩,
     ⟨11832, 8850⟩, ⟨0, 15⟩, ⟨⟨1, some 1, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.2.11.0: fold", ⟨⟨1, some 2, 1, .K2⟩, 0⟩,
     ⟨26070, 8850⟩, ⟨0, 17⟩, ⟨⟨1, some 2, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.3.11.0: fold", ⟨⟨1, some 3, 1, .K2⟩, 0⟩,
     ⟨11832, 8850⟩, ⟨0, 15⟩, ⟨⟨1, some 3, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.4.11.0: fold", ⟨⟨1, some 4, 1, .K2⟩, 0⟩,
     ⟨26070, 8850⟩, ⟨0, 17⟩, ⟨⟨1, some 4, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.5.11.0: fold", ⟨⟨1, some 5, 1, .K2⟩, 0⟩,
     ⟨11832, 8850⟩, ⟨0, 15⟩, ⟨⟨1, some 5, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.6.11.0: fold", ⟨⟨1, some 6, 1, .K2⟩, 0⟩,
     ⟨26070, 8850⟩, ⟨0, 17⟩, ⟨⟨1, some 6, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.7.11.0: fold", ⟨⟨1, some 7, 1, .K2⟩, 0⟩,
     ⟨11832, 8850⟩, ⟨0, 15⟩, ⟨⟨1, some 7, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.8.11.0: fold", ⟨⟨1, some 8, 1, .K2⟩, 0⟩,
     ⟨26070, 8850⟩, ⟨0, 17⟩, ⟨⟨1, some 8, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.9.11.0: fold", ⟨⟨1, some 9, 1, .K2⟩, 0⟩,
     ⟨11832, 8850⟩, ⟨0, 15⟩, ⟨⟨1, some 9, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.10.11.0: fold", ⟨⟨1, some 10, 1, .K2⟩, 0⟩,
     ⟨26070, 8850⟩, ⟨0, 17⟩, ⟨⟨1, some 10, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.11.11.0: fold", ⟨⟨1, some 11, 1, .K2⟩, 0⟩,
     ⟨11832, 8850⟩, ⟨0, 15⟩, ⟨⟨1, some 11, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.12.11.0: fold", ⟨⟨1, some 12, 1, .K2⟩, 0⟩,
     ⟨26070, 8850⟩, ⟨0, 17⟩, ⟨⟨1, some 12, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.13.11.0: fold", ⟨⟨1, some 13, 1, .K2⟩, 0⟩,
     ⟨11832, 8850⟩, ⟨0, 15⟩, ⟨⟨1, some 13, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.14.11.0: fold", ⟨⟨1, some 14, 1, .K2⟩, 0⟩,
     ⟨26070, 8850⟩, ⟨0, 17⟩, ⟨⟨1, some 14, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.15.11.0: fold", ⟨⟨1, some 15, 1, .K2⟩, 0⟩,
     ⟨11832, 8850⟩, ⟨0, 15⟩, ⟨⟨1, some 15, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.16.11.0: fold", ⟨⟨1, some 16, 1, .K2⟩, 0⟩,
     ⟨26070, 8850⟩, ⟨0, 17⟩, ⟨⟨1, some 16, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.17.11.0: fold", ⟨⟨1, some 17, 1, .K2⟩, 0⟩,
     ⟨11832, 8850⟩, ⟨0, 15⟩, ⟨⟨1, some 17, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.18.11.0: fold", ⟨⟨1, some 18, 1, .K2⟩, 0⟩,
     ⟨26070, 8850⟩, ⟨0, 17⟩, ⟨⟨1, some 18, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.19.11.0: fold", ⟨⟨1, some 19, 1, .K2⟩, 0⟩,
     ⟨11832, 8850⟩, ⟨0, 15⟩, ⟨⟨1, some 19, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.20.11.0: fold", ⟨⟨1, some 20, 1, .K2⟩, 0⟩,
     ⟨26070, 8850⟩, ⟨0, 17⟩, ⟨⟨1, some 20, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.21.11.0: fold", ⟨⟨1, some 21, 1, .K2⟩, 0⟩,
     ⟨11832, 8850⟩, ⟨0, 15⟩, ⟨⟨1, some 21, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.22.11.0: fold", ⟨⟨1, some 22, 1, .K2⟩, 0⟩,
     ⟨26070, 8850⟩, ⟨0, 17⟩, ⟨⟨1, some 22, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.23.11.0: fold", ⟨⟨1, some 23, 1, .K2⟩, 0⟩,
     ⟨11832, 8850⟩, ⟨0, 15⟩, ⟨⟨1, some 23, 11, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.24.13.0: fold", ⟨⟨1, some 24, 2, .K2⟩, 0⟩,
     ⟨23217, 8850⟩, ⟨0, 17⟩, ⟨⟨1, some 24, 13, .K10⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 1.-.2.0: fold", ⟨⟨1, none, 1, .K2⟩, 0⟩,
     ⟨0, 439⟩, ⟨0, 3⟩, ⟨⟨1, none, 2, .K12⟩, 0⟩, true⟩,
   ⟨"the fold's fresh mask to 3.-.2.0: fold", ⟨⟨1, none, 4, .K1⟩, 0⟩,
     ⟨0, 3882⟩, ⟨0, 11⟩, ⟨⟨3, none, 2, .K12⟩, 0⟩, true⟩]

/-- A public test: a maker's answer against a list of tuples. -/
def foldsAre (x : Except String (List Ahead))
    (t : List (String × Addr × Due × Due × Addr × Bool)) : Bool :=
  match x with
  | .ok l => decide (l.map aheadView = t)
  | .error _ => false

/-- What its yes says, at a list's own tuples. -/
theorem foldsAre_eq {x : Except String (List Ahead)} {l : List Ahead}
    (h : foldsAre x (l.map aheadView) = true) : x = .ok l := by
  cases x with
  | error e => cases h
  | ok l' =>
    exact congrArg Except.ok (List.map_injective_iff.2 aheadView_inj (of_decide_eq_true h))

/-- The test accepts the written list's tuples. -/
theorem foldsFirst_test :
    foldsAre (foldEntries (planOf WP.first.blocksInOrder) (planOf WP.second.blocksInOrder) proofSendsFull.1)
      (foldsFirstW.map aheadView) = true := by
  unfold foldEntries isSwitch
  simp only [Johnson.Unfolds.splitOn_eq]
  decide +kernel

/-- **THE EQUATION: THE ENTRIES BY WHICH FOLDS SPEND THE FIRST CHAIN's FRESH TABLES.** -/
theorem foldEntries_first_written :
    foldEntries (planOf WP.first.blocksInOrder) (planOf WP.second.blocksInOrder) proofSendsFull.1 =
      .ok foldsFirstW :=
  foldsAre_eq foldsFirst_test

/-- **THE EQUATION AT THE SECOND CHAIN: THE EMPTY LIST.** It says little: all four written sendings
of that chain are switches', so the maker's loop is never entered. -/
theorem foldEntries_second_written :
    foldEntries (planOf WP.second.blocksInOrder) [] proofSendsFull.2.2 = .ok [] := by
  refine foldsAre_eq (l := []) ?_
  unfold foldEntries isSwitch
  simp only [Johnson.Unfolds.splitOn_eq]
  decide +kernel

/-- The written list's first entry: it serves negative lines alone. -/
def foldsFirstHeadW : Ahead := foldsFirstW.headD ⟨"", default, default, default, default, false⟩

/-- **THE TEST CAN FAIL**: the last entry dropped; the first entry's start of the extension field
greater by one; the first two swapped; one letter more at the first name. -/
theorem foldsFirst_bite :
    foldsAre (foldEntries (planOf WP.first.blocksInOrder) (planOf WP.second.blocksInOrder) proofSendsFull.1)
        (foldsFirstW.map aheadView).dropLast = false ∧
      foldsAre (foldEntries (planOf WP.first.blocksInOrder) (planOf WP.second.blocksInOrder) proofSendsFull.1)
        (aheadView { foldsFirstHeadW with
          start := ⟨foldsFirstHeadW.start.f, foldsFirstHeadW.start.e + 1⟩ } ::
            (foldsFirstW.map aheadView).drop 1) = false ∧
      foldsAre (foldEntries (planOf WP.first.blocksInOrder) (planOf WP.second.blocksInOrder) proofSendsFull.1)
        (((foldsFirstW.map aheadView).take 2).reverse ++
          (foldsFirstW.map aheadView).drop 2) = false ∧
      foldsAre (foldEntries (planOf WP.first.blocksInOrder) (planOf WP.second.blocksInOrder) proofSendsFull.1)
        (aheadView { foldsFirstHeadW with name := foldsFirstHeadW.name ++ "x" } ::
          (foldsFirstW.map aheadView).drop 1) = false := by
  rw [foldEntries_first_written]
  decide +kernel

end AtFullSide.K14

#print axioms AtFullSide.K14.foldsAre_eq
#print axioms AtFullSide.K14.foldsFirst_test
#print axioms AtFullSide.K14.foldEntries_first_written
#print axioms AtFullSide.K14.foldEntries_second_written
#print axioms AtFullSide.K14.foldsFirst_bite
