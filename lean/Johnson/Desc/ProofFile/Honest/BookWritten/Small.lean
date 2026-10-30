-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookWritten/Small.lean: AT THE LIBRARY's WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean) AND ITS WRITTEN SENDINGS (Johnson/G/SendsWritten.lean): THE
MAKER's LIST OF THE FOLDS THAT SEND A FRESH TABLE OF THEIR OWN IS EMPTY AT THE FIRST AND AT THE
SECOND CHAIN; THE GREATEST NUMBER OF A GROUP AMONG THE FIRST CHAIN's LABELS IS 25; OF THE SHARED
CHAIN's SENDINGS THAT ARE NO SWITCH THE MESSAGES ARE FOUR AND THE ROWS TWO, SPELLED; OF THE SECOND
CHAIN's THERE IS NO ROW. No premise.
Written by the authors of the honest side of the linear claim's shared rounds (K14), in the frame's
folder, not by the frame's authors; the makers are theirs.

  ownFresh_none_written   ownFreshIn at the first and at the second chain: empty
  lastLink_written   lastLink at the first chain's sendings
  sentSharedW, rowsSharedW   the two spelled lists
  sentView, sentView_inj   SentMsg has no decision of equality: a view as a pair of tuples, which
                  is one-to-one
  sentSharedIs, rowsAre   two public tests: a maker's answer against a list; rowsAre_eq: what the
                  second one's yes says
  sentIn_shared_written, rowsIn_shared_written, rowsIn_second_written   **the equations**
  sentShared_bite, rowsAre_bite   THE TESTS CAN FAIL: a member dropped, a number greater by one,
                  two members swapped; at the messages also one letter of a label; at the second
                  chain the shared chain's two rows

How the labels are read. The kernel does not get past String.splitOn and the reading of a number
off a slice by itself: sentIn, rowsIn, lastLink, isSwitch and linkOf are unfolded by name, and the
two readers of labels are rewritten by the library's
splitOn_eq (Johnson/Unfolds/SplitOn.lean) and slice_toNat?_eq (Johnson/Unfolds/SliceFoldl.lean);
then Lean's kernel evaluates.


HOW THE SPELLED LISTS CAME: they were printed by Lean's evaluator and laid into this file by a
program; THE EVALUATOR IS TRUSTED FOR NOTHING: each list is held against its maker by Lean's kernel.

Limits. A fact on written values: WP's own limit stands (its values were printed off the goals'
stored full-size public files); so does the written sendings' (Johnson/G/SendsWritten.lean: the
labels and the two entries of each sending rest on one print and on a test by Lean's evaluator; no
theorem): lastLink reads labels alone, sentIn and rowsIn sort by them, sentSharedW spells two.
NOTHING AT ANY OTHER DESCRIPTION. THAT bookRaw OR bookWhole RETURNS IS NOT SAID; nothing on any test
of the book's own. rowsIn AND sentIn LEAVE THE SWITCHES OUT: the shared chain's nine written
sendings hold more messages than these four, and the book's rows at the shared and the second chain
have the switches' rows and a fold's own besides: not here. AN EMPTY LIST OF ownFreshIn SAYS LESS
THAN "no fold sends such a table": the maker drops in silence a fold at the round 0 and one behind
which it finds nothing; bookRaw reads that the list is empty, and no more. WITHOUT A NEGATIVE LINE:
ownFresh_none_written; lastLink_written. No option is raised. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookWhole
import Johnson.AtFull.ProofPlan.WP
import Johnson.G.SendsWritten
import Johnson.Unfolds.SplitOn
import Johnson.Unfolds.SliceFoldl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **The maker's list of the folds that send a fresh table of their own is empty at the first and
at the second chain.** -/
theorem ownFresh_none_written : ownFreshIn WP.first.blocksInOrder = [] ∧ ownFreshIn WP.second.blocksInOrder = [] := by
  decide +kernel

/-- **The greatest number of a group among the first chain's labels.** The labels' numbers run from
0 to 25; the places of WP's first chain have the links 0 to 24 alone (Seeds.lean, Cuts.lean): the
sending "link 25, moment 0" has its round, number 48235, in a sub-protocol in no link, the one at
⟨1, none, 1, .K2⟩ (addrsFirstW's member number 75, from 0). -/
theorem lastLink_written : lastLink proofSendsFull.1 = some 25 := by
  unfold lastLink linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- **The four messages of the shared chain's sendings that are no switch, written**: label; round;
sender; number in the sending; where its coins begin; how many; a fold's fresh table; mask rows
alone with a sample. -/
def sentSharedW : List SentMsg :=
  [⟨"the folded row", 1, ⟨⟨2, none, 2, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 10808⟩, false, false⟩,
   ⟨"the folded row", 1, ⟨⟨2, none, 2, .K1⟩, 0⟩, 1, ⟨0, 10808⟩, ⟨0, 167⟩, true, false⟩,
   ⟨"Omega", 4, ⟨⟨2, none, 5, .K1⟩, 0⟩, 0, ⟨0, 0⟩, ⟨0, 42853⟩, false, false⟩,
   ⟨"Omega", 4, ⟨⟨2, none, 5, .K1⟩, 0⟩, 1, ⟨0, 42853⟩, ⟨0, 216⟩, false, true⟩]

/-- **The two rows of the shared chain's sendings that are no switch, written.** -/
def rowsSharedW : List (Addr × Due) :=
  [(⟨⟨2, none, 2, .K1⟩, 0⟩, ⟨0, 10975⟩), (⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 43069⟩)]

/-- A message as a pair of tuples of four. (At one tuple of eight Lean's search for a decision of
equality gives up.) -/
def sentView (m : SentMsg) : (String × Nat × Addr × Nat) × (Due × Due × Bool × Bool) :=
  ((m.label, m.round, m.sender, m.j), (m.start, m.count, m.fresh, m.masks))

/-- Two messages with one pair of tuples are one. -/
theorem sentView_inj : Function.Injective sentView := by
  rintro ⟨a, b, c, d, e, f, g, h⟩ ⟨a', b', c', d', e', f', g', h'⟩ q
  simp only [sentView, Prod.mk.injEq] at q
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := q
  rfl

/-- A public test: the shared chain's messages against a list of tuples. -/
def sentSharedIs (t : List ((String × Nat × Addr × Nat) × (Due × Due × Bool × Bool))) : Bool :=
  match sentIn WP.shared.blocksInOrder proofSendsFull.2.1 [] with
  | .ok l => decide (l.map sentView = t)
  | .error _ => false

/-- A public test: a chain's rows against a list. -/
def rowsAre (x : Except String (List (Addr × Due))) (t : List (Addr × Due)) : Bool :=
  match x with
  | .ok l => decide (l = t)
  | .error _ => false

/-- What its yes says. -/
theorem rowsAre_eq {x : Except String (List (Addr × Due))} {t : List (Addr × Due)}
    (h : rowsAre x t = true) : x = .ok t := by
  cases x with
  | error e => cases h
  | ok l => exact congrArg Except.ok (of_decide_eq_true h)

/-- The first test accepts the written list's tuples. -/
theorem sentShared_test : sentSharedIs (sentSharedW.map sentView) = true := by
  unfold sentSharedIs sentIn isSwitch
  simp only [Johnson.Unfolds.splitOn_eq]
  decide +kernel

/-- **THE EQUATION: THE MESSAGES OF THE SHARED CHAIN's SENDINGS THAT ARE NO SWITCH.** -/
theorem sentIn_shared_written : sentIn WP.shared.blocksInOrder proofSendsFull.2.1 [] = .ok sentSharedW := by
  have h := sentShared_test
  unfold sentSharedIs at h
  cases hs : sentIn WP.shared.blocksInOrder proofSendsFull.2.1 [] with
  | error w =>
    rw [hs] at h
    cases h
  | ok l =>
    rw [hs] at h
    exact congrArg Except.ok (List.map_injective_iff.2 sentView_inj (of_decide_eq_true h))

/-- The second test accepts the two written lists. -/
theorem rows_test :
    rowsAre (rowsIn WP.shared.blocksInOrder proofSendsFull.2.1 []) rowsSharedW = true ∧
      rowsAre (rowsIn WP.second.blocksInOrder proofSendsFull.2.2 []) [] = true := by
  unfold rowsIn isSwitch
  simp only [Johnson.Unfolds.splitOn_eq]
  decide +kernel

/-- **THE EQUATION: THE ROWS OF THE SHARED CHAIN's SENDINGS THAT ARE NO SWITCH.** -/
theorem rowsIn_shared_written : rowsIn WP.shared.blocksInOrder proofSendsFull.2.1 [] = .ok rowsSharedW :=
  rowsAre_eq rows_test.1

/-- **THE EQUATION: OF THE SECOND CHAIN's SENDINGS THAT ARE NO SWITCH THERE IS NO ROW.** -/
theorem rowsIn_second_written : rowsIn WP.second.blocksInOrder proofSendsFull.2.2 [] = .ok [] :=
  rowsAre_eq rows_test.2

/-- **THE FIRST TEST CAN FAIL**: the last message dropped; the first message's count greater by one;
the first two swapped; one letter of the first label. -/
theorem sentShared_bite :
    sentSharedIs (sentSharedW.map sentView).dropLast = false ∧
      sentSharedIs ((("the folded row", 1, ⟨⟨2, none, 2, .K1⟩, 0⟩, 0), (⟨0, 0⟩, ⟨0, 10809⟩, false,
        false)) :: (sentSharedW.map sentView).drop 1) = false ∧
      sentSharedIs (((sentSharedW.map sentView).take 2).reverse ++
        (sentSharedW.map sentView).drop 2) = false ∧
      sentSharedIs ((("the folded roW", 1, ⟨⟨2, none, 2, .K1⟩, 0⟩, 0), (⟨0, 0⟩, ⟨0, 10808⟩, false,
        false)) :: (sentSharedW.map sentView).drop 1) = false := by
  unfold sentSharedIs sentIn isSwitch
  simp only [Johnson.Unfolds.splitOn_eq]
  decide +kernel

/-- **THE SECOND TEST CAN FAIL**: the last row dropped; the first row's count greater by one; the
two swapped; the shared chain's two rows at the second chain. -/
theorem rowsAre_bite :
    rowsAre (rowsIn WP.shared.blocksInOrder proofSendsFull.2.1 []) rowsSharedW.dropLast = false ∧
      rowsAre (rowsIn WP.shared.blocksInOrder proofSendsFull.2.1 [])
        ((⟨⟨2, none, 2, .K1⟩, 0⟩, ⟨0, 10976⟩) :: rowsSharedW.drop 1) = false ∧
      rowsAre (rowsIn WP.shared.blocksInOrder proofSendsFull.2.1 []) rowsSharedW.reverse = false ∧
      rowsAre (rowsIn WP.second.blocksInOrder proofSendsFull.2.2 []) rowsSharedW = false := by
  unfold rowsIn isSwitch
  simp only [Johnson.Unfolds.splitOn_eq]
  decide +kernel

end ProofFile.Honest

#print axioms ProofFile.Honest.ownFresh_none_written
#print axioms ProofFile.Honest.lastLink_written
#print axioms ProofFile.Honest.sentView_inj
#print axioms ProofFile.Honest.rowsAre_eq
#print axioms ProofFile.Honest.sentShared_test
#print axioms ProofFile.Honest.sentIn_shared_written
#print axioms ProofFile.Honest.rows_test
#print axioms ProofFile.Honest.rowsIn_shared_written
#print axioms ProofFile.Honest.rowsIn_second_written
#print axioms ProofFile.Honest.sentShared_bite
#print axioms ProofFile.Honest.rowsAre_bite
