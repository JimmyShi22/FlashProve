-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawWantsWritten.lean: AT THE WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean), THE LIBRARY's WRITTEN LIST OF THE FIRST CHAIN's SENDINGS AND THE
MERGES THAT mergesByName (Honest/BookWhole.lean) GUESSES OFF THE KINDS AND THE COUNTS: WHATEVER
linksWants (Honest/BookAll.lean) RETURNS THERE, THE FRAME's TEST OVER ALL PAIRS, wantsFree
(Honest/BookEntries.lean), ACCEPTS THE STRETCHES THAT spendingBook ASKS IT ABOUT: the links' and the
lone sumchecks', in spendingBook's own terms. One definition with code; statements with their
proofs.

  rawWantsL       the test that is evaluated: linksWants at spendingBook's own arguments returns
                  (the index-mask message is spendingBook's own by rawIdx_written,
                  AtFullSide/K14/RawFactsWritten.lean), and the test of one pass wantsFreeL
                  (Honest/BookFreeL.lean) accepts a.1 ++ b.1 as spendingBook has them
  rawWantsL_written   **it accepts**: ONE EVALUATION IN LEAN's KERNEL, which makes the stretches as
                  far as wantsFreeL reads them
  rawWants_written   **so wantsFree accepts**, by wantsFreeL_sound: in the form in which
                  spendingBook's return wants it: for every a that linksWants yields
  rawLinksWants_returns   and linksWants does return there: so rawWants_written is not empty
  rawWantsL_bent  the evaluation can fail: with the index-mask message's free entries set to 49 the
                  same test rejects

wantsFree itself is not evaluated: it walks all pairs of the stretches.
OPTIONS ARE RAISED in front of the two evaluations: maxRecDepth to 1000000, and maxHeartbeats is
lifted: the first chain has 48,293 rounds. This side library's files Lean compiles with a larger
stack (lakefile.toml). No other option is raised.
What is assumed. Nothing.
What is not claimed. THAT ANY DESCRIPTION BUT WP HAS SUCH STRETCHES (WP.lean's own limit: its values
were printed by Lean's evaluator). THE SENDINGS ARE FOUND BY THEIR LABELS, WHICH REST ON ONE PRINT
(Johnson/G/SendsWritten.lean's own limit). THE MERGES ARE A GUESS, in the frame's own word: that
they are the format's merges is said nowhere. How many the stretches are. That spendingBook or
bookRaw returns: this is one of their steps. Nothing on the book's own tests. Numbers and addresses:
nothing on soundness, completeness or hiding.
-/
import AtFullSide.K14.RawFactsWritten
import Johnson.Desc.ProofFile.Honest.BookFreeL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **The test that is evaluated**, at an index-mask message idx: linksWants at spendingBook's own
arguments returns, and wantsFreeL accepts the links' stretches with the lone sumchecks' behind. -/
def rawWantsL (idx : MsgAt) : Bool :=
  match linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater idx (mergesByName WP.first.blocksInOrder).ends
      (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 with
  | .ok a => wantsFreeL (a.1 ++ (loneWants idx (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1)
  | .error _ => false

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The test of one pass accepts the stretches, made by Lean's kernel.** -/
theorem rawWantsL_written : rawWantsL rawIdxW = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The evaluation can fail: with 49 free entries in the index-mask message the test rejects. -/
theorem rawWantsL_bent : rawWantsL { rawIdxW with free := 49 } = false := by decide +kernel

/-- linksWants returns at spendingBook's own arguments. -/
theorem rawLinksWants_returns : ∃ a, linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW
    (mergesByName WP.first.blocksInOrder).ends (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
      .ok a := by
  have h := rawWantsL_written
  unfold rawWantsL at h
  split at h
  · rename_i a ha
    exact ⟨a, ha⟩
  · cases h

/-- **WHATEVER linksWants RETURNS THERE: wantsFree ACCEPTS a.1 ++ b.1 AS spendingBook HAS THEM.** -/
theorem rawWants_written : ∀ a, linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW
    (mergesByName WP.first.blocksInOrder).ends (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
      .ok a →
    wantsFree (a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1) = true := by
  intro a ha
  have h := rawWantsL_written
  unfold rawWantsL at h
  rw [ha] at h
  exact wantsFreeL_sound h

end AtFullSide.K14

#print axioms AtFullSide.K14.rawWantsL_written
#print axioms AtFullSide.K14.rawWantsL_bent
#print axioms AtFullSide.K14.rawLinksWants_returns
#print axioms AtFullSide.K14.rawWants_written
