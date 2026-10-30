-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawWantsApart.lean: AT THE WRITTEN DESCRIPTION WP (Johnson/AtFull/ProofPlan/WP.lean),
THE LIBRARY's WRITTEN LIST OF THE FIRST CHAIN's SENDINGS AND THE MERGES THAT mergesByName
(Honest/BookWhole.lean) GUESSES: WHATEVER linksWants RETURNS THERE: OF THE STRETCHES THAT
spendingBook ASKS wantsFree ABOUT, TWO THAT STAND AT DIFFERENT NUMBERS OF THE LIST AND ARE OF ONE
MESSAGE DO NOT MEET; and each lies within its message's free entries. Two statements with their
proofs; no definition; nothing is evaluated here.

  rawWants_apart  **two stretches of one message, at two numbers of the list, have no entry in
                  common** (meets … = false): the frame's wantsFree_apart (Honest/BookFree.lean) at
                  rawWants_written (AtFullSide/K14/RawWantsWritten.lean), whose evaluation it rests
                  on
  rawWants_within   each stretch's number and count add up to no more than its message's free
                  entries: the frame's wantsFree_free there

What is assumed. Nothing.
What is not claimed. «OF ONE MESSAGE» IS NOT «OF ONE OWNER»: the test compares messages (name,
owner, base, free entries). At WP one part, ⟨⟨1, some 0, 1, K1⟩, 0⟩, sends two of them: the
index-mask message and link 0's mask row (rawIdxW, rawRowsW, AtFullSide/K14/RawFactsWritten.lean):
that a stretch of the one and a stretch of the other share no coin is not said here
(AtFullSide/K14/RawWantsOnce.lean has it; and that two stretches with one owner and one base are of
one message: this file's caller brings that equation). THE LIST IS NOT ALL THAT SPENDS: the entries
on fold masks and the shared split's one coin are no stretches of this form, and the test is not
asked of them (Honest/BookFree.lean's own limit). A fact on the list of stretches, not on a book's
entries. That spendingBook, bookRaw or bookWhole returns. THAT ANY DESCRIPTION BUT WP HAS SUCH
STRETCHES; the sendings are found by labels that rest on one print; the merges are a guess (the
limits of AtFullSide/K14/RawWantsWritten.lean, all). Numbers: nothing on soundness, completeness or
hiding.
-/
import AtFullSide.K14.RawWantsWritten
import Johnson.Desc.ProofFile.Honest.BookFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **TWO STRETCHES OF ONE MESSAGE, AT TWO NUMBERS OF THE LIST, DO NOT MEET.** -/
theorem rawWants_apart : ∀ a, linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW
    (mergesByName WP.first.blocksInOrder).ends (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
      .ok a →
    ∀ x ∈ (a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).zipIdx,
    ∀ y ∈ (a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).zipIdx,
    x.2 ≠ y.2 → x.1.msg = y.1.msg →
      meets x.1.number x.1.count y.1.number y.1.count = false :=
  fun a ha _ hx _ hy hn hm => wantsFree_apart (rawWants_written a ha) hx hy hn hm

/-- Each stretch lies within its message's free entries. -/
theorem rawWants_within : ∀ a, linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW
    (mergesByName WP.first.blocksInOrder).ends (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
      .ok a →
    ∀ w ∈ a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1,
    w.number + w.count ≤ w.msg.free :=
  fun a ha _ hw => wantsFree_free (rawWants_written a ha) hw

end AtFullSide.K14

#print axioms AtFullSide.K14.rawWants_apart
#print axioms AtFullSide.K14.rawWants_within
