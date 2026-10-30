-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawLinksNext.lean: AT THE WRITTEN DESCRIPTION WP (Johnson/AtFull/ProofPlan/WP.lean),
THE LIBRARY's WRITTEN LIST OF THE FIRST CHAIN's SENDINGS AND THE MERGES THAT mergesByName
(Honest/BookWhole.lean) GUESSES: WHATEVER linksWants (Honest/BookAll.lean) RETURNS AT spendingBook's
OWN ARGUMENTS, ITS SECOND COMPONENT, THE INDEX-MASK MESSAGE's NEXT FREE ENTRY BEHIND THE SEGMENTS,
IS 13: by one evaluation in Lean's kernel. One definition with code; statements with their proofs.

  rawLinksNextIs n   the test: linksWants returns there, and its second component is n
  rawLinksNext_written, rawLinksNext_bent   at 13 it accepts; at 14 it rejects
  rawLinksNext    **out of the Bool: linksWants … = .ok a → a.2 = 13**

That the index-mask message rawIdxW is spendingBook's: rawIdx_written
(AtFullSide/K14/RawFactsWritten.lean). That linksWants returns there: rawLinksWants_returns
(AtFullSide/K14/RawWantsWritten.lean), and again by rawLinksNext_written.
OPTIONS ARE RAISED in front of the two evaluations: maxRecDepth to 1000000 (no lower number was
tried), and maxHeartbeats is lifted. The file stands in this side library because its import does.
What is assumed. Nothing.
What is not claimed. Anything on a book. THAT ANY DESCRIPTION BUT WP HAS THIS VALUE; the sendings
are found by labels that rest on one print; THE MERGES ARE A GUESS: the number counts the end values
that the guess lays under the index-mask message. A number: nothing on soundness, completeness or
hiding.
-/
import AtFullSide.K14.RawFactsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- The test: linksWants returns at spendingBook's own arguments, and its second component is n. -/
def rawLinksNextIs (n : Nat) : Bool :=
  match linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW (mergesByName WP.first.blocksInOrder).ends
      (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 with
  | .ok a => a.2 == n
  | .error _ => false

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **At 13 the test accepts.** -/
theorem rawLinksNext_written : rawLinksNextIs 13 = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- At 14 it rejects. -/
theorem rawLinksNext_bent : rawLinksNextIs 14 = false := by decide +kernel

/-- **WHATEVER linksWants RETURNS THERE: ITS SECOND COMPONENT IS 13.** -/
theorem rawLinksNext : ∀ a, linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW
    (mergesByName WP.first.blocksInOrder).ends (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
      .ok a → a.2 = 13 := by
  intro a ha
  have h := rawLinksNext_written
  unfold rawLinksNextIs at h
  rw [ha] at h
  exact beq_iff_eq.1 h

end AtFullSide.K14

#print axioms AtFullSide.K14.rawLinksNext_written
#print axioms AtFullSide.K14.rawLinksNext_bent
#print axioms AtFullSide.K14.rawLinksNext
