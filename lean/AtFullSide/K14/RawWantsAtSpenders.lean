-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawWantsAtSpenders.lean: AT THE WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean), THE LIBRARY's WRITTEN LIST OF THE FIRST CHAIN's SENDINGS AND THE
MERGES THAT mergesByName (Honest/BookWhole.lean) GUESSES: OF THE STRETCHES THAT spendingBook ASKS
wantsFree ABOUT, TWO NAME THE PART NUMBER 1 AT THE PLACE ⟨1, some 24, 9, K11⟩ AS THEIR SPENDER, AND
ONE THE PART NUMBER 1 AT THE PLACE ⟨1, none, 3, K13⟩; THEIR USES, OWNERS, BASES, NUMBERS AND COUNTS
ARE WRITTEN VALUES: each by one evaluation in Lean's kernel. One definition with code; statements
with their proofs. FACTS ON THE LIST OF STRETCHES, NOT ON A BOOK.

  rawWantsAt s    of the stretches a.1 ++ b.1, in spendingBook's own terms (as in
                  AtFullSide/K14/RawWantsWritten.lean; that the index-mask message rawIdxW is
                  spendingBook's: rawIdx_written, AtFullSide/K14/RawFactsWritten.lean): those that
                  name the spender s, in the list's order, each as use, owner, base, number, count
  rawWantsAt_of_ok   what rawWantsAt is where linksWants returns a
  rawWantsAtK11_written   **at that part they are two**: "sum", of link 24's mask row, number 3531,
                  count 38; "ends", of the index-mask message, number 12, count 1
  rawWantsAtK13_written   **at K13's part it is one**: "sum", of the index-mask message, number 13,
                  count 37
  rawWantsAtK11_bent, rawWantsAtK13_bent   the evaluations can fail: with the first number greater
                  by one the comparison rejects

What it is for. spendingBook lays each stretch w into the book as the entry Want.entry w
(Honest/BookEntries.lean): owner w.msg.owner, start w.msg.base with w.number added to its second
number, count ⟨0, w.count⟩, spent by w.spender. So K11's two stretches stand for the entries with
the starts ⟨23217, 3970⟩ and ⟨25848, 8659⟩ and the counts ⟨0, 38⟩ and ⟨0, 1⟩, K13's one for the
start ⟨25848, 8660⟩ and the count ⟨0, 37⟩. THAT STEP, AND THAT THESE ARE THE PARTS' ENTRIES IN A
BOOK, IS NO THEOREM HERE (AtFullSide/K14/RawSpentWritten.lean has it, from a return of bookWhole, by
rawWantsAt_of_ok). THE MESSAGE's NAME AND ITS FREE ENTRIES ARE NOT IN THE TUPLE: which message a
stretch is of is read off owner AND base (the owner alone would not tell: link 0's mask row and the
index-mask message have one owner), and an entry's first field, the run's name, is not had from
these facts.
OPTIONS ARE RAISED in front of the four evaluations: maxRecDepth to 1000000 (no lower number was
tried), and maxHeartbeats is lifted: the first chain has 48,293 rounds. This side library's files
Lean compiles with a larger stack (lakefile.toml). No other option is raised.
What is assumed. Nothing.
What is not claimed. Anything on a book: that spendingBook, bookRaw or bookWhole returns; which
entries a part spends there. THAT ANY DESCRIPTION BUT WP HAS THESE VALUES (WP.lean's own limit: its
values were printed by Lean's evaluator). THE SENDINGS ARE FOUND BY THEIR LABELS, WHICH REST ON ONE
PRINT (Johnson/G/SendsWritten.lean's own limit). THE MERGES ARE A GUESS, in the frame's own word:
that K11's part's end value is laid under the index-mask message, and that K13's part is a lone
sumcheck, is that guess's doing. Numbers and addresses: nothing on soundness, completeness or
hiding.
-/
import AtFullSide.K14.RawFactsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- Of the stretches that spendingBook asks wantsFree about: those that name the spender s, in the
list's order: use, owner, base, number, count. Nothing where linksWants rejects. -/
def rawWantsAt (s : Addr) : Option (List (String × Addr × Due × Nat × Nat)) :=
  match linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW (mergesByName WP.first.blocksInOrder).ends
      (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 with
  | .ok a => some (((a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).filter
        fun w => w.spender == s).map fun w => (w.use, w.msg.owner, w.msg.base, w.number, w.count))
  | .error _ => none

/-- What rawWantsAt is where linksWants returns a. -/
theorem rawWantsAt_of_ok {a : List Want × Nat}
    (ha : linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW
      (mergesByName WP.first.blocksInOrder).ends (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
        .ok a) (s : Addr) :
    rawWantsAt s = some (((a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).filter
        fun w => w.spender == s).map fun w =>
          (w.use, w.msg.owner, w.msg.base, w.number, w.count)) := by
  unfold rawWantsAt
  rw [ha]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The two stretches of the part number 1 at the place ⟨1, some 24, 9, K11⟩.** -/
theorem rawWantsAtK11_written : rawWantsAt ⟨⟨1, some 24, 9, .K11⟩, 1⟩ =
    some [("sum", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 3531, 38),
      ("ends", ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨25848, 8647⟩, 12, 1)] := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The evaluation can fail: with the first number greater by one the comparison rejects. -/
theorem rawWantsAtK11_bent : decide (rawWantsAt ⟨⟨1, some 24, 9, .K11⟩, 1⟩ =
    some [("sum", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 3532, 38),
      ("ends", ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨25848, 8647⟩, 12, 1)]) = false := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The one stretch of the part number 1 at the place ⟨1, none, 3, K13⟩.** -/
theorem rawWantsAtK13_written : rawWantsAt ⟨⟨1, none, 3, .K13⟩, 1⟩ =
    some [("sum", ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨25848, 8647⟩, 13, 37)] := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The evaluation can fail: with the number greater by one the comparison rejects. -/
theorem rawWantsAtK13_bent : decide (rawWantsAt ⟨⟨1, none, 3, .K13⟩, 1⟩ =
    some [("sum", ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨25848, 8647⟩, 14, 37)]) = false := by decide +kernel

end AtFullSide.K14

#print axioms AtFullSide.K14.rawWantsAt_of_ok
#print axioms AtFullSide.K14.rawWantsAtK11_written
#print axioms AtFullSide.K14.rawWantsAtK11_bent
#print axioms AtFullSide.K14.rawWantsAtK13_written
#print axioms AtFullSide.K14.rawWantsAtK13_bent
