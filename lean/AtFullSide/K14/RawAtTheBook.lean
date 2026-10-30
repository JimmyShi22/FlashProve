-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawAtTheBook.lean: THERE IS A BOOK THAT bookWhole (Honest/BookWhole.lean) RETURNS AT
THE WRITTEN DESCRIPTION WP (Johnson/AtFull/ProofPlan/WP.lean), THE LIBRARY's WRITTEN SENDINGS AND
THE MERGES THAT mergesByName GUESSES, AND AT IT THE PARTS AT K11's, K13's AND K6's PLACES AND THE
ROWS AT K5's TWELVE PLACES AND K6's SPEND WHAT IS WRITTEN. One form; statements with their proofs:
calls alone: nothing is evaluated here.

  RawBookFacts B  **the form: fifteen clauses on a book**: entryRunIs (Honest/Small/EntryRunIs.lean)
                  accepts K11's part's two entries, K13's part's one and K6's parts' ten, each at
                  its position with its written owner, start and count; oneStretch
                  (Honest/BookStretch.lean) at K5's twelve rows is (the link's switch's part 0,
                  2251, 1072); at K6's row (⟨⟨1, some 24, 2, K2⟩, 0⟩, 2434, 173). No "there is" in
                  it
  rawBook_facts   whatever book bookWhole returns at WP has the form: the files named below, called
  rawBook_closed  **there is such a book: no premise**: with bookWhole_returns_written
                  (AtFullSide/K14/BookWholeWritten.lean)

The clauses' homes: AtFullSide/K14/RawEntryRunIs.lean (rawEntryRunIsAtK11_sum,
rawEntryRunIsAtK11_ends, rawEntryRunIsAtK13, rawEntryRunIsAtK6_ten) and
AtFullSide/K14/RawRowStretch.lean (rawRowStretchAtK5, rawRowStretchAtK6). The same at the proof
file's IOP as written in Lean: AtFullSide/K14/RawAtTheBookAtHead.lean.
No option is raised. The file stands in this side library because its imports do.
What is assumed. Nothing. rawBook_closed rests on bookWhole_returns_written: of the makers' texts as
they lie beneath this file, and at mergesByName, a guess.
What is not claimed. A BOOK's NUMBER IS A CLAIM ON A SENDER's TEXT: the book's own tests see
entries, not texts: that a sender lays, or a spender reads, the coins of these numbers is not said
here. That bookWhole returns says that the book's eleven own tests accept, and no more. An entry's
name; entries that carry; oneStretch reads the extension field's half alone. THE MERGES ARE A GUESS;
the sendings are found by labels that rest on one print; WP's values were printed by Lean's
evaluator. The full size alone. Numbers and addresses: nothing on soundness, completeness or hiding.
-/
import AtFullSide.K14.BookWholeWritten
import AtFullSide.K14.RawEntryRunIs
import AtFullSide.K14.RawRowStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open ProofFile.Honest

/-- **The form: what the parts at K11's, K13's and K6's places, and the rows at K5's twelve places
and K6's, spend in the book B.** -/
def RawBookFacts (B : ProverCoinCounts) : Prop :=
  entryRunIs (spentE B ⟨⟨1, some 24, 9, .K11⟩, 1⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩ ⟨23217, 3970⟩
      ⟨0, 38⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 9, .K11⟩, 1⟩) 1 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ ⟨25848, 8659⟩
      ⟨0, 1⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, none, 3, .K13⟩, 1⟩) 0 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ ⟨25848, 8660⟩
      ⟨0, 37⟩ = true ∧
    (entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 1⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2434⟩ ⟨0, 9⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 2⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2443⟩ ⟨0, 49⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 2⟩) 1 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2492⟩ ⟨0, 2⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 4⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2494⟩ ⟨0, 7⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 5⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2501⟩ ⟨0, 24⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 5⟩) 1 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2525⟩ ⟨0, 4⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 6⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2529⟩ ⟨0, 24⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 6⟩) 1 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2553⟩ ⟨0, 2⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 7⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2555⟩ ⟨0, 50⟩ = true ∧
    entryRunIs (spentE B ⟨⟨1, some 24, 4, .K6⟩, 7⟩) 1 ⟨⟨1, some 24, 2, .K2⟩, 0⟩
      ⟨23217, 2605⟩ ⟨0, 2⟩ = true) ∧
    (∀ g, g < 12 → oneStretch (rowEntries B ⟨1, some (2 * g + 1), 3, .K5⟩ 13 0) =
      some (⟨⟨1, some (2 * g + 1), 1, .K2⟩, 0⟩, 2251, 1072)) ∧
    oneStretch (rowEntries B ⟨1, some 24, 4, .K6⟩ 8 0) =
      some (⟨⟨1, some 24, 2, .K2⟩, 0⟩, 2434, 173)

/-- Whatever book bookWhole returns at WP has the form. -/
theorem rawBook_facts {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) : RawBookFacts B :=
  ⟨rawEntryRunIsAtK11_sum hB, rawEntryRunIsAtK11_ends hB, rawEntryRunIsAtK13 hB,
    rawEntryRunIsAtK6_ten hB, fun g hg => rawRowStretchAtK5 hB g hg, rawRowStretchAtK6 hB⟩

/-- **THERE IS A BOOK THAT bookWhole RETURNS AT WP, AND IT HAS THE FORM: NO PREMISE.** -/
theorem rawBook_closed : ∃ B, bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
    (mergesByName WP.first.blocksInOrder) = .ok B ∧ RawBookFacts B := by
  obtain ⟨B, hB⟩ := bookWhole_returns_written
  exact ⟨B, hB, rawBook_facts hB⟩

end AtFullSide.K14

#print axioms AtFullSide.K14.rawBook_facts
#print axioms AtFullSide.K14.rawBook_closed
