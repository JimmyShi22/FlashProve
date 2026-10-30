-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawReturnsWritten.lean: **AT THE LIBRARY's WRITTEN DESCRIPTION WP, THE WRITTEN LISTS
OF SENDINGS AND THE GUESSED MERGES, THE FRAME's MAKER bookRaw (Honest/BookWhole.lean) RETURNS A
BOOK**: the maker of the book of coins in front of the book's own eleven tests. WITH NO PREMISE.
Four theorems; no definition. A join: calls, and three evaluations over written lists (two by
"decide +kernel", for which maxRecDepth is raised to 1000000; one by a plain "decide" over four
messages). It lies in the side library because it imports three files of it, whose evaluations want
that library's deeper stack.

  rawFresh_rounds, rawFresh_in, rawFresh_bite   among the first chain's 189 written messages
                  (sentFirstW, Honest/BookWritten/SentFirst.lean) the fresh tables under a link's
                  label are sent in just the 26 rounds rawFreshRounds, in that order; without "under
                  a link's label" the list of rounds is another
  bookRaw_returns_written   by bookRaw_returns and spendingBook_returns
                  (Honest/BookRawReturns.lean). ALL TWENTY OF THEIR PREMISES ARE MET HERE:
                  the first chain's rows and messages; W's sending is among them
                  (Honest/BookWritten/RowsFirst.lean, SentFirst.lean) ·
                  the shared and the second chain's rows; Omega's sending is there; no fold outside
                  the shared chain sends its own fresh table (Honest/BookWritten/Small.lean) · the
                  short list returns, and with it the shared chain's fold entries
                  (sharedAhead_written, Honest/K14/SharedAheadWritten.lean) · the index-mask
                  message; each link's mask row; behind each of 26 rounds a fold stands with a
                  sending behind it (AtFullSide/K14/RawFactsWritten.lean) · wantsFree accepts the
                  stretches that are laid (rawWants_written, AtFullSide/K14/RawWantsWritten.lean) ·
                  the first and the second chain's fold entries (AtFullSide/K14/FoldsWritten.lean) ·
                  the three chains' switches' rows; mainRoomFault finds no switch at fault
                  (AtFullSide/K14/SwitchesWritten.lean)

What it rests on. No premise; but ALL THAT IS MET IS MET BY EVALUATIONS IN LEAN's KERNEL AT WRITTEN
VALUES, in the files named: WP and the written lists of sendings are literals of the library: that
they are the stored public files' is not said here (under the library's hypothesis:
Honest/K14/WrittenAtHead.lean, Honest/K14/SharedSendsWritten.lean). Which masked sumchecks are
merges is the frame's guess (mergesByName).
What it is not. THE BOOK IS NOT NAMED: "there is a book": nothing can be evaluated at it. NOTHING ON
THE BOOK's OWN ELEVEN TESTS (ProverCoinCounts.checked): that bookWhole or the frame's maker onlineProverFromPublicFiles returns is
not shown. It holds of the makers' texts as they lie beneath this file: if one turns, it is to be
compiled anew. The full size alone. All limits of the files named hold here. No property is claimed.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookRawReturns
import Johnson.Desc.ProofFile.Honest.BookWritten.SentFirst
import Johnson.Desc.ProofFile.Honest.K14.SharedAheadWritten
import AtFullSide.K14.RawWantsWritten
import AtFullSide.K14.FoldsWritten
import AtFullSide.K14.SwitchesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

set_option maxRecDepth 1000000 in
/-- **Among the first chain's written messages the fresh tables under a link's label are sent in
just the 26 rounds rawFreshRounds, in that order.** An evaluation in Lean's kernel over the written
list; the labels are read by the library's laws on splitting a string. -/
theorem rawFresh_rounds :
    (sentFirstW.filter fun f => f.fresh && (linkOf f.label).isSome).map (·.round) =
      rawFreshRounds := by
  unfold linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **That equation can fail**: without "under a link's label" the list of rounds is another. -/
theorem rawFresh_bite :
    decide ((sentFirstW.filter fun f => f.fresh).map (·.round) = rawFreshRounds) = false := by
  decide +kernel

/-- So each such message's round is one of the 26. -/
theorem rawFresh_in : ∀ f ∈ sentFirstW, f.fresh = true → (linkOf f.label).isSome = true →
    f.round ∈ rawFreshRounds := by
  intro f hf h1 h2
  rw [← rawFresh_rounds]
  exact List.mem_map.2 ⟨f, List.mem_filter.2 ⟨hf, by rw [h1, h2]; rfl⟩, rfl⟩

/-- **bookRaw RETURNS A BOOK AT THE WRITTEN DESCRIPTION**, at the written lists of sendings and the
guessed merges. No premise. The book is not named; the book's own eleven tests are not asked. -/
theorem bookRaw_returns_written :
    ∃ W, bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok W := by
  obtain ⟨f1, -, -, -, -, -, -, -, hf1, -⟩ := shared_steps_return sharedAhead_written
  have hS := spendingBook_returns (M := mergesByName WP.first.blocksInOrder) ⟨_, rowsIn_first_written⟩
    ⟨_, rowsIn_shared_written⟩ ⟨_, rowsIn_second_written⟩ rawIdx_written rawRows_some
    rawWants_written ⟨_, foldEntries_first_written⟩ ⟨f1, hf1⟩ ⟨_, foldEntries_second_written⟩
  refine bookRaw_returns hS sentIn_first_written sharedAhead_written
    ⟨_, switchRows_first_written⟩ ⟨_, switchRows_shared_written⟩ ⟨_, switchRows_second_written⟩
    mainRoomFault_written
    (fun f hf h1 h2 => rawBehind_written _ (rawFresh_in f hf h1 h2)) ?_ sentFirst_w ?_
  · intro m1 h1
    rw [sentIn_shared_written] at h1
    obtain rfl := Except.ok.inj h1
    decide
  · rw [ownFresh_none_written.1, ownFresh_none_written.2]
    exact ⟨rfl, rfl⟩

end AtFullSide.K14

#print axioms AtFullSide.K14.rawFresh_rounds
#print axioms AtFullSide.K14.rawFresh_bite
#print axioms AtFullSide.K14.rawFresh_in
#print axioms AtFullSide.K14.bookRaw_returns_written
