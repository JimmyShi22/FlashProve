-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/BookWholeWritten.lean: A WORKING FILE. AT THE LIBRARY's WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean) AND ITS WRITTEN SENDINGS (Johnson/G/SendsWritten.lean), AT
mergesByName's MERGES: THE FRAME's bookWhole (Johnson/Desc/ProofFile/Honest/BookWhole.lean) RETURNS
A BOOK: THE RAW BOOK PASSES ALL ELEVEN OF ITS OWN TESTS. No premise. Statements with their proofs;
calls and rewritings alone; no evaluation in this file.

  clause2_of_return, clause10_of_return   the second and the tenth test's Bools as they stand, out
                  of clause2_written and clause10_written (AtFullSide/K14/RawRowsWritten.lean), by
                  clauses_verdicts (Honest/BookWordOf.lean)
  rawWord_none    **whatever book bookRaw returns there: no test of its own is named as failing**
  bookWhole_returns_raw   **the book that bookWhole returns is the raw book**
  bookWhole_returns_written   **bookWhole returns**
  bookWhole_returns_written_ahead   the same, with the book's entries named: rawAheadW
                  (AtFullSide/K14/RawAheadWritten.lean)

How it is put together. bookRaw_returns_written (AtFullSide/K14/RawReturnsWritten.lean) gives the
raw book W. rawAhead_written (AtFullSide/K14/RawAheadWritten.lean) says that its entries are
rawAheadW: by that one equation each closed fact at rawAheadW is carried to W. The first and the
third test: AtFullSide/K14/RawBookRowsWritten.lean; the fourth, the sixth and the ninth:
RawTest4Written.lean and its two sisters; the fifth, the seventh, the eighth and the eleventh: that
their twins accept rawAheadW (AtFullSide/K14/RawTwinFifth.lean, RawTwinSeventh.lean,
RawTwinEighth.lean; the names' keys: RawKeyDefs.lean, RawKeysTests.lean, RawNamesKeys.lean) with the
twins' laws, through word_none_of_twins (Honest/BookLinear/WordOfTwins.lean). Then
bookWhole_returns_of (Honest/BookWordOf.lean).

Limits. A FACT ON WRITTEN VALUES: WP's own limit stands (its values were printed off the goals'
stored full-size public files); so does the written sendings' (labels on one print; a test by Lean's
evaluator, no theorem). NOTHING AT ANY OTHER DESCRIPTION. THE MERGES ARE mergesByName's, WHICH THE
FRAME's OWN TEXT CALLS A GUESS: that they are the format's merges is said nowhere. Two of the book's
ten pieces of entries are not spelled: they are their makers' terms. THAT bookWhole RETURNS SAYS
THAT THE BOOK's ELEVEN OWN TESTS ACCEPT, AND NO MORE: nothing on the tests on owners that stand
outside the eleven (ownersClearBy, Honest/BookGuard.lean, is part of none of them), nothing on
carriesWhole (Honest/BookCoins.lean), nothing on how many positions are opened against tails and
pads. THE ELEVEN READ THE BOOK's ENTRIES, ROWS AND CUTS AND THE DESCRIPTION, NOT THE PARTS' TEXTS:
that a part lays, spends or carries what the book's numbers say is not said. The book is made of the
description, the sendings and the merges alone: no filling is looked at. Which sending is a switch,
of which test, and which is "the folded row", "Omega" or "W", is read off its label. THAT onlineProverFromPublicFiles
RETURNS, OR THAT ANY PLAY RETURNS, IS NOT SAID. What it is good for that the tests accept is the
frame's laws' to say. No option is raised. Nothing on soundness, on completeness or on what is
hidden; no property.
-/
import AtFullSide.K14.RawReturnsWritten
import AtFullSide.K14.RawClausesWritten
import AtFullSide.K14.RawRowsWritten
import AtFullSide.K14.RawTwinFifth
import AtFullSide.K14.RawTwinSeventh
import AtFullSide.K14.RawTwinEighth
import AtFullSide.K14.RawKeysTests
import AtFullSide.K14.RawNamesKeys
import Johnson.Desc.ProofFile.Honest.BookLinear.WordOfTwins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- The second test's Bool as it stands. CONDITIONAL: that bookRaw returns W. -/
theorem clause2_of_return (M : Merges) (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2 M = .ok W) :
    ((W.first ++ W.shared ++ W.second).all fun r =>
      ((W.first ++ W.shared ++ W.second).filter fun q => q.1 == r.1).length == 1) = true := by
  have c := clause2_written M W h
  rw [← List.getElem?_map, clauses_verdicts] at c
  exact Option.some.inj c

/-- The tenth test's Bool as it stands. CONDITIONAL: that bookRaw returns W. -/
theorem clause10_of_return (M : Merges) (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2 M = .ok W) :
    (W.cuts.all fun c =>
      (WP.first.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
        WP.shared.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
        WP.second.blocksInOrder.map fun b => (b.place, b.rounds.length)).lookup c.1 ==
          some (c.2.foldl (· + ·) 0) && c.2.all (· != 0) &&
        (W.cuts.filter fun d => d.1 == c.1).length == 1) = true := by
  have c := clause10_written M W h
  rw [← List.getElem?_map, clauses_verdicts] at c
  exact Option.some.inj c

/-- **WHATEVER BOOK bookRaw RETURNS AT THE WRITTEN DESCRIPTION: NO TEST OF ITS OWN IS NAMED AS
FAILING.** CONDITIONAL: that it returns W. -/
theorem rawWord_none (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok W) :
    W.word WP = none := by
  have eA : W.ahead = rawAheadW := rawAhead_written W h
  refine word_none_of_twins (g := posW) (d := 20) (owners := ownersW) (uses := usesW)
    (K := rawKeysW) orderW_nodup ?_ ?_ ?_ rawTables_ok rawKeys_in
    rawKeys_nodup ?_ (clause1_written _ W h) (clause2_of_return _ W h) (clause3_written _ W h)
    (clause4_written W h) (clause6_written W h) (clause9_written W h)
    (clause10_of_return _ W h)
  · rw [eA]
    exact raw5_test
  · rw [eA]
    exact raw7_test
  · rw [eA]
    exact raw8_test
  · rw [eA]
    exact rawNames_keys

/-- **THE BOOK THAT bookWhole RETURNS IS THE RAW BOOK.** CONDITIONAL: that bookRaw returns W. -/
theorem bookWhole_returns_raw (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok W) :
    bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok W :=
  bookWhole_returns_of h (rawWord_none W h)

/-- **bookWhole RETURNS AT THE WRITTEN DESCRIPTION.** -/
theorem bookWhole_returns_written :
    ∃ B, bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B := by
  obtain ⟨W, hW⟩ := bookRaw_returns_written
  exact ⟨W, bookWhole_returns_raw W hW⟩

/-- The same, with the book's entries named. -/
theorem bookWhole_returns_written_ahead :
    ∃ B, bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B ∧ B.ahead = rawAheadW := by
  obtain ⟨W, hW⟩ := bookRaw_returns_written
  exact ⟨W, bookWhole_returns_raw W hW, rawAhead_written W hW⟩

end AtFullSide.K14

#print axioms AtFullSide.K14.clause2_of_return
#print axioms AtFullSide.K14.clause10_of_return
#print axioms AtFullSide.K14.rawWord_none
#print axioms AtFullSide.K14.bookWhole_returns_raw
#print axioms AtFullSide.K14.bookWhole_returns_written
#print axioms AtFullSide.K14.bookWhole_returns_written_ahead
