-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawTest9Written.lean: AT THE LIBRARY's WRITTEN DESCRIPTION WP, AT mergesByName's
MERGES: THE NINTH OF THE BOOK's OWN ELEVEN TESTS (ProverCoinCounts.clauses,
Johnson/Desc/ProofFile/Honest/Frame.lean) ACCEPTS rawAheadW (AtFullSide/K14/RawAheadWritten.lean;
13,116 entries: rawAheadW_length, AtFullSide/K14/RawLengthsWritten.lean), THE STRETCHES' ENTRIES
MADE BY LEAN's KERNEL OFF THEIR MAKERS' OWN TERMS; SO IT ACCEPTS WHATEVER BOOK bookRaw RETURNS
THERE. Statements with their proofs.

  raw9_wants      rawTest9 (AtFullSide/K14/RawEntriesKit.lean) accepts the stretches' entries: an
                  evaluation by Lean's kernel, of the term as it stands
  raw9_seg        it accepts rawSegW: no evaluation: every entry that segmentCarries returns is
                  carried, not spent (the frame's BookRow.segmentCarries_once,
                  Honest/BookRowKit.lean), and the test asks nothing of such an entry
  raw9_test       **it accepts rawAheadW**: no premise
  clause9_written   **the test accepts the raw book**: to the letter the premise h9 of
                  clauses_all_of_each (Honest/BookWordOf.lean) at this book and WP

No option is raised. The file lies in the side library because it imports files of it. The negative
line is rawTest_bite's (RawEntriesKit.lean).

Limits. clause9_written IS AN IMPLICATION FROM "bookRaw RETURNS W". A fact on written values: WP's
own limit and the written sendings' stand. THE MERGES ARE mergesByName's, WHICH THE FRAME's OWN TEXT
CALLS A GUESS: that they are the format's merges is said nowhere. THE TEST DOES LITTLE WORK AT THE
TWO LONG LISTS: at rawSegW its first conjunct fails throughout; what it meets at the stretches'
entries is said by no statement. That the Bool is the list's own member:
AtFullSide/K14/RawClausesWritten.lean. ONE OF ELEVEN TESTS. Nothing on soundness, on completeness or
on what is hidden; no property.
-/
import AtFullSide.K14.RawEntriesKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- The test accepts the stretches' entries. -/
theorem raw9_wants : rawTest9 (rawWantsW.map (·.entry)) = true := by
  decide +kernel

/-- The test accepts the carrying entries of the chain of segments. -/
theorem raw9_seg : rawTest9 rawSegW = true := by
  unfold rawTest9
  rw [List.all_eq_true]
  intro a ha
  rw [BookRow.segmentCarries_once rawSeg_returns a ha]
  rfl

/-- **THE NINTH TEST ACCEPTS rawAheadW.** -/
theorem raw9_test : rawTest9 rawAheadW = true :=
  rawTest9_whole raw9_wants raw9_seg

/-- **THE NINTH TEST ACCEPTS THE RAW BOOK.** CONDITIONAL: that bookRaw returns W. -/
theorem clause9_written (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok W) :
    (W.ahead.all fun a => !(a.once && (WP.shared.blocksInOrder.map (·.place)).contains a.owner.place &&
      !(WP.shared.blocksInOrder.map (·.place)).contains a.spender.place)) = true := by
  rw [rawAhead_written W h]
  exact raw9_test

end AtFullSide.K14

#print axioms AtFullSide.K14.raw9_wants
#print axioms AtFullSide.K14.raw9_seg
#print axioms AtFullSide.K14.raw9_test
#print axioms AtFullSide.K14.clause9_written
