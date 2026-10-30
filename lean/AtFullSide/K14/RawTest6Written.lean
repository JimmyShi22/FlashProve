-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawTest6Written.lean: AT THE LIBRARY's WRITTEN DESCRIPTION WP, AT mergesByName's
MERGES: THE SIXTH OF THE BOOK's OWN ELEVEN TESTS (ProverCoinCounts.clauses,
Johnson/Desc/ProofFile/Honest/Frame.lean) ACCEPTS rawAheadW (AtFullSide/K14/RawAheadWritten.lean;
13,116 entries: rawAheadW_length, AtFullSide/K14/RawLengthsWritten.lean), THE TWO LONG LISTS MADE BY
LEAN's KERNEL OFF THEIR MAKERS' OWN TERMS; SO IT ACCEPTS WHATEVER BOOK bookRaw RETURNS THERE.
Statements with their proofs.

  raw6_wants      rawTest6 (AtFullSide/K14/RawEntriesKit.lean) accepts the stretches' entries: an
                  evaluation by Lean's kernel, of the term as it stands
  raw6_seg        it accepts rawSegW: an evaluation
  raw6_test       **it accepts rawAheadW**: no premise
  clause6_written   **the test accepts the raw book**: to the letter the premise h6 of
                  clauses_all_of_each (Honest/BookWordOf.lean) at this book and WP

How the labels are read, in raw6_seg. linkOf stands inside segmentCarries: both are unfolded by name
and the reader is rewritten by the library's splitOn_eq (Johnson/Unfolds/SplitOn.lean) and
slice_toNat?_eq (Johnson/Unfolds/SliceFoldl.lean); then Lean's kernel evaluates.

No option is raised. The file lies in the side library because it imports files of it. The negative
line is rawTest_bite's (RawEntriesKit.lean).

Limits. clause6_written IS AN IMPLICATION FROM "bookRaw RETURNS W". A fact on written values: WP's
own limit and the written sendings' stand. THE MERGES ARE mergesByName's, WHICH THE FRAME's OWN TEXT
CALLS A GUESS: that they are the format's merges is said nowhere. rawSegW stands over segmentCarries
(Honest/BookCarry.lean): the first two lines of raw6_seg's proof name what stands inside that maker.
That the Bool is the list's own member: AtFullSide/K14/RawClausesWritten.lean. ONE OF ELEVEN TESTS.
Nothing on soundness, on completeness or on what is hidden; no property.
-/
import AtFullSide.K14.RawEntriesKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- The test accepts the stretches' entries. -/
theorem raw6_wants : rawTest6 (rawWantsW.map (·.entry)) = true := by
  decide +kernel

/-- The test accepts the carrying entries of the chain of segments. -/
theorem raw6_seg : rawTest6 rawSegW = true := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- **THE SIXTH TEST ACCEPTS rawAheadW.** -/
theorem raw6_test : rawTest6 rawAheadW = true :=
  rawTest6_whole raw6_wants raw6_seg

/-- **THE SIXTH TEST ACCEPTS THE RAW BOOK.** CONDITIONAL: that bookRaw returns W. -/
theorem clause6_written (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok W) :
    (W.ahead.all fun a => !((WP.first.blocksInOrder.map (·.place)).contains a.owner.place &&
      (WP.shared.blocksInOrder.map (·.place)).contains a.spender.place)) = true := by
  rw [rawAhead_written W h]
  exact raw6_test

end AtFullSide.K14

#print axioms AtFullSide.K14.raw6_wants
#print axioms AtFullSide.K14.raw6_seg
#print axioms AtFullSide.K14.raw6_test
#print axioms AtFullSide.K14.clause6_written
