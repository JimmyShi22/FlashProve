-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawTest4Written.lean: AT THE LIBRARY's WRITTEN DESCRIPTION WP, AT mergesByName's
MERGES: THE FOURTH OF THE BOOK's OWN ELEVEN TESTS (ProverCoinCounts.clauses,
Johnson/Desc/ProofFile/Honest/Frame.lean) ACCEPTS rawAheadW (AtFullSide/K14/RawAheadWritten.lean;
13,116 entries: rawAheadW_length, AtFullSide/K14/RawLengthsWritten.lean), THE TWO LONG LISTS MADE BY
LEAN's KERNEL OFF THEIR MAKERS' OWN TERMS; SO IT ACCEPTS WHATEVER BOOK bookRaw RETURNS THERE.
Statements with their proofs.

  raw4_wants      rawTest4 (AtFullSide/K14/RawEntriesKit.lean) accepts the stretches' entries: an
                  evaluation by Lean's kernel, of the term as it stands
  raw4_seg        it accepts rawSegW: an evaluation
  raw4_test       **it accepts rawAheadW**: no premise
  clause4_written   **the test accepts the raw book**: to the letter the premise h4 of
                  clauses_all_of_each (Honest/BookWordOf.lean) at this book and WP

How the labels are read, in raw4_seg. linkOf stands inside segmentCarries: both are unfolded by name
and the reader is rewritten by the library's splitOn_eq (Johnson/Unfolds/SplitOn.lean) and
slice_toNat?_eq (Johnson/Unfolds/SliceFoldl.lean); then Lean's kernel evaluates.

No option is raised. The file lies in the side library because it imports files of it. The negative
line is rawTest_bite's (RawEntriesKit.lean).

Limits. clause4_written IS AN IMPLICATION FROM "bookRaw RETURNS W". A fact on written values: WP's
own limit and the written sendings' stand. THE MERGES ARE mergesByName's, WHICH THE FRAME's OWN TEXT
CALLS A GUESS: that they are the format's merges is said nowhere. rawSegW stands over segmentCarries
(Honest/BookCarry.lean): the first two lines of raw4_seg's proof name what stands inside that maker.
dueAt yields ⟨0, 0⟩ where an owner has no row: so the test's acceptance also says that every entry
with a run of some length has an owner with a row. That the Bool is the list's own member:
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
theorem raw4_wants : rawTest4 (rawWantsW.map (·.entry)) = true := by
  decide +kernel

/-- The test accepts the carrying entries of the chain of segments. -/
theorem raw4_seg : rawTest4 rawSegW = true := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- **THE FOURTH TEST ACCEPTS rawAheadW.** -/
theorem raw4_test : rawTest4 rawAheadW = true :=
  rawTest4_whole raw4_wants raw4_seg

/-- **THE FOURTH TEST ACCEPTS THE RAW BOOK.** CONDITIONAL: that bookRaw returns W. -/
theorem clause4_written (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok W) :
    (W.ahead.all fun a =>
      decide (a.start.f + a.count.f ≤ (dueAt (W.first ++ W.shared ++ W.second) a.owner).f) &&
        decide (a.start.e + a.count.e ≤
          (dueAt (W.first ++ W.shared ++ W.second) a.owner).e)) = true := by
  obtain ⟨e1, e2, e3⟩ := rawBookRows_written _ W h
  rw [rawAhead_written W h, e1, e2, e3]
  exact raw4_test

end AtFullSide.K14

#print axioms AtFullSide.K14.raw4_wants
#print axioms AtFullSide.K14.raw4_seg
#print axioms AtFullSide.K14.raw4_test
#print axioms AtFullSide.K14.clause4_written
