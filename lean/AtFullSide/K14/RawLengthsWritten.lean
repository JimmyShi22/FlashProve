-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawLengthsWritten.lean: OF rawAheadW (AtFullSide/K14/RawAheadWritten.lean): rawWantsW
HAS 7,940 MEMBERS, rawSegW 5,130, rawAheadW 13,116. No premise. Statements with their proofs.

  rawWantsW_length   **7,940**: an evaluation by Lean's kernel
  rawSegW_length  **5,130**: an evaluation
  rawAheadW_length   **13,116**: by the two and the eight written pieces' lengths

How the labels are read. linkOf stands inside segmentCarries: both are unfolded by name and the
reader is rewritten by the library's splitOn_eq (Johnson/Unfolds/SplitOn.lean) and slice_toNat?_eq
(Johnson/Unfolds/SliceFoldl.lean); then Lean's kernel evaluates. rawWantsW is evaluated as it
stands.

No option is raised. The file lies in the side library because it imports files of it.

Limits. A fact on written values: WP's own limit and the written sendings' stand. THE MERGES ARE
mergesByName's, WHICH THE FRAME's OWN TEXT CALLS A GUESS: that they are the format's merges is said
nowhere. A LENGTH FORCES A LIST's SPINE ALONE: nothing is said here of any member. 5,130 AND 13,116
ARE THE NUMBERS OF segmentCarries (Honest/BookCarry.lean) AS IT STANDS; the first two lines of
rawSegW_length's proof name what stands inside that maker. No negative line: an equation with a
numeral. Nothing on any test of the book's own. Nothing on soundness, on completeness or on what is
hidden; no property.
-/
import AtFullSide.K14.RawAheadWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **THE STRETCHES ARE 7,940.** -/
theorem rawWantsW_length : rawWantsW.length = 7940 := by
  decide +kernel

/-- **THE CARRYING ENTRIES OF THE CHAIN OF SEGMENTS ARE 5,130.** -/
theorem rawSegW_length : rawSegW.length = 5130 := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- **THE RAW BOOK's ENTRIES ARE 13,116.** -/
theorem rawAheadW_length : rawAheadW.length = 13116 := by
  unfold rawAheadW
  simp only [List.length_append, List.length_map, rawWantsW_length, rawSegW_length]
  decide +kernel

end AtFullSide.K14

#print axioms AtFullSide.K14.rawWantsW_length
#print axioms AtFullSide.K14.rawSegW_length
#print axioms AtFullSide.K14.rawAheadW_length
