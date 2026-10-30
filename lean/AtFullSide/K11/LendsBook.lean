-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/LendsBook.lean: the two terms of the closed facts in LendsWritten.lean: the written rows
and entries of the maker's book, with its cuts left empty, and the plan's three numbers that the test
k11Lends reads. It is no book of record: a term for the kernel.
-/
import AtFullSide.K14.RawBookRowsWritten
import AtFullSide.K14.RawAheadWritten
import Johnson.Desc.ProofFile.Honest.K11.Plays.LotsPublicStatement
import Johnson.Unfolds.SplitOn
import Johnson.Unfolds.SliceFoldl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open ProofFile.Honest
open ProofFile.Honest.K11 (k11Lends)
open AtFullSide.K14 (rawRowsFirstW rawRowsSharedW rawRowsSecondW rawAheadW rawSegW)
open Johnson.Desc.First.ForkMerge (HeadMergeP)

/-- **The written rows and entries of the maker's book, its cuts left empty.** No book of record. -/
def k11BookW : ProverCoinCounts := ⟨rawRowsFirstW, rawRowsSharedW, rawRowsSecondW, rawAheadW, []⟩

/-- The plan's three numbers that the test reads; all else 0 or empty. -/
def k11ParW (lk : Nat) : HeadMergeP := ⟨24, 9, { lk := lk }, 0, 0, 0, 0, 0⟩

end AtFullSide.K11

#print axioms AtFullSide.K11.k11BookW
#print axioms AtFullSide.K11.k11ParW
