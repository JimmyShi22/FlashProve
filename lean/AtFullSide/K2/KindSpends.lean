-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/KindSpends.lean: no spending entry of the written book names a part of the kind "the
code switch" (K2): the kind spends no coin of another part.

  noKindSpends       by Lean's kernel
  noKindSpends_bent  a control: the book's spending entries do name parts of the kind K3

Limits. Of the written book's entries. The lines in front of the kernel follow
AtFullSide/K1/RowTakers/AllSeg.lean.
-/
import AtFullSide.K14.RawAheadWritten
import AtFullSide.K14.RawLengthsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open ProofFile.Honest ProofFile.Honest.K14
open AtFullSide.K14

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- No spending entry names a part of the kind. -/
theorem noKindSpends : (rawAheadW.all fun e => !e.once || e.spender.place.kind != .K2) = true := by
  unfold rawAheadW rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: the like test at the kind K3 says no. -/
theorem noKindSpends_bent :
    (rawAheadW.all fun e => !e.once || e.spender.place.kind != .K3) = false := by
  unfold rawAheadW rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

end AtFullSide.K2

#print axioms AtFullSide.K2.noKindSpends
#print axioms AtFullSide.K2.noKindSpends_bent
