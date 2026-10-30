-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/ReadsCount.lean: how many reads the plan of a segment of the first chain has, at a
public record X: the one number that the two families of the item "tie l" share.

  nReads   segment 24, the output head: its plan's count · an even segment 2 g: group g's layers'
           count · an odd segment 2 g + 1: group g's attention's count

Limits. A definition. That the segment's built data has this sort and group is said at the laws that
read it. Nothing on soundness, completeness or hiding.
-/
import Johnson.HonestTrace.U3Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1

/-- **The number of reads of segment l's plan.** -/
def nReads (X : OnBytes.Model.Verify.Public) (l : ℕ) : ℕ :=
  if l = 24 then X.H.nU.getD 2 0
  else if l % 2 = 0 then ((X.G[l / 2]?).map fun hp => hp.nU.getD 2 0).getD 0
  else ((X.A[l / 2]?).map fun a => a.nW).getD 0

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.nReads
