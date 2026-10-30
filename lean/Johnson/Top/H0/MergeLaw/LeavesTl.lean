-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/LeavesTl.lean: the merge's block leaves the smallness test's record. Two
small theorems with their proofs.

What is said. `decide_leaves_tl`: where the merge's decision says yes, `S.tl?` behind is `S.tl?` in
front. `merge_leaves_tl`: the same in the form `Block.Leaves` (Johnson/Desc/Sound/FoldHeard.lean).
By `isLocal` (Law.lean): of the record the decision writes "nothing is owed" and the head's part; of
the head's part four fields (what the merge leaves, the two ledgers, the slot); all else it hands
on.

Limits. Of the kind's block `headClaimMergeKind P`: not of a block that a description lays around it.
Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.Law
import Johnson.Desc.Sound.FoldHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc (Block)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind headMergeDecide)

/-- Where the merge's decision says yes, the smallness test's record is as it was. -/
theorem decide_leaves_tl (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') : s'.tl? = s.tl? := by
  obtain ⟨a, a', e1, e2, _, e4, _⟩ := isLocal P s rs s' h
  unfold S.tl?
  rw [e1, e2, e4]

/-- **The merge's block leaves the smallness test's record.** -/
theorem merge_leaves_tl (P : HeadMergeP) : (headClaimMergeKind P).Leaves S.tl? :=
  fun _ _ _ _ h => decide_leaves_tl P h

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_leaves_tl
