-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/AlikeAtMerge.lean: the state behind an accepting step of the merge of the
claims on the committed table (kind K11) goes on from the state in front, as far as the output
head's readers see: `Alike` (Johnson/Desc/Kinds/Law/RunsFixed.lean). One theorem with its proof.

`merge_alike`: `Alike s s'` across the step, where the open segment's ledger has its sizes in front.

By `isLocal` (Law.lean: of the output head's part the step writes four fields alone, and of the
state beside it only what is owed), `decide_later` (Keeps.lean: the ledger behind is later) and
`merge_trees` (LedgerBehind.lean: the ledger's list of arrays stays).

Why. The laws on the runs "planes" and "join" and on the output head's own three take `Alike`
between the two states (`letters_alike`, `reader_rides_own`). `merge_keptMore` (KeptAtMerge.lean) is
the like for the premise `KeptMore` of another family of laws.

Limits. One direction alone: from front to behind. No accepting step is exhibited. Nothing on
soundness.

-/
import Johnson.Top.H0.MergeLaw.LedgerBehind
import Johnson.Desc.Kinds.Law.RunsFixed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.Kinds.Head.Law (Alike)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- **The state behind the merge's accepting step goes on from the state in front, as far as the
output head's readers see.** -/
theorem merge_alike (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') (hz : ∀ a, s.here = .head a → Sized a.F) :
    Alike s s' := by
  obtain ⟨a, a', ha, ha', e, ea, -⟩ := isLocal P s rs s' h
  obtain ⟨a₁, a₁', e1, e1', hL⟩ := decide_later h
  obtain rfl : a₁ = a := by
    rw [ha] at e1
    exact (Here.head.inj e1).symm
  obtain rfl : a₁' = a' := by
    rw [ha'] at e1'
    exact (Here.head.inj e1').symm
  refine ⟨a₁, a₁', ha, ha', by rw [ea], by rw [ea], by rw [ea], by rw [ea], by rw [ea],
    by rw [e], by rw [e], hL, by rw [merge_trees P h ha ha' (hz a₁ ha)]⟩

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_alike
