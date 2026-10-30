-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RunsAtMerge.lean: at the merge of the claims on the committed table (kind
K11): one named condition on nine runs of claims gives what the fifth tie asks of the runs that are
open on both sides of the merge. One theorem: a joining.

What is said. `fwd_of_runsPass`: where the list of segments is the written one, the merge's
accepting step and `RunsPass` (KeepAtMerge.lean: a run's reader answers
behind the merge what it answers in front, and a fact on its late slots, at nine runs) give `Fwd` at
every run under the six names that are open across the merge: `t5_cut_low`'s premise hf
(RidesJoinLow.lean). The six names stand for ten runs (`six_are_ten`, FormsBackAtMerge.lean); the
tenth, the approximate range proof's own, holds outright (`equations_pass`, KeepAtMerge.lean).

Limits. `RunsPass` is shown of no state. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.KeepAtMerge
import Johnson.Top.H0.MergeLaw.FormsBackAtMerge

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes.Slice
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Reads.Pass (Fwd)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR X)

/-- **`Fwd` at every run under the six names, from the one condition on nine runs.** -/
theorem fwd_of_runsPass (hl : D.links = linksFull) (Pm : HeadMergeP) {a b : S} {rs : List Fmt.RoundView}
    (hy : headMergeDecide Pm a rs = .ok b) (H : RunsPass (D.Rd 24) Pm a b) :
    ∀ y ∈ sixNames, ∀ p ∈ D.runs 24 y.1 y.2, Fwd (D.Rd 24) p.1 p.2 a b := by
  intro y hy' p hp
  have hs : D.links[24]? = some .head := by
    rw [hl]
    decide +kernel
  rw [runs_at_sort D 24 y.1 y.2 .head hs] at hp
  have hmem : p ∈ sixNames.flatMap (fun x => First.runsOf .head x.1 x.2) :=
    List.mem_flatMap.2 ⟨y, hy', hp⟩
  rw [six_are_ten] at hmem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact H.fwd_objects2
  · exact H.fwd_guests2
  · exact H.fwd_planes2
  · exact H.fwd_join3
  · exact H.fwd_norm3
  · exact H.fwd_policy3
  · exact H.fwd_logits3
  · exact (equations_pass D.lk X _ 24 5 Pm hy).1
  · exact H.fwd_objects7
  · exact H.fwd_guests7

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.fwd_of_runsPass
