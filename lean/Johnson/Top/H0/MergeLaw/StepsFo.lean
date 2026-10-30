-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/StepsFo.lean: the merge's decision steps: what was heard stands, and the
ledger only grows, with its sizes. Small theorems with their proofs.

Why. A law that follows a lookup's value along a link asks of every later block of the link: its
decision leaves what the lookup was heard to return, and leaves the link's ledger a later one with
its sizes (`Block.Steps (CarriesFo S.fork? hd)`, Johnson/Desc/Sound/FoldSteps.lean,
Johnson/Desc/First/LedgerAtFo.lean). At the head's link the merge is such a block; it WRITES the
ledger.

Main names:
  `decide_leaves_look`: the merge's yes leaves `S.lookHeard?`. `decide_fork_later`: where a ledger
    is open in front one is open behind, later in the library's order that keeps the sizes (by
    `decide_later`, Keeps.lean).
  `merge_steps`: the kind's block steps, at any reading hd that its yes leaves. `merge_steps_look`:
    at `S.lookHeard?`. `merge_steps_tl`: at every reading of `S.tl?` alone: the lookup on the
    digits' value among them.
  `K11.blkAt_steps_look`, `K11.blkAt_steps_tl`: the same of the lot's own block
    (Johnson/Desc/ProofFile/Lot/K11.lean). No test on the plan is asked.

Limits. Of the decision alone: nothing on the block's run of claims (`run_later`, Keeps.lean, has
the ledger's half). Of the bare blocks: not under the wrappers that a description lays around them.
Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.Keeps
import Johnson.Top.H0.MergeLaw.LeavesTl
import Johnson.Top.H0.MergeLaw.LotIs
import Johnson.Desc.First.LedgerAtFo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block CarriesFo carriesFoOfLater)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind headMergeDecide)

/-- Where the merge's decision says yes, what the lookup on the calls was heard to return is as it
was. -/
theorem decide_leaves_look (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') : s'.lookHeard? = s.lookHeard? := by
  obtain ⟨a, a', e1, e2, _, e4, _⟩ := isLocal P s rs s' h
  unfold S.lookHeard?
  rw [e1, e2, e4]

/-- Where it says yes and a ledger is open in front: one is open behind, later in the library's
order that keeps the sizes. -/
theorem decide_fork_later (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') (F : Fork) (hF : s.fork? = some F) :
    ∃ G, s'.fork? = some G ∧ OnBytes.PscRun.Later F G := by
  obtain ⟨a, a', e1, e2, hl⟩ := decide_later h
  obtain ⟨b, b', f1, f2, _, f4, _⟩ := isLocal P s rs s' h
  obtain rfl : a = b := by
    rw [e1] at f1
    exact Here.head.inj f1
  obtain rfl : a' = b' := by
    rw [e2] at f2
    exact Here.head.inj f2
  have ho : a'.opened = a.opened := by rw [f4]
  unfold S.fork? at hF ⊢
  rw [e1] at hF
  rw [e2]
  by_cases hx : a.opened = true
  · simp only [hx, if_true] at hF
    obtain rfl := Option.some.inj hF
    exact ⟨a'.F, by simp [ho, hx], hl⟩
  · simp [hx] at hF

/-- **THE MERGE's DECISION STEPS**, at any reading hd of what was heard that its yes leaves: what
was heard stands; the ledger only grows, with its sizes. -/
theorem merge_steps (P : HeadMergeP) (hd : S → Option Forest.Heard)
    (hh : ∀ s rs s', headMergeDecide P s rs = .ok s' → hd s' = hd s) :
    (headClaimMergeKind P).Steps (CarriesFo S.fork? hd) :=
  fun s rs _ s' h => carriesFoOfLater S.fork? hd s s'
    (fun g hg => by rw [hh s rs s' h]; exact hg) (decide_fork_later P h)

/-- At what the lookup on the calls was heard to return. -/
theorem merge_steps_look (P : HeadMergeP) : (headClaimMergeKind P).Steps (CarriesFo S.fork? S.lookHeard?)
    :=
  merge_steps P _ fun _ _ _ h => decide_leaves_look P h

/-- At every reading of the smallness test's record alone: the lookup on the digits' among them. -/
theorem merge_steps_tl (P : HeadMergeP) (f : Option HTailF2 → Option Forest.Heard) :
    (headClaimMergeKind P).Steps (CarriesFo S.fork? fun s => f s.tl?) :=
  merge_steps P _ fun _ _ _ h => by rw [decide_leaves_tl P h]

end VerifiableInference.Desc.First.MergeLaw

namespace K11
open VerifiableInference.Desc (CarriesFo)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.MergeLaw

/-- **The same of the lot's own block.** -/
theorem blkAt_steps_look (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    (blkAt Z "H.8.call" G).Steps (CarriesFo S.fork? S.lookHeard?) :=
  merge_steps_look (parOf Z G)

theorem blkAt_steps_tl (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (f : Option OnBytes.Model.HTailF2 → Option OnBytes.Model.Forest.Heard) :
    (blkAt Z "H.8.call" G).Steps (CarriesFo S.fork? fun s => f s.tl?) :=
  merge_steps_tl (parOf Z G) f

end K11

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_steps
#print axioms K11.blkAt_steps_look
#print axioms K11.blkAt_steps_tl
