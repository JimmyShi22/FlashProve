-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/LotIs.lean: the block that the merge's lot lays is the block of which the
merge's laws speak. Theorems with their proofs, most of them by definition.

Why. The lot (Johnson/Desc/ProofFile/Lot/K11.lean) lays `blkAt Z "H.8.call" G`: the kind's block
`headClaimMergeKind` (Johnson/Desc/First/Fork/MergeKind.lean) at the place's numbers `parOf Z G`, with one
clause more in its test on the plan. The laws under Johnson/Top/H0/MergeLaw/ speak of
`headClaimMergeKind P`. The two are not one term.

Main names:
  `lot_lays`: the lot lays that one block, among the blocks that state their claims; nothing else.
  `blkAt_fields`: its decision, rounds, runs of claims, runs behind the batching, place, name,
    oracles and "before" are the kind's block's. `blkAt_decide`, `blkAt_claims`: the two functions
    that run are the kind's `headMergeDecide` and `headMergeClaim`.
  `blkAt_step`: AS A STEP THE TWO ARE ONE FUNCTION.
  `blkAt_planOk`: its test on the plan is the kind's own AND "the step that is looked for is in the
    table of the steps of verify-on-bytes". `blkAt_found`: so a yes gives that clause.
    `blkAt_refuses`: at a name that the table has not, the test is false.
  `sent_of_planOk`: where the test passes, the number "sent" is the count in front of that step.

Limits. On the lot's block alone: that a written description lays this block at the merge's place,
and under which wrappers, is not said here. Nothing on soundness or on hiding.

-/
import Johnson.Desc.ProofFile.Lot.K11

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace K11
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First
open Johnson.Desc.First.ForkMerge

/-- The lot lays one block, in the list of the blocks that state their claims; none elsewhere. -/
theorem lot_lays (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    (lot Z).hearC G = [blkAt Z "H.8.call" G] ∧ (lot Z).own G = [] ∧ (lot Z).controls = [] ∧
      (lot Z).letters = false := ⟨rfl, rfl, rfl, rfl⟩

/-- **Field by field the lot's block is the kind's block at the place's numbers**, but for its test
on the plan. -/
theorem blkAt_fields (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    (blkAt Z "H.8.call" G).decide = (headClaimMergeKind (parOf Z G)).decide ∧
    (blkAt Z "H.8.call" G).rounds = (headClaimMergeKind (parOf Z G)).rounds ∧
    (blkAt Z "H.8.call" G).claims = (headClaimMergeKind (parOf Z G)).claims ∧
    (blkAt Z "H.8.call" G).after = (headClaimMergeKind (parOf Z G)).after ∧
    (blkAt Z "H.8.call" G).place = (headClaimMergeKind (parOf Z G)).place ∧
    (blkAt Z "H.8.call" G).name = (headClaimMergeKind (parOf Z G)).name ∧
    (blkAt Z "H.8.call" G).oracles = (headClaimMergeKind (parOf Z G)).oracles ∧
    (blkAt Z "H.8.call" G).before = (headClaimMergeKind (parOf Z G)).before :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Its decision is the kind's own function. -/
theorem blkAt_decide (Z : ProofFile.Pub) (G : ProofFile.Ground) (s : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (blkAt Z "H.8.call" G).decide s rs gs = headMergeDecide (parOf Z G) s rs := rfl

/-- Its one run of claims is the kind's own function, under the driver's name. -/
theorem blkAt_claims (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    (blkAt Z "H.8.call" G).claims = [("the merge", headMergeClaim)] := rfl

/-- **AS A STEP THE TWO ARE ONE FUNCTION.** -/
theorem blkAt_step (Z : ProofFile.Pub) (G : ProofFile.Ground) (ft : Nat) (s : S) (rs : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn) :
    (blkAt Z "H.8.call" G).step ft s rs cols = (headClaimMergeKind (parOf Z G)).step ft s rs cols := rfl

/-- Its test on the plan is the kind's own, and "the step that is looked for is in the table". -/
theorem blkAt_planOk (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    (blkAt Z "H.8.call" G).planOk = true ↔
      (headClaimMergeKind (parOf Z G)).planOk = true ∧ (sentAt? Z "H.8.call").isSome = true := by
  show ((headClaimMergeKind (parOf Z G)).planOk && (sentAt? Z "H.8.call").isSome) = true ↔ _
  exact Bool.and_eq_true _ _ ▸ Iff.rfl

/-- **Where its test on the plan passes, the step that is looked for is in the table**: the clause
that the lot adds to the kind's own test. -/
theorem blkAt_found (Z : ProofFile.Pub) (G : ProofFile.Ground) (h : (blkAt Z "H.8.call" G).planOk = true) :
    (sentAt? Z "H.8.call").isSome = true ∧ (Z.cuts.any fun c => c.look == "H.8.call") = true := by
  have h2 := ((blkAt_planOk Z G).1 h).2
  refine ⟨h2, ?_⟩
  unfold sentAt? ProofFile.Pub.roundsBefore? at h2
  by_cases hc : (Z.cuts.any fun c => c.look == "H.8.call") = true
  · exact hc
  · rw [if_neg hc] at h2
    exact absurd h2 (by simp)

/-- At a name that the table has not, the block's test on the plan is false. -/
theorem blkAt_refuses (Z : ProofFile.Pub) (G : ProofFile.Ground) (look : String)
    (h : (Z.cuts.any fun c => c.look == look) = false) : (blkAt Z look G).planOk = false := by
  show ((headClaimMergeKind (parAt Z look G)).planOk && (sentAt? Z look).isSome) = false
  unfold sentAt? ProofFile.Pub.roundsBefore?
  rw [if_neg (by rw [h]; simp)]
  simp

/-- Where that test passes, "sent" is the count in front of the step, by `Z.roundsBefore` too. -/
theorem sent_of_planOk (Z : ProofFile.Pub) (G : ProofFile.Ground) (h : (blkAt Z "H.8.call" G).planOk = true) :
    (parOf Z G).sent =
      (Z.D.1.take (Z.roundsBefore "H.8.call")).foldl (fun n r => n + r.entry.roots) 0 := by
  have h2 := ((blkAt_planOk Z G).1 h).2
  show (sentAt? Z "H.8.call").getD 0 = _
  unfold sentAt? at h2 ⊢
  unfold ProofFile.Pub.roundsBefore? at h2 ⊢
  by_cases hc : (Z.cuts.any fun c => c.look == "H.8.call") = true
  · rw [if_pos hc]
    rfl
  · rw [if_neg hc] at h2
    exact absurd h2 (by simp)

end K11

#print axioms K11.blkAt_step
#print axioms K11.blkAt_planOk
#print axioms K11.blkAt_found
#print axioms K11.blkAt_refuses
#print axioms K11.sent_of_planOk
