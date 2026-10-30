-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/FenceAtMergeLater.lean: THE FENCE IN FRONT OF THE MERGE OF THE CLAIMS ON THE
COMMITTED TABLE (kind K11) AT THE OUTPUT HEAD's SECOND AND THIRD SENDING: the premise hF of
`t5_cut` (RidesJoin.lean), of the same make as `fence_at_merge` (FenceAtMerge.lean).

  openAtMerge_later   A CLOSED FACT, by Lean's kernel: Item.pin 24 1 and Item.pin 24 2 are open at
                      border 346 of the written list at the full size
  fence_at_merge_later   every member that sits at a tenant of the output head's sending 1 or 2 is
                      fenced at base: from "every sampled tenant whose pin is open at border 346
                      sits in a tree below base": `t5_cut`'s hF, to the letter

Limits. The premise is not paid here. A `low_full` not in this library (not `P5T.low_full`)
concludes it at k := 346 at the numbers `N.withTold ps told`, whose fields sent and index are N's
own (`withTold` turns the fields treesAt, msgsAt and indexNo alone). N, base and ms are letters. No
soundness statement.

-/
import Johnson.Top.H0.MergeLaw.FenceAtMerge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc.Sound (Mem SitsAt Fenced linksFull)
open VerifiableInference.Desc.First (Item Numbers openSets start flatPlacesOf sampledIn)

/-- **A closed fact**: the two later pins are open there. -/
theorem openAtMerge_later :
    (openAtMerge.contains (Item.pin 24 1) && openAtMerge.contains (Item.pin 24 2)) = true := by
  decide +kernel

/-- **THE FENCE AT THE TWO LATER SENDINGS.** -/
theorem fence_at_merge_later (N : Numbers) (base : Nat)
    (low : ∀ x ∈ sampledIn N
      ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[346]?.getD []),
      x.1 < base) (ms : List Mem) :
    ∀ t, t = 1 ∨ t = 2 → ∀ p ∈ N.sent 24 t, ∀ x ∈ ms, SitsAt x p.1 p.2 → Fenced base [x] := by
  have h := openAtMerge_later
  rw [Bool.and_eq_true] at h
  have h1 : Item.pin 24 1 ∈ openAtMerge := List.contains_iff_mem.1 h.1
  have h2 : Item.pin 24 2 ∈ openAtMerge := List.contains_iff_mem.1 h.2
  rintro t (rfl | rfl)
  · exact fenced_of_low (fun p hp => low p (mem_sampled_sent N h1 hp)) ms
  · exact fenced_of_low (fun p hp => low p (mem_sampled_sent N h2 hp)) ms

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.openAtMerge_later
#print axioms VerifiableInference.Desc.First.MergeLaw.fence_at_merge_later
