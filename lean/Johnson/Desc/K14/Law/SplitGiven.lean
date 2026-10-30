-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/SplitGiven.lean: where the shared chain's blocks pass their own tests on the
plan, THE SHAPE SPLITS: o_u and o_omega differ in code, there are two groups, and "SPLIT" has its
round. Theorems.

WHY. Several laws on the shared chain bear the premise P.S.sharedSplitNeeded = true ("two codes"):
that the shared point stays behind "LIN point", and what stands on it. It is no debt of a caller who
holds the tests on the plan: the block "SPLIT"'s own test (Johnson/Desc/OnPlan/OkShare.lean:
At.splitB) asks that flag outright. Here that is said once, at the block and at the chain.

  eight               blocks P = some l: l is a list of just eight blocks.
  split_given         blocks P = some [b1, …, b8], b8.planOk = true: P.S.sharedSplitNeeded = true.
  blocks_said         every block of (chainOf c P tests last).blocksInOrder passes its test on the plan: the
                      kind's rounds could be said: blocks P is there.
  split_at_the_chain  **at the chain**: under the same premise: P.S.sharedSplitNeeded = true.
SO A SHAPE WITHOUT A SPLIT PASSES NO TEST ON THE PLAN: this description serves shapes that split,
and no other: whatever a law says for the other case has no member among plans that pass.
What is not claimed. That some plan passes: the rides say. Nothing on soundness.

-/
import Johnson.Desc.K14.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.OnPublicFiles

/-- The kind's blocks are eight. -/
theorem eight (P : P14) (l : List (Block St Unit)) (hb : blocks P = some l) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8, l = [b1, b2, b3, b4, b5, b6, b7, b8] := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq]
    at hb
  obtain ⟨_, _, rfl⟩ := hb
  exact ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- **What "SPLIT"'s test on the plan gives.** -/
theorem split_given (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hp : b8.planOk = true) :
    P.S.sharedSplitNeeded = true := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  have h : OkD.At.splitB P.codes P.S = true := hp
  unfold OkD.At.splitB at h
  rw [Bool.and_eq_true] at h
  exact h.1

/-- Each of the kind's blocks, as the chain lays them, stands in the flat list; so its own test on
the plan has passed where all the flat list's have. -/
private theorem own_pass (c : Model.Verify.Chains) (P : P14) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (h : ∀ b ∈ (chainOf c P tests last).blocksInOrder, b.planOk = true) :
    ∀ x ∈ blocksOr P, x.planOk = true := by
  intro x hx
  let B : Block St Unit → Block St Unit := fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }
  have hflat : (chainOf c P tests last).blocksInOrder = B (frontBlock c) ::
      (blocksOr P ++ tests ++ [last (blocksOr P ++ tests)]).map B := by
    simp [chainOf, VerifiableInference.Desc.Chain.blocksInOrder, B]
  have hm : B x ∈ (chainOf c P tests last).blocksInOrder := by
    rw [hflat]
    exact List.mem_cons_of_mem _
      (List.mem_map.2 ⟨x, List.mem_append_left _ (List.mem_append_left _ hx), rfl⟩)
  have k : (x.planOk && x.hasNoClaimsAndNothingAfter) = true := h (B x) hm
  rw [Bool.and_eq_true] at k
  exact k.1

/-- Where all pass, the kind's rounds could be said. -/
theorem blocks_said (c : Model.Verify.Chains) (P : P14) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (h : ∀ b ∈ (chainOf c P tests last).blocksInOrder, b.planOk = true) :
    ∃ l, blocks P = some l := by
  cases hb : blocks P with
  | some l => exact ⟨l, rfl⟩
  | none =>
    have key := own_pass c P tests last h
    unfold blocksOr at key
    rw [hb] at key
    have k : false = true := key _ (List.mem_singleton.2 rfl)
    cases k

/-- **At the chain: the shape splits.** -/
theorem split_at_the_chain (c : Model.Verify.Chains) (P : P14) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (h : ∀ b ∈ (chainOf c P tests last).blocksInOrder, b.planOk = true) :
    P.S.sharedSplitNeeded = true := by
  obtain ⟨l, hb⟩ := blocks_said c P tests last h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := eight P l hb
  refine split_given P b1 b2 b3 b4 b5 b6 b7 b8 hb (own_pass c P tests last h b8 ?_)
  unfold blocksOr
  rw [hb]
  simp

end Desc.K14.Law
