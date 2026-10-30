-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/MarksHeadSub.lean: every mark of an owner's own list is a mark of
`marksHead` (Honest/Law/MarksHead.lean). An owner that spends the silence of its own marks asks that
these marks stand in the list `hm` of `FirstAsks` (Honest/Law/CoverAsks.lean). K8's authors' lemma
`firstAsks_symbols_letter` has that premise in the form `∀ mk ∈ part1Marks Z G₀, mk ∈ hm`. Here it
is proved at `hm := marksHead`, for each of the five lists.

  1  `part1_sub`, `k3_sub`, `k4_sub`, `k5_sub`, `k6_sub`   the five

Limits.
  * Membership alone. Nothing is said on what a mark's silence gives.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.MarksHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground)

/-- K8's and K11's authors' marks stand in `marksHead`. -/
theorem part1_sub : ∀ mk ∈ P1K8.part1Marks Zp G₀, mk ∈ marksHead Zp G₀ := fun mk h => by
  unfold marksHead
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl h)))

/-- The lookups' authors' marks stand in `marksHead`. -/
theorem k3_sub : ∀ mk ∈ K3.Good.k3Marks Zp G₀, mk ∈ marksHead Zp G₀ := fun mk h => by
  unfold marksHead
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr h)))

/-- K4's authors' marks stand in `marksHead`. -/
theorem k4_sub : ∀ mk ∈ K4.k4MarksWide Zp G₀, mk ∈ marksHead Zp G₀ := fun mk h => by
  unfold marksHead
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr h))

/-- K5's authors' marks stand in `marksHead`. -/
theorem k5_sub : ∀ mk ∈ K5.k5Marks Zp G₀, mk ∈ marksHead Zp G₀ := fun mk h => by
  unfold marksHead
  simp only [List.mem_append]
  exact Or.inl (Or.inr h)

/-- K6's authors' marks stand in `marksHead`. -/
theorem k6_sub : ∀ mk ∈ K6.part4Marks Zp G₀, mk ∈ marksHead Zp G₀ := fun mk h => by
  unfold marksHead
  simp only [List.mem_append]
  exact Or.inr h

end ProofFile.Honest

#print axioms ProofFile.Honest.part1_sub
#print axioms ProofFile.Honest.k3_sub
#print axioms ProofFile.Honest.k4_sub
#print axioms ProofFile.Honest.k5_sub
#print axioms ProofFile.Honest.k6_sub
