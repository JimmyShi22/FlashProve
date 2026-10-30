-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverSum.lean: a choice of the numbers `p₁` that proves the fields
`hp₁` and `hp₂` of `FirstAsks` (Honest/Law/CoverAsks.lean). The bound of `falls_asks` adds one
number `p₁ n` for each gated sub-protocol (`coverGates`, Honest/Law/CoverChain.lean). The two fields
ask that `p₁ n` is at least the sum of the numbers stated for the marks and the counted falls at
that sub-protocol. Here `p₁ n` is laid as that sum. It is a choice and claims nothing: with it the
bound reads as the sum, over the gated sub-protocols, of the numbers of their owners' marks and of
their counted falls. It is general in the chain.

  1  `priceAt`   the definition
  2  `priceAt_at`   its value at the sub-protocol after `A`
  3  `hp₁_sum`, `hp₂_sum`   the two fields

Limits.
  * The numbers `qM` and `qF` are arguments. Nothing holds them against a test here.
  * No number follows from the lemmas.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open scoped ENNReal
open VerifiableInference.Desc

variable {S Cl : Type}

/-- The number laid at the gated sub-protocol number `n`: the numbers of the owners' marks at its
place, added up, and, if it has a round, the numbers of the falls counted at it. A sub-protocol
without a round would else add the numbers of the falls counted at the one before it a second time.
0 if there is no such sub-protocol. -/
noncomputable def priceAt (pre : List (Block S Cl)) (hm : List Mark)
    (qM : Block S Cl → Mark → ℝ≥0∞) (reps : Block S Cl → List (Fall S))
    (qF : Block S Cl → Fall S → ℝ≥0∞) (n : Nat) : ℝ≥0∞ :=
  match pre[n]? with
  | some b => ((hm.filter fun m => m.place == b.place).map (qM b)).sum +
      (if b.rounds.isEmpty then 0 else ((reps b).map (qF b)).sum)
  | none => 0

variable (hm : List Mark) (qM : Block S Cl → Mark → ℝ≥0∞) (reps : Block S Cl → List (Fall S))
  (qF : Block S Cl → Fall S → ℝ≥0∞)

/-- Its value at the sub-protocol after `A`. -/
theorem priceAt_at {pre A B : List (Block S Cl)} {b : Block S Cl} (e : pre = A ++ b :: B) :
    priceAt pre hm qM reps qF A.length =
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum +
        (if b.rounds.isEmpty then 0 else ((reps b).map (qF b)).sum) := by
  have hg : pre[A.length]? = some b := by
    rw [e, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  simp only [priceAt, hg]

/-- The field `hp₁` of `FirstAsks`, at `p₁ := priceAt pre₁ hm qM reps qF`: with equality. -/
theorem hp₁_sum (pre₁ : List (Block S Cl)) (seatF : Place → Bool) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum + ((reps b).map (qF b)).sum ≤
        priceAt pre₁ hm qM reps qF (0 + A.length) := by
  intro A b b' B e _ hr
  have hne : ¬ (b.rounds.isEmpty = true) := fun h => hr (List.isEmpty_iff.1 h)
  exact le_of_eq (by rw [Nat.zero_add, priceAt_at hm qM reps qF e, if_neg hne])

/-- The field `hp₂` of `FirstAsks`, at the same `p₁`. -/
theorem hp₂_sum (pre₁ : List (Block S Cl)) (seatF : Place → Bool) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B → seatF b.place = false →
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum ≤
        priceAt pre₁ hm qM reps qF (0 + A.length) := by
  intro A b b' B e _
  rw [Nat.zero_add, priceAt_at hm qM reps qF e]
  exact le_self_add

end ProofFile.Honest

#print axioms ProofFile.Honest.priceAt_at
#print axioms ProofFile.Honest.hp₁_sum
#print axioms ProofFile.Honest.hp₂_sum
