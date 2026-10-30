-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/CountsPos.lean: a number of a shape: the sum, over the rounds, of the leaves of the hash
tree over the round's oracle.

A definition, statements (in `Iop.Spec`) and proofs. Framework only. Nothing assumed beyond the
hypotheses of the statements and whatever the arguments hold as proofs.
A shape (`Shape`, Iop/Shape.lean) is the list of a protocol's rounds, in order.

Why: a bound "rounds · (a tree over the largest oracle)" is harmless for a protocol of a hundred
rounds and ruinous for one of 10^5 rounds of which a few hundred send an oracle. Here a round
without an oracle adds 1 (the tree over no position has one leaf), a round with an oracle of c
positions adds lvOf c = 2^⌈log₂ c⌉: exactly c at a power of two.

Main names:
  `Shape.leafSum s`: the sum over the rounds r of s of lvOf (Nat.card r.Pos).
  `Spec.leafSum_app`: it is additive.
  `Spec.leafSum_le`: at most ro rounds, each with at most 2^dp positions ⇒ leafSum s ≤ ro · 2^dp.
    The coarse bound is a consequence.
  `Spec.lvLoc_leaf`: the compiler's count of leaves of an ordinary protocol (`lvLoc`,
    CompileK/Counts.lean) is this number.
  `Spec.lvB_leaf`: those of a batch protocol (`lvJ`, `lv0`), at every annotation (`RoundSplits`,
    Iop/Batch.lean), are at most it.

Limits: `Nat.card` of an infinite type is 0: `leafSum` alone would count an infinite oracle as 1.
`lvLoc_leaf`, `lvB_leaf` take pt : s.IsPoint, under which every round's positions are finite.
This file does not say any protocol's number.

Terms: lean/GLOSSARY.md.
-/
import CompileK.CountsRecut
import Iop.SplitNonce
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop

/-- The leaves of the trees over all oracles. -/
def Shape.leafSum : Shape → ℕ
  | [] => 0
  | r :: s => lvOf (Nat.card r.Pos) + Shape.leafSum s

namespace Spec

def leafSum_app : Prop := ∀ s t : Shape, Shape.leafSum (s ++ t) = Shape.leafSum s + Shape.leafSum t

def leafSum_le : Prop :=
  ∀ (s : Shape) (ro dp : ℕ),
    s.length ≤ ro → (∀ r ∈ s, Nat.card r.Pos ≤ 2 ^ dp) → Shape.leafSum s ≤ ro * 2 ^ dp

def lvLoc_leaf : Prop := ∀ (s : Shape) (pt : s.IsPoint), Shape.lvLoc s pt = Shape.leafSum s

def lvB_leaf : Prop :=
  ∀ (s : Shape) (A : RoundSplits s) (pt : s.IsPoint),
    Shape.lvJ s A pt ≤ Shape.leafSum s ∧ Shape.lv0 s A pt ≤ Shape.leafSum s

end Spec

/-- lvOf is monotone -/
theorem lvOf_grows {a b : ℕ} (h : a ≤ b) : lvOf a ≤ lvOf b :=
  Nat.pow_le_pow_right (by norm_num) (Nat.clog_mono_right 2 h)

theorem leafSum_app : Spec.leafSum_app := by
  intro s t
  induction s with
  | nil => exact (Nat.zero_add _).symm
  | cons r s ih =>
    show lvOf (Nat.card r.Pos) + Shape.leafSum (s ++ t) =
      lvOf (Nat.card r.Pos) + Shape.leafSum s + Shape.leafSum t
    rw [ih, Nat.add_assoc]

theorem leafSum_le : Spec.leafSum_le := by
  intro s ro dp hl hs
  have key : ∀ s : Shape,
      (∀ r ∈ s, Nat.card r.Pos ≤ 2 ^ dp) → Shape.leafSum s ≤ s.length * 2 ^ dp := by
    intro s
    induction s with
    | nil => exact fun _ => Nat.zero_le _
    | cons r s ih =>
      intro hs
      have h1 : lvOf (Nat.card r.Pos) ≤ 2 ^ dp :=
        le_of_le_of_eq (lvOf_grows (hs r List.mem_cons_self)) (lvOf_pow dp)
      have h2 := ih fun r' hr => hs r' (List.mem_cons_of_mem _ hr)
      show lvOf (Nat.card r.Pos) + Shape.leafSum s ≤ (s.length + 1) * 2 ^ dp
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      exact Nat.add_le_add h2 h1
  exact le_trans (key s hs) (Nat.mul_le_mul_right _ hl)

theorem lvLoc_leaf : Spec.lvLoc_leaf := by
  intro s
  induction s with
  | nil => exact fun _ => rfl
  | cons r s ih =>
    rintro ⟨pt, pts⟩
    letI := pt.finPos
    show lvOf (Fintype.card r.Pos) + Shape.lvLoc s pts = lvOf (Nat.card r.Pos) + Shape.leafSum s
    rw [Nat.card_eq_fintype_card, ih pts]

theorem lvB_leaf : Spec.lvB_leaf := by
  intro s
  induction s with
  | nil => exact fun _ _ => ⟨Nat.zero_le _, Nat.zero_le _⟩
  | cons r s ih =>
    rintro ⟨a, A⟩ ⟨pt, pts⟩
    letI := pt.finPos
    have h2 := ih A pts
    have hp := RAnn.card_parts a pt
    refine ⟨?_, ?_⟩
    · show lvOf (a.cardJ pt) + Shape.lvJ s A pts ≤ lvOf (Nat.card r.Pos) + Shape.leafSum s
      rw [Nat.card_eq_fintype_card]
      exact Nat.add_le_add (lvOf_grows (by omega)) h2.1
    · show lvOf (a.card0 pt) + Shape.lv0 s A pts ≤ lvOf (Nat.card r.Pos) + Shape.leafSum s
      rw [Nat.card_eq_fintype_card]
      exact Nat.add_le_add (lvOf_grows (by omega)) h2.2

end Iop
