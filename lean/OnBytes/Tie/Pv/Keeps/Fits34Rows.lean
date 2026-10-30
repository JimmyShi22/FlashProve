-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/Fits34Rows.lean: plain statements on the openings of a file's three lists of
rounds, from which the third and the fifth clause of the makers' test on these lists follow.

Definitions alone. The makers' test `Three.Whole.fits` (OnBytes/Three/Data.lean) gives every tree of
a file one number over the whole file and lays all trees in one table. Its third clause (`fits3`,
OnBytes/Maker/OkOfTop.lean) says of each opening that the tree stands in the table, was sent no
later than it is opened, and is opened under the table's shape; its fifth (`fits4`) says which
number an opened tree's shape bears. Here the same is said round by round and opening by opening,
with no table.
Main names:
  `firstOf t₁ c`: the number in the label of the first own tree of the chain number c.
  `treesIn R₁ R₂ R₃ c`: the number of trees that the chain number c sends.
  `OpensFit R₁ R₂ R₃ Sh c R`: of every opening of the rounds R of the chain number c whose name
    stands for the tree number y.2 of the chain y.1: that chain is no later than c; the opening's
    shape is Sh y; that shape bears the number firstOf … y.1 + y.2; the chain y.1 sends more than
    y.2 trees; and if it is the chain c itself, the tree's root is sent in this round or before it.
  `row_fits34_of_opens`: the proposition that `OpensFit` of the three lists gives `fits3` and
    `fits4`. It is proved in OnBytes/Tie/Pv/Keeps/Fits34OfOpens.lean.
Limits: nothing is proved here. `OpensFit` is shown of no lists here. Sh is the caller's letter.
-/
import OnBytes.Maker.OkOfTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.OkOf.Rows

open OnBytes OnBytes.Maker
open OnBytes.Params (Rounds)

/-- The number in the label of a chain's first own tree. t₁: the number of trees of the first
chain. -/
def firstOf (t₁ : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | _ => Three.first₃ t₁

/-- The number of trees that a chain sends. -/
def treesIn (R₁ R₂ R₃ : Rounds) : ℕ → ℕ
  | 0 => Three.rootsIn R₁
  | 1 => Three.rootsIn R₂
  | _ => Three.rootsIn R₃

/-- What is asked of the openings of the chain number c with the rounds R. Sh: the one shape of a
tree, by the chain that sends it and its number in that chain. -/
def OpensFit (R₁ R₂ R₃ : Rounds) (Sh : ℕ × ℕ → Fmt.Shape) (c : ℕ) (R : Rounds) : Prop :=
  ∀ (i : ℕ) (r : Fmt.Round × List Fmt.Stored), R[i]? = some r → ∀ o ∈ r.1.opens,
    ∀ y, Three.named c o.2 = some y →
      y.1 ≤ c ∧ o.1 = Sh y ∧ (Sh y).tree = firstOf (Three.rootsIn R₁) y.1 + y.2 ∧
        y.2 < treesIn R₁ R₂ R₃ y.1 ∧
        (y.1 = c → y.2 < (Three.sentBefore R).getD i 0 + r.1.items.countP (· == .root))

/-- `OpensFit` of the three lists gives the two clauses. -/
def row_fits34_of_opens : Prop :=
  ∀ (R₁ R₂ R₃ : Rounds) (Sh : ℕ × ℕ → Fmt.Shape),
    OpensFit R₁ R₂ R₃ Sh 0 R₁ → OpensFit R₁ R₂ R₃ Sh 1 R₂ → OpensFit R₁ R₂ R₃ Sh 2 R₃ →
      fits3 R₁ R₂ R₃ = true ∧ fits4 R₁ R₂ R₃ = true

end OnBytes.Tie.Pv.Keeps.OkOf.Rows
