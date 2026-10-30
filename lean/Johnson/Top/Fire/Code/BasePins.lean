-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/BasePins.lean: THE MESSAGES WHOSE PIN IS OPEN AT EACH BORDER OF THE KEY FILE's THREE CHAINS, AS WRITTEN NUMBERS, and the test «the pinned trees lie below the pieces' bases» (BaseNums.lean) at these lists. DEFINITIONS ALONE, over BaseNums.lean, which stands over the data's type alone (OnBytes/Maker/Whole.lean): so that a test can be laid where no table of ours may be imported.
Main names. `pinsW₁` | `pinsW₂` | `pinsW₃`: the lists, border by border · `pinW L n`: the n-th, nothing beyond the list · `basesDoor at_ rs₁ rs₂ rs₃ D`: `basesAllN` at them.
That these are our tables' own lists, and what a yes gives: BasePinsTie.lean.
Nothing on soundness.

-/
import Johnson.Top.Fire.Code.BaseNums

set_option autoImplicit false

namespace LPFD
open OnBytes.Maker

/-- The first chain's borders 0 to 19. -/
def pinsW₁ : List (List Nat) := [[], [0], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0], [0], [0, 2], [0, 2]]

/-- The shared chain's borders 0 to 12. -/
def pinsW₂ : List (List Nat) := [[0, 2], [0, 2], [0, 2], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3, 4, 5], [0, 2, 3, 4, 5], [0, 2, 3, 4, 5], [0, 2, 3, 4, 5], [0, 2, 4, 5], [0, 2, 4], [0, 2, 4]]

/-- The last chain's borders 0 to 4. -/
def pinsW₃ : List (List Nat) := [[0, 2, 4], [0, 2, 4], [0, 2, 4], [], []]

/-- The n-th list; nothing beyond. -/
def pinW (L : List (List Nat)) (n : Nat) : List Nat := L.getD n []

/-- **The pinned trees lie below the pieces' bases, at every border of the three chains, at the written lists.** rs_j: the blocks' numbers of declared rounds. -/
def basesDoor (at_ : Nat → Nat × Nat) (rs₁ rs₂ rs₃ : List Nat) (D : WholeD) : Bool :=
  basesAllN at_ (pinW pinsW₁) (pinW pinsW₂) (pinW pinsW₃) rs₁ rs₂ rs₃ D

end LPFD
