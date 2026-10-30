-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/MerkleM.lean: Merkle trees over 2^d leaves, as programs on lists, without dependent types,
in any monad with a node function.

The theory without monads (collisions, extraction) is in Hash/MerklePure.lean;
Compile/MerkleList.lean relates the two.

Limits: nothing here asks that a list has 2^d entries or that j is below 2^d: `pairUp` passes an odd
last entry up unhashed; `rootOf` and `pathOf` take `default` where an entry is missing.
-/
import Mathlib.Data.Nat.Notation

namespace Compile
variable {M : Type → Type} [Monad M] {D : Type}

/-- one level up: hash neighbours in pairs; an odd last entry goes up as it is -/
def pairUp (hN : D → D → M D) : List D → M (List D)
  | a :: b :: t => do
      let c ← hN a b
      let r ← pairUp hN t
      pure (c :: r)
  | l => pure l

/-- all levels, leaves first; d steps -/
def levelsM (hN : D → D → M D) : ℕ → List D → M (List (List D))
  | 0, l => pure [l]
  | d + 1, l => do
      let u ← pairUp hN l
      let r ← levelsM hN d u
      pure (l :: r)

/-- the root: the first entry of the last level -/
def rootOf [Inhabited D] (lv : List (List D)) : D := (lv.getLastD []).headD default

/-- the sibling digests of leaf j, from the leaves upwards (the last level, the root, has none) -/
def pathOf [Inhabited D] : List (List D) → ℕ → List D
  | [], _ => []
  | [_], _ => []
  | l :: ls, j => l.getD (if j % 2 = 0 then j + 1 else j - 1) default :: pathOf ls (j / 2)

/-- from a leaf digest and its path to a root -/
def climbM (hN : D → D → M D) : List D → ℕ → D → M D
  | [], _, c => pure c
  | s :: ss, j, c => do
      let u ← if j % 2 = 0 then hN c s else hN s c
      climbM hN ss (j / 2) u

end Compile
