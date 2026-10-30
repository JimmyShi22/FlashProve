-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedLazyTree.lean: a Merkle tree, split at a level into blocks. Lists only; no oracle,
no protocol.

A tree over 2 ^ (ℓ + e) leaves (Compile/MerkleM.lean, Compile/MerkleList.lean: `levelsF`, `pathOf`,
`rootOf`) is a tree of depth e over its level ℓ, and each node of level ℓ is the root of a tree of
depth ℓ over a block of 2 ^ ℓ leaves.

  `lvl`   level ℓ over the leaves l. `getD_levelsF_lvl`: it is entry ℓ of the list of all levels
  `block`   `block ℓ u l` is the leaves u · 2^ℓ, .., (u + 1) · 2^ℓ - 1. `pairUpF_block`: one level
            up, the blocks are the blocks of the next level
  `rootOf_block`   node u of level ℓ is the root of the tree over block u
  `pathOf_block`   the path of leaf q is its path in the tree over its block, followed by the path
                   of that block's root in the tree over level ℓ

So whoever holds level ℓ can open leaf q from the 2^ℓ leaves of one block. There is no hypothesis on
the lengths of the lists: beyond the end of a list both sides read the default value.
-/
import Compile.MerkleList

namespace Compile.Batch
namespace Seed

variable {D : Type} (h : D → D → D)

/-- level ℓ over the leaves l -/
def lvl : ℕ → List D → List D
  | 0, l => l
  | ℓ + 1, l => lvl ℓ (pairUpF h l)

theorem getD_levelsF_lvl : ∀ (ℓ e : ℕ) (l : List D), (levelsF h (ℓ + e) l).getD ℓ [] = lvl h ℓ l
  | 0, e, l => by
      obtain ⟨ls, hls⟩ := exists_levelsF_eq_cons h (0 + e) l
      rw [hls]
      rfl
  | ℓ + 1, e, l => by
      rw [show ℓ + 1 + e = (ℓ + e) + 1 by omega, levelsF_succ, List.getD_cons_succ]
      exact getD_levelsF_lvl ℓ e _

/-- the leaves u · 2^ℓ, .., (u + 1) · 2^ℓ - 1 -/
def block (ℓ u : ℕ) (l : List D) : List D := (l.drop (u * 2 ^ ℓ)).take (2 ^ ℓ)

theorem pairUpF_drop : ∀ (n : ℕ) (l : List D), pairUpF h (l.drop (2 * n)) = (pairUpF h l).drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, [a] => by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      show pairUpF h [] = ([a] : List D).drop (n + 1)
      simp
      rfl
  | n + 1, a :: b :: t => by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, List.drop_succ_cons, List.drop_succ_cons,
        pairUpF_cons₂, List.drop_succ_cons]
      exact pairUpF_drop n t

theorem pairUpF_take : ∀ (n : ℕ) (l : List D), pairUpF h (l.take (2 * n)) = (pairUpF h l).take n
  | 0, _ => by simp; rfl
  | _ + 1, [] => rfl
  | n + 1, [a] => by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      show pairUpF h (a :: ([] : List D).take (2 * n + 1)) = ([a] : List D).take (n + 1)
      simp
      rfl
  | n + 1, a :: b :: t => by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, List.take_succ_cons, List.take_succ_cons,
        pairUpF_cons₂, pairUpF_cons₂, List.take_succ_cons]
      exact congrArg _ (pairUpF_take n t)

/-- one level up, the blocks are the blocks of the next level -/
theorem pairUpF_block (ℓ u : ℕ) (l : List D) :
    pairUpF h (block (ℓ + 1) u l) = block ℓ u (pairUpF h l) := by
  unfold block
  rw [show 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ by rw [pow_succ]; omega, pairUpF_take,
    Nat.mul_left_comm u 2 (2 ^ ℓ), pairUpF_drop]

variable [Inhabited D]

/-- for r < 2^ℓ, entry r of block u is leaf u · 2^ℓ + r -/
theorem getD_block {ℓ r : ℕ} (u : ℕ) (l : List D) (hr : r < 2 ^ ℓ) :
    (block ℓ u l).getD r default = l.getD (u * 2 ^ ℓ + r) default := by
  unfold block
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hr, List.getElem?_drop]

/-- Node u of level ℓ is the root of the tree over block u. -/
theorem rootOf_block :
    ∀ (ℓ u : ℕ) (l : List D), rootOf (levelsF h ℓ (block ℓ u l)) = (lvl h ℓ l).getD u default
  | 0, u, l => by
      show ((block 0 u l)).headD default = l.getD u default
      have e := getD_block (ℓ := 0) (r := 0) u l (Nat.two_pow_pos 0)
      rw [pow_zero, Nat.mul_one, Nat.add_zero] at e
      rw [← e]
      cases block 0 u l <;> rfl
  | ℓ + 1, u, l => by
      obtain ⟨ls, hls⟩ := exists_levelsF_eq_cons h ℓ (pairUpF h (block (ℓ + 1) u l))
      rw [levelsF_succ, hls, rootOf_cons₂, ← hls, pairUpF_block]
      exact rootOf_block ℓ u (pairUpF h l)

/-- The path of leaf q: its path in the tree over its block, then the path of that block's root in
the tree over level ℓ. -/
theorem pathOf_block :
    ∀ (ℓ e : ℕ) (l : List D) (q : ℕ), pathOf (levelsF h (ℓ + e) l) q =
      pathOf (levelsF h ℓ (block ℓ (q / 2 ^ ℓ) l)) (q % 2 ^ ℓ) ++
        pathOf (levelsF h e (lvl h ℓ l)) (q / 2 ^ ℓ)
  | 0, e, l, q => by
      rw [Nat.zero_add, pow_zero, Nat.div_one]
      rfl
  | ℓ + 1, e, l, q => by
      obtain ⟨ls, hls⟩ := exists_levelsF_eq_cons h (ℓ + e) (pairUpF h l)
      obtain ⟨ls', hls'⟩ :=
        exists_levelsF_eq_cons h ℓ (pairUpF h (block (ℓ + 1) (q / 2 ^ (ℓ + 1)) l))
      have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; omega
      have hpos : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
      have hr : q % 2 ^ (ℓ + 1) < 2 ^ (ℓ + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hq : q / 2 ^ (ℓ + 1) * 2 ^ (ℓ + 1) + q % 2 ^ (ℓ + 1) = q := Nat.div_add_mod' q _
      have hpar : q % 2 ^ (ℓ + 1) % 2 = q % 2 := Nat.mod_mod_of_dvd q ⟨2 ^ ℓ, hp⟩
      have e1 : q / 2 ^ (ℓ + 1) = q / 2 / 2 ^ ℓ := by rw [hp, Nat.div_div_eq_div_mul]
      have e2 : q % 2 ^ (ℓ + 1) / 2 = q / 2 % 2 ^ ℓ := by
        rw [hp, Nat.mod_mul_right_div_self]
      rw [show ℓ + 1 + e = (ℓ + e) + 1 by omega, levelsF_succ, hls, pathOf_cons₂, ← hls,
        levelsF_succ, hls', pathOf_cons₂, ← hls', pairUpF_block, List.cons_append,
        pathOf_block ℓ e (pairUpF h l) (q / 2), e2, ← e1]
      congr 1
      by_cases hev : q % 2 = 0
      · rw [if_pos hev, if_pos (hpar.trans hev), getD_block _ _ (by omega)]
        congr 1
        omega
      · rw [if_neg hev, if_neg (by rw [hpar]; exact hev), getD_block _ _ (by omega)]
        congr 1
        omega

end Seed
end Compile.Batch
