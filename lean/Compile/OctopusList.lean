-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/OctopusList.lean: the honest trees of Compile/MerkleM.lean have the paths and roots of
Hash/OctopusFacts.lean, under the conditions below. The first are lists of levels (`pathOf`,
`rootOf`; `levelsF`: Compile/MerkleList.lean); the second, those of a function from leaf numbers to
leaf digests (`upG`, `topG`, `hpath`).

  `pathOf_eq_hpath`, `rootOf_eq_topG`    Let l be 2^d leaf digests and let g hold them at the
                                         numbers t * 2^d, .., t * 2^d + 2^d - 1 (tree number t of a
                                         forest). Then the path that pathOf reads off the levels for
                                         leaf j < 2^d is hpath at the number t * 2^d + j, and the
                                         root of the levels is level d of g at the number t.
  `mem_upN`                              Every node that is left after d levels is the ancestor j /
                                         2^d of a node j of the list.
Notation: Octopus: "pruned Merkle paths ("authentication octopus")" (the head of Hash/Octopus.lean);
`js` (the list in the row of `mem_upN`): a list of natural numbers; "a list js of node numbers"
(there); `hN`: a function D → D → D; "a function `hN` that hashes two children" (there).

No oracle, no probability.
-/
import Hash.OctopusFacts
import Compile.MerkleList

namespace Compile
open Octopus

variable {D : Type} [Inhabited D] (hN : D → D → D)

theorem upG_of_block {d t : ℕ} {l : List D} {g : ℕ → D} (hl : l.length = 2 ^ (d + 1))
    (hg : ∀ i < 2 ^ (d + 1), g (t * 2 ^ (d + 1) + i) = l.getD i default) :
    ∀ i < 2 ^ d, upG hN g (t * 2 ^ d + i) = (pairUpF hN l).getD i default := by
  intro i hi
  have h2 : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ, Nat.mul_comm]
  rw [getD_pairUpF hN l i (by omega), ← hg (2 * i) (by omega), ← hg (2 * i + 1) (by omega)]
  unfold upG
  have e1 : 2 * (t * 2 ^ d + i) = t * 2 ^ (d + 1) + 2 * i := by rw [h2]; ring
  rw [e1, Nat.add_assoc]

/-- The path that is read off the levels is the honest path of the forest (hypotheses below). -/
theorem pathOf_eq_hpath :
    ∀ (d t : ℕ) (l : List D) (g : ℕ → D) (j : ℕ), l.length = 2 ^ d →
      (∀ i < 2 ^ d, g (t * 2 ^ d + i) = l.getD i default) → j < 2 ^ d →
      pathOf (levelsF hN d l) j = hpath hN d g (t * 2 ^ d + j)
  | 0, _, _, _, _, _, _, _ => rfl
  | d + 1, t, l, g, j, hl, hg, hj => by
      obtain ⟨ls, hls⟩ := exists_levelsF_eq_cons hN d (pairUpF hN l)
      have h2 : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ, Nat.mul_comm]
      have hj2 : j / 2 < 2 ^ d := by omega
      have ih := pathOf_eq_hpath d t (pairUpF hN l) (upG hN g) (j / 2)
        (length_pairUpF hN _ l (by rw [hl, h2])) (upG_of_block hN hl hg) hj2
      have h3 : t * 2 ^ (d + 1) = 2 * (t * 2 ^ d) := by rw [h2]; ring
      have e1 : (t * 2 ^ (d + 1) + j) / 2 = t * 2 ^ d + j / 2 := by rw [h3]; omega
      have e2 : sibOf (t * 2 ^ (d + 1) + j) =
          t * 2 ^ (d + 1) + (if j % 2 = 0 then j + 1 else j - 1) := by
        unfold sibOf
        have : (t * 2 ^ (d + 1) + j) % 2 = j % 2 := by rw [h3]; omega
        rw [this]
        split_ifs <;> omega
      rw [levelsF_succ, hls, pathOf_cons₂, ← hls, ih, hpath, e1, e2, hg _ (by split_ifs <;> omega)]

/-- The root of the levels is level d of the forest at the number of the tree (hypotheses below). -/
theorem rootOf_eq_topG :
    ∀ (d t : ℕ) (l : List D) (g : ℕ → D), l.length = 2 ^ d →
      (∀ i < 2 ^ d, g (t * 2 ^ d + i) = l.getD i default) → rootOf (levelsF hN d l) = topG hN d g t
  | 0, t, l, g, hl, hg => by
      have := hg 0 (by simp)
      simp only [pow_zero, Nat.mul_one, Nat.add_zero] at this
      rw [topG, this]
      match l, hl with
      | [a], _ => rfl
  | d + 1, t, l, g, hl, hg => by
      obtain ⟨ls, hls⟩ := exists_levelsF_eq_cons hN d (pairUpF hN l)
      have h2 : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ, Nat.mul_comm]
      have ih := rootOf_eq_topG d t (pairUpF hN l) (upG hN g)
        (length_pairUpF hN _ l (by rw [hl, h2])) (upG_of_block hN hl hg)
      rw [levelsF_succ, hls, rootOf_cons₂, ← hls, ih, topG]

omit [Inhabited D] in
theorem mem_upN : ∀ (d : ℕ) (js : List ℕ) (x : ℕ), x ∈ upN d js → ∃ k ∈ js, x = k / 2 ^ d
  | 0, _, x, h => ⟨x, h, by simp⟩
  | d + 1, js, x, h => by
      obtain ⟨k, hk, rfl⟩ := mem_upN d (up js) x h
      obtain ⟨k', hk', rfl⟩ := mem_up js k hk
      exact ⟨k', hk', by rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]⟩

end Compile
