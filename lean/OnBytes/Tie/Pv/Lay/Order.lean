-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/Order.lean: the two orders in which the model's product layers bind their
variables, as closed facts on the model's own lists.

In `levelRounds` (OnBytes/Model/Psc.lean) round number j runs in variable v = order[j]; its
coordinate of the equality point is rho[mu - 1 - v], and its challenge is stored at the same
place. The model has two lists: `orderDefault mu` and `orderRange mu` (OnBytes/Model/Frame.lean).

Main names:
  `coords mu order`: the places of rho that the rounds read, in the rounds' order.
  `default_coords`: under `orderDefault` round j reads rho[j].
  `range_coords`: for 9 ≤ mu, under `orderRange` the rounds read rho at mu - 3, mu - 2, mu - 1, mu
    - 6, mu - 5, mu - 4, mu - 9, mu - 8, mu - 7, and then at 0, 1, .., mu - 10.
  `default_perm`, `range_perm`: each list is a permutation of 0, .., mu - 1 (the second for 9 ≤
    mu): every variable is bound just once. `default_length`, `range_length`: each has mu members.
  `range_short`: below 9 `orderRange` has 9 members, not mu.
  `orders_part`, `orders_ne`: at mu = 9 the two orders differ.

Limits: nothing is said on a run, nor on whose challenges the coordinates of rho are.
-/
import OnBytes.Model.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay

open OnBytes OnBytes.Model

/-- the places of rho that the rounds read, in the rounds' order -/
def coords (mu : Nat) (order : List Nat) : List Nat := order.map (mu - 1 - ·)

theorem default_length (mu : Nat) : (orderDefault mu).length = mu := by simp [orderDefault]

theorem default_perm (mu : Nat) : (orderDefault mu).Perm (List.range mu) := List.reverse_perm _

theorem rev_coords (n c : Nat) : ((List.range n).reverse.map (· + c)).map (n + c - 1 - ·) =
    List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_reverse, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
    omega

theorem default_coords (mu : Nat) : coords mu (orderDefault mu) = List.range mu := by
  have h := rev_coords mu 0
  simpa [coords, orderDefault] using h

theorem range_length (mu : Nat) (h : 9 ≤ mu) : (orderRange mu).length = mu := by
  simp [orderRange]
  omega

theorem range_short (mu : Nat) (h : mu < 9) : (orderRange mu).length = 9 := by
  simp [orderRange]
  omega

theorem range_perm (mu : Nat) (h : 9 ≤ mu) : (orderRange mu).Perm (List.range mu) := by
  obtain ⟨n, rfl⟩ : ∃ n, mu = 9 + n := ⟨mu - 9, by omega⟩
  have e : List.range (9 + n) = List.range 9 ++ (List.range n).map (9 + ·) := List.range_add
  rw [e]
  unfold orderRange
  refine List.Perm.append (by decide) ?_
  have e2 : 9 + n - 9 = n := by omega
  rw [e2]
  have e3 : (List.range n).map (9 + ·) = (List.range n).map (· + 9) := by
    apply List.map_congr_left
    intro a _
    omega
  rw [e3]
  exact (List.reverse_perm _).map _

theorem range_coords (mu : Nat) (h : 9 ≤ mu) : coords mu (orderRange mu) =
    [mu - 3, mu - 2, mu - 1, mu - 6, mu - 5, mu - 4, mu - 9, mu - 8, mu - 7] ++ List.range (mu -
        9) := by
  obtain ⟨n, rfl⟩ : ∃ n, mu = n + 9 := ⟨mu - 9, by omega⟩
  have e2 : n + 9 - 9 = n := by omega
  unfold coords orderRange
  rw [e2, List.map_append, rev_coords n 9]
  congr 1

/-- The two orders part at the least mu for which `orderRange` is meant: with `orderDefault` in
its place the equation of `range_coords` is false. -/
theorem orders_part : coords 9 (orderDefault 9) ≠ [9 - 3, 9 - 2, 9 - 1, 9 - 6, 9 - 5, 9 - 4, 9 -
    9, 9 - 8, 9 - 7] ++ List.range (9 - 9) := by
  decide

theorem orders_ne : orderRange 9 ≠ orderDefault 9 := by decide

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.orders_part
#print axioms OnBytes.Tie.Pv.Lay.orders_ne
#print axioms OnBytes.Tie.Pv.Lay.default_coords
#print axioms OnBytes.Tie.Pv.Lay.default_perm
#print axioms OnBytes.Tie.Pv.Lay.range_coords
#print axioms OnBytes.Tie.Pv.Lay.range_perm
#print axioms OnBytes.Tie.Pv.Lay.range_length
#print axioms OnBytes.Tie.Pv.Lay.range_short
