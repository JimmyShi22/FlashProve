-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPieceExt.lean.
The extension of one piece of a key vector: a rectangle of cells, row by row.

A piece of a call's keys is a rectangle of 2^a rows and Cp columns of cells, laid on 2^(a + k) key
places: the cell in row r and column c is key number 2^k r + c, and the places with c from Cp on
hold 0. This file computes the multilinear extension of such a piece, and ties the plain tables of
equality weights (eqTabK) to the library's Blocks.eqN. All is stated over a field K.

* eqN_congrB: Blocks.eqN reads its point at m coordinates alone.
* tabK_blocks: entry i of eqTabK l, for i below 2^(the length of l), is Blocks.eqN at the list l,
  the top bit's coordinate first.
* exL_getD, exL_len: a stretch of a list, inside the list.
* pieceKeys_ext: under Cp ≤ 2^k, the extension of a piece is the sum over its columns of the
  column's weight times the sum over its rows of the row's weight times the cell. The first a
  coordinates of the point weigh the rows, the next k the columns.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinOut
import OnBytes.Tie.Pv.Lookup.Forest.FoTab
import Cb.Pv.Lookup.Ends.Pieces

set_option autoImplicit false

namespace Fo
open TwV Finset OnBytes.Ends

section
variable {K : Type} [Field K]

theorem eqN_congrB (m off off' : ℕ) (a a' : ℕ → K) (h : ∀ t < m, a (off + t) = a' (off' + t))
    (z : ℕ) : Blocks.eqN m off a z = Blocks.eqN m off' a' z := by
  unfold Blocks.eqN
  exact prod_congr rfl fun t ht => by rw [h t (mem_range.1 ht)]

theorem tabK_blocks (l : List K) (i : ℕ) (hi : i < 2 ^ l.length) :
    (eqTabK l).getD i 0 = Blocks.eqN l.length 0 (Blocks.ofList l) i := by
  rw [eqTabK_get, if_pos hi]
  have e := eqN_top (Blocks.ofList l) 0 l.length i
  simp only [Nat.zero_add] at e
  rw [← e]
  congr 2
  exact (rho_ptL l).symm

omit [Field K] in
theorem exL_len (l : List K) (a b : ℕ) (h : b ≤ l.length) : (exL l a b).length = b - a := by
  unfold exL
  rw [List.length_take, List.length_drop]
  omega

theorem exL_getD (l : List K) (a b t : ℕ) (ht : t < b - a) :
    (exL l a b).getD t 0 = l.getD (a + t) 0 := by
  unfold exL
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt ht,
    List.getElem?_drop]

/-- The extension of one piece. -/
theorem pieceKeys_ext (a k Cp : ℕ) (hC : Cp ≤ 2 ^ k) (x : ℕ → ℕ → K) (inn : ℕ → K) :
    Blocks.ext (a + k)
        (fun Y => if Y / 2 ^ k < 2 ^ a ∧ Y % 2 ^ k < Cp then x (Y / 2 ^ k) (Y % 2 ^ k) else 0) inn =
      ∑ i ∈ range Cp, Blocks.eqN k a inn i * ∑ r ∈ range (2 ^ a), Blocks.eqN a 0 inn r * x r i := by
  have hp : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)
  rw [ext_rows a k]
  have e1 : ∀ r ∈ range (2 ^ a), Blocks.eqN a 0 inn r *
      Blocks.ext k (fun c => if (2 ^ k * r + c) / 2 ^ k < 2 ^ a ∧ (2 ^ k * r + c) % 2 ^ k < Cp then
        x ((2 ^ k * r + c) / 2 ^ k) ((2 ^ k * r + c) % 2 ^ k) else 0) (fun t => inn (a + t)) =
      ∑ i ∈ range Cp, Blocks.eqN a 0 inn r * (Blocks.eqN k a inn i * x r i) := by
    intro r hr
    rw [← mul_sum]
    congr 1
    unfold Blocks.ext
    rw [← sum_subset (range_subset_range.2 hC) (fun c hc hn => by
      have hc' : c < 2 ^ k := mem_range.1 hc
      have hn' : ¬ c < Cp := fun h => hn (mem_range.2 h)
      beta_reduce
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc', if_neg (fun h => hn' h.2), mul_zero])]
    refine sum_congr rfl fun c hc => ?_
    have hc1 : c < Cp := mem_range.1 hc
    have hc' : c < 2 ^ k := lt_of_lt_of_le hc1 hC
    beta_reduce
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc', Nat.mul_add_div hp, Nat.div_eq_of_lt hc',
      Nat.add_zero, if_pos ⟨mem_range.1 hr, hc1⟩, eqN_shift k a]
  rw [sum_congr rfl e1, sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun r _ => by ring

end
end Fo
