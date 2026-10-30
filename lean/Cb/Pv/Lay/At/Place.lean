-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/Place.lean: vectors that are laid as blocks into a long vector, their extensions, and
the degrees of these as functions of the point.

A long vector of 2^(h + g) entries is cut into 2^h blocks of 2^g entries. The extension of a vector
that is 0 outside one block is an equality weight in the first h coordinates times an extension in
the last g coordinates. So it is a product of a function of the first coordinates and a function of
the last ones, and the degrees of the two add up to 1 in each variable.

Main names:
  `blk g n v`: the vector v of 2^g entries as block number n of a long vector.
  `extAt g off v ζ`: the extension of v at the coordinates off, .., off + g - 1 of ζ.
  `ext_blk`: the extension of a block.
  `extAt_tensor`: the extension of a vector of products u (row) * v (column).
  `win off g`: the degrees 1 at the variables off, .., off + g - 1 and 0 elsewhere.
  `degLE_eqN`, `degLE_extAt`: an equality weight and an extension at these coordinates have the
  degrees win off g.
Limits: identities and degrees alone.


-/
import Cb.Pv.Lay.Prod
import Blocks.LookupCalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.At
open Finset
open Blocks (eqN ext)

section Place
variable {E : Type} [Field E]

/-- The vector v of 2^g entries as block number n of a long vector. -/
def blk (g n : ℕ) (v : ℕ → E) (y : ℕ) : E := if y / 2 ^ g = n then v (y % 2 ^ g) else 0

/-- The extension of v at the coordinates off, .., off + g - 1 of ζ. -/
def extAt (g off : ℕ) (v ζ : ℕ → E) : E := ∑ y ∈ range (2 ^ g), eqN g off ζ y * v y

theorem div_at (g x : ℕ) {y : ℕ} (hy : y < 2 ^ g) : (x * 2 ^ g + y) / 2 ^ g = x := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos g), Nat.div_eq_of_lt hy,
    Nat.zero_add]

theorem mod_at (g x : ℕ) {y : ℕ} (hy : y < 2 ^ g) : (x * 2 ^ g + y) % 2 ^ g = y := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]

/-- The extension of a block. -/
theorem ext_blk (h g : ℕ) {n : ℕ} (hn : n < 2 ^ h) (v ζ : ℕ → E) :
    ext (h + g) (blk g n v) ζ = eqN h 0 ζ n * extAt g h v ζ := by
  rw [Blocks.ext_two, Finset.sum_eq_single n]
  · unfold extAt
    rw [mul_sum]
    refine sum_congr rfl fun y hy => ?_
    have hy' := mem_range.mp hy
    unfold blk
    rw [if_pos (div_at g n hy'), mod_at g n hy']
    ring
  · intro x _ hx
    refine sum_eq_zero fun y hy => ?_
    unfold blk
    rw [if_neg (by rw [div_at g x (mem_range.mp hy)]; exact hx), mul_zero]
  · intro hc
    exact absurd (mem_range.mpr hn) hc

/-- The extension of a vector of products of a function of the row and a function of the column. -/
theorem extAt_tensor (a b off : ℕ) (u v ζ : ℕ → E) :
    extAt (a + b) off (fun y => u (y / 2 ^ b) * v (y % 2 ^ b)) ζ =
      extAt a off u ζ * extAt b (off + a) v ζ := by
  unfold extAt
  rw [pow_add, Alg.sum_range_mul_add, Finset.sum_mul_sum]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y hy => ?_
  have hy' := mem_range.mp hy
  beta_reduce
  rw [Blocks.eqN_append' a b off ζ x hy', div_at b x hy', mod_at b x hy']
  ring

/-- A constant factor moves out of extAt. -/
theorem extAt_smul (g off : ℕ) (c : E) (v ζ : ℕ → E) :
    extAt g off (fun y => c * v y) ζ = c * extAt g off v ζ := by
  unfold extAt
  rw [mul_sum]
  exact sum_congr rfl fun y _ => by ring

/-- extAt reads v below 2^g alone. -/
theorem extAt_congr {g off : ℕ} {v w : ℕ → E} (h : ∀ y, y < 2 ^ g → v y = w y) (ζ : ℕ → E) :
    extAt g off v ζ = extAt g off w ζ :=
  sum_congr rfl fun y hy => by rw [h y (mem_range.mp hy)]

/-- A vector that is 0 from n on. -/
theorem extAt_cut {g n off : ℕ} (hn : n ≤ 2 ^ g) (v ζ : ℕ → E) :
    extAt g off (fun y => if y < n then v y else 0) ζ = ∑ y ∈ range n, eqN g off ζ y * v y := by
  unfold extAt
  rw [← sum_subset (range_subset_range.mpr hn)]
  · exact sum_congr rfl fun y hy => by
      beta_reduce
      rw [if_pos (mem_range.mp hy)]
  · intro y _ hy
    beta_reduce
    rw [if_neg fun hc => hy (mem_range.mpr hc), mul_zero]

/-! ### Degrees -/

/-- The degrees 1 at the variables off, .., off + g - 1 and 0 elsewhere. -/
def win {k : ℕ} (off g : ℕ) : Fin k → ℕ := fun i => if off ≤ i.val ∧ i.val < off + g then 1 else 0

/-- An equality weight at the coordinates off, .., off + g - 1. -/
theorem degLE_eqN {k : ℕ} (g off n : ℕ) (h : off + g ≤ k) :
    Alg.DegLE (win off g) fun z : Fin k → E => eqN g off (Blocks.nat z) n := by
  have e : (fun z : Fin k → E => eqN g off (Blocks.nat z) n) =
      fun z => Alg.eqk (fun t : Fin g => z ⟨off + t, by have := t.isLt; omega⟩)
        (Alg.bits g n) := by
    funext z
    rw [Blocks.eqN_eq]
    unfold Alg.eqN
    congr 1
    funext t
    unfold Blocks.nat
    rw [dif_pos (by have := t.isLt; omega)]
  rw [e]
  refine (Alg.DegLE.eqk (K := E) (Alg.bits g n)).comp
    (fun t : Fin g => (⟨off + t, by have := t.isLt; omega⟩ : Fin k))
    (fun a b hab => ?_) (win off g) fun t => ?_
  · have := congrArg Fin.val hab
    exact Fin.ext (by simpa using this)
  · unfold win
    rw [if_pos ⟨Nat.le_add_right _ _, by have := t.isLt; show off + (t : ℕ) < off + g; omega⟩]

/-- An extension at the coordinates off, .., off + g - 1. -/
theorem degLE_extAt {k : ℕ} (g off : ℕ) (v : ℕ → E) (h : off + g ≤ k) :
    Alg.DegLE (win off g) fun z : Fin k → E => extAt g off v (Blocks.nat z) :=
  Alg.DegLE.sum _ fun y _ => (degLE_eqN g off y h).mul_const (v y)

/-- Two windows that follow one another. -/
theorem win_add {k : ℕ} (a b : ℕ) (v : Fin k) : win (k := k) 0 a v + win a b v ≤ 1 := by
  unfold win
  split_ifs <;> omega

end Place

end Cb.Pv.Lay.At

#print axioms Cb.Pv.Lay.At.ext_blk
#print axioms Cb.Pv.Lay.At.extAt_tensor
#print axioms Cb.Pv.Lay.At.degLE_extAt
