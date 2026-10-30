-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/PanPlace.lean: the panels of a group of layers as blocks of the two long vectors of the
batched sumcheck.

The library lays the panels end to end, sorted by their numbers of bits, largest first
(Inst/Model/FF/Objects.lean: offP). So a panel of w bits begins at a multiple of 2^w: it is one
block of 2^w entries, and each of its rows is one block of 2^wc entries, wc the bits of a column.

Main names:
  `blk_eq`: a block, with its stretch written out. `blk_mul_sum`: the inner product of two vectors
  that live on one block.
  `rows_blk`: vectors laid as the rows of a block make up one vector on the block.
  `off_dvd`: a panel begins at a multiple of its size. `nP`: its block's number. `pan_out`: a vector
  on the panel's block is 0 outside the panel's stretch.
  `cellOf`: a function of row and column as a vector on the panel's block, 0 outside its rows and
  columns. `local_sum`: the inner product on a block with such a vector.
  `pans_sum`: for two families of vectors on the panels' blocks, the inner product of the two long
  vectors is the sum over the panels of the inner products on the blocks.
Limits: identities alone.


-/
import Cb.Pv.Lay.At.Place
import Cb.Pv.Lay.End.SigC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.At
open Finset
open Inst.Model.FFSeg (Dim Pan pans offP lamS)
open Cb.Pv.Lay.End.Sig (before offP_eq inStretch sum_stretch sum_corner sum_apart pans_apart
  off_inside)

variable {E : Type} [Field E]

/-- A block, with its stretch written out. -/
theorem blk_eq (g n : ℕ) (V : ℕ → E) (y : ℕ) :
    blk g n V y = if n * 2 ^ g ≤ y ∧ y < n * 2 ^ g + 2 ^ g then V (y - n * 2 ^ g) else 0 := by
  unfold blk
  have hW : 0 < 2 ^ g := Nat.two_pow_pos g
  have hdm := Nat.div_add_mod y (2 ^ g)
  have hm := Nat.mod_lt y hW
  by_cases h : y / 2 ^ g = n
  · subst h
    have e : y / 2 ^ g * 2 ^ g = 2 ^ g * (y / 2 ^ g) := Nat.mul_comm _ _
    rw [if_pos rfl, if_pos ⟨by omega, by omega⟩]
    congr 1
    omega
  · rw [if_neg h, if_neg]
    rintro ⟨h1, h2⟩
    exact h (Nat.div_eq_of_lt_le h1 (by rw [Nat.add_mul, Nat.one_mul]; exact h2))

/-- The inner product of two vectors that live on one block. -/
theorem blk_mul_sum {g n N : ℕ} (hN : n * 2 ^ g + 2 ^ g ≤ N) (V V' : ℕ → E) :
    ∑ y ∈ range N, blk g n V y * blk g n V' y = ∑ t ∈ range (2 ^ g), V t * V' t := by
  rw [← sum_stretch hN fun t => V t * V' t]
  refine sum_congr rfl fun y _ => ?_
  rw [blk_eq, blk_eq]
  by_cases h : n * 2 ^ g ≤ y ∧ y < n * 2 ^ g + 2 ^ g
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h, zero_mul]

/-- Vectors laid as the first R rows of a block make up one vector on the block. a: the bits of a
row's number; b: the bits of a column. -/
theorem rows_blk (a b n R : ℕ) (hR : R ≤ 2 ^ a) (v : ℕ → ℕ → E) (y : ℕ) :
    ∑ e ∈ range R, blk b (n * 2 ^ a + e) (v e) y =
      blk (a + b) n (fun t => if t / 2 ^ b < R then v (t / 2 ^ b) (t % 2 ^ b) else 0) y := by
  have hA : 0 < 2 ^ a := Nat.two_pow_pos a
  have e1 : y / 2 ^ (a + b) = y / 2 ^ b / 2 ^ a := by
    rw [Nat.div_div_eq_div_mul, pow_add, Nat.mul_comm]
  have e2 : y % 2 ^ (a + b) / 2 ^ b = y / 2 ^ b % 2 ^ a := by
    rw [pow_add, Nat.mul_comm, Nat.mod_mul_right_div_self]
  have e3 : y % 2 ^ (a + b) % 2 ^ b = y % 2 ^ b :=
    Nat.mod_mod_of_dvd y (pow_dvd_pow 2 (Nat.le_add_left b a))
  have hdm := Nat.div_add_mod (y / 2 ^ b) (2 ^ a)
  have hm := Nat.mod_lt (y / 2 ^ b) hA
  unfold blk
  beta_reduce
  rw [e1, e2, e3]
  by_cases h : y / 2 ^ b / 2 ^ a = n
  · have c : n * 2 ^ a = 2 ^ a * n := Nat.mul_comm _ _
    rw [if_pos h]
    by_cases hr : y / 2 ^ b % 2 ^ a < R
    · rw [if_pos hr, Finset.sum_eq_single (y / 2 ^ b % 2 ^ a)]
      · rw [if_pos (by rw [h] at hdm; omega)]
      · intro e _ he
        rw [if_neg (by rw [h] at hdm; omega)]
      · intro hc
        exact absurd (mem_range.mpr hr) hc
    · rw [if_neg hr]
      refine sum_eq_zero fun e he => ?_
      have := mem_range.mp he
      rw [if_neg (by rw [h] at hdm; omega)]
  · rw [if_neg h]
    refine sum_eq_zero fun e he => ?_
    have he' := mem_range.mp he
    rw [if_neg]
    intro hc
    apply h
    rw [hc, Nat.add_comm, Nat.add_mul_div_right _ _ hA, Nat.div_eq_of_lt (by omega), Nat.zero_add]

section Pans
variable (D : Dim)

/-- A panel begins at a multiple of its size. -/
theorem off_dvd (p : Pan) : 2 ^ p.wid D ∣ offP D p := by
  rw [offP_eq]
  refine List.dvd_sum fun x hx => ?_
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
  by_cases h : before D q p
  · rw [if_pos h]
    refine pow_dvd_pow 2 ?_
    unfold before at h
    omega
  · rw [if_neg h]
    exact dvd_zero _

/-- The number of a panel's block. -/
def nP (p : Pan) : ℕ := offP D p / 2 ^ p.wid D

theorem nP_mul (p : Pan) : nP D p * 2 ^ p.wid D = offP D p :=
  Nat.div_mul_cancel (off_dvd D p)

/-- A vector on the panel's block is 0 outside the panel's stretch. -/
theorem pan_out (p : Pan) (V : ℕ → E) (y : ℕ) (h : ¬ inStretch D p y) :
    blk (p.wid D) (nP D p) V y = 0 := by
  rw [blk_eq, nP_mul]
  exact if_neg h

/-- A function of row and column as a vector on the panel's block. -/
def cellOf (p : Pan) (F : ℕ → ℕ → E) (t : ℕ) : E :=
  if t / 2 ^ p.wcol D < p.nr D ∧ t % 2 ^ p.wcol D < p.nc D then
    F (t / 2 ^ p.wcol D) (t % 2 ^ p.wcol D) else 0

/-- The inner product on a block of any vector with a function of row and column. -/
theorem local_sum (p : Pan) (V : ℕ → E) (G : ℕ → ℕ → E) :
    ∑ t ∈ range (2 ^ p.wid D), V t * cellOf D p G t =
      ∑ ρ ∈ range (p.nr D), ∑ ι ∈ range (p.nc D), V (ρ * 2 ^ p.wcol D + ι) * G ρ ι := by
  have hr : p.nr D ≤ 2 ^ Nat.clog 2 (p.nr D) := Nat.le_pow_clog (by decide) _
  have hc : p.nc D ≤ 2 ^ p.wcol D := Nat.le_pow_clog (by decide) _
  have hw : p.wid D = Nat.clog 2 (p.nr D) + p.wcol D := rfl
  rw [hw, pow_add, Alg.sum_range_mul_add,
    ← sum_corner hr hc fun ρ ι => V (ρ * 2 ^ p.wcol D + ι) * G ρ ι]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b hb => ?_
  have hb' : b < 2 ^ p.wcol D := mem_range.mp hb
  unfold cellOf
  rw [div_at _ a hb', mod_at _ a hb']
  by_cases h : a < p.nr D ∧ b < p.nc D
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

/-- For two families of vectors on the panels' blocks, the inner product of the two long vectors is
the sum over the panels of the inner products on the blocks. -/
theorem pans_sum (VA VB : Pan → ℕ → E) :
    ∑ y ∈ range (2 ^ lamS D),
        ((pans D).map fun p => blk (p.wid D) (nP D p) (VA p) y).sum *
          ((pans D).map fun p => blk (p.wid D) (nP D p) (VB p) y).sum =
      ((pans D).map fun p => ∑ t ∈ range (2 ^ p.wid D), VA p t * VB p t).sum := by
  rw [sum_apart (2 ^ lamS D) _ _ (inStretch D) (fun p y h => pan_out D p _ y h)
    (fun p y h => pan_out D p _ y h) (pans D) (pans_apart D)]
  refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
  exact blk_mul_sum (by rw [nP_mul]; exact off_inside D hp) _ _

end Pans

end Cb.Pv.Lay.At

#print axioms Cb.Pv.Lay.At.rows_blk
#print axioms Cb.Pv.Lay.At.local_sum
#print axioms Cb.Pv.Lay.At.pans_sum
