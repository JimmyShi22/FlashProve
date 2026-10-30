-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/WeightsMeet.lean: the verifier's tables of weights of a long table's entries (hiTab,
OnBytes/Model/Tensors.lean) read as the library's equality weights, at any point r that agrees with
the reading of the verifier's point on the coordinates in front of the last la.

The dictionary FrontDict (Johnson/Road/K4/ValuesOfClaims.lean) asks this of three tables (its fields
sqW, g5W, g6W), each at the index that the verifier computes from a row's number, a stride and a
block's number. Here these three clauses are concluded from sizes and from the tie of the points.

Main names:
  `hiTab_meet`: one entry of the table.
  `hiTab_rows`: the entry at row * stride + block, where the stride is 2^b: it is the weight of the
    number row * 2^b + block.
  `hiTab_flat`: the entry at x / blocks * stride + x % blocks, where stride = blocks: it is the
    weight of x.
Limits. The tie of the points (hr) and the sizes are premises. Identities on public numbers: nothing
on a world, on a draw, on soundness or on hiding.


-/
import Johnson.Road.HeadEnds
import Johnson.Road.FormsKeysPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes.Model (Reading hiTab)
open Blocks (eqN)

variable {K : Type} [Field K] {ρ : Reading K}

/-- One entry of the table of weights. -/
theorem hiTab_meet {z e : Array E} {la want : ℕ} (h : (hiTab z la want).toOption = some e)
    {r : ℕ → K} (hr : ∀ j, j < want → pt ρ z j = r j) {x : ℕ} (hx : x < 2 ^ want) :
    ρ.val (e.getD x zeroE) = eqN want 0 r x := by
  obtain ⟨h1, h2, rfl⟩ := Hd.hiTab_ok (ok_of_toOption h)
  have hs : (z.extract 0 (z.size - la)).size = want := by
    rw [Array.size_extract]
    omega
  rw [eqTab_value (ρ := ρ) _ x (by rw [hs]; exact hx), hs]
  refine eqN_congr' _ _ (fun j hj => ?_) x
  rw [Nat.zero_add, ← hr j hj]
  unfold pt
  congr 1
  have hj' : j < z.size - la := by rw [h2]; exact hj
  have hz : j < z.size := by omega
  simp [Array.getD, hj', hz]

/-- The entry at row * stride + block, where the stride is 2^b. -/
theorem hiTab_rows {z e : Array E} {la a b stride : ℕ}
    (h : (hiTab z la (a + b)).toOption = some e) {r : ℕ → K}
    (hr : ∀ j, j < a + b → pt ρ z j = r j) (hs : stride = 2 ^ b) {i kh : ℕ} (hi : i < 2 ^ a)
    (hk : kh < 2 ^ b) :
    ρ.val (e.getD (i * stride + kh) zeroE) = eqN (a + b) 0 r (i * 2 ^ b + kh) := by
  rw [hs]
  refine hiTab_meet h hr ?_
  rw [Nat.pow_add]
  calc i * 2 ^ b + kh < i * 2 ^ b + 2 ^ b := Nat.add_lt_add_left hk _
    _ = (i + 1) * 2 ^ b := by ring
    _ ≤ 2 ^ a * 2 ^ b := Nat.mul_le_mul_right _ hi

/-- The entry at x / blocks * stride + x % blocks, where stride = blocks. -/
theorem hiTab_flat {z e : Array E} {la want blocks stride : ℕ}
    (h : (hiTab z la want).toOption = some e) {r : ℕ → K}
    (hr : ∀ j, j < want → pt ρ z j = r j) (hs : stride = blocks) {x : ℕ} (hx : x < 2 ^ want) :
    ρ.val (e.getD (x / blocks * stride + x % blocks) zeroE) = eqN want 0 r x := by
  rw [hs, Nat.div_add_mod']
  exact hiTab_meet h hr hx

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.hiTab_meet
#print axioms OnBytes.Road.K4.hiTab_rows
#print axioms OnBytes.Road.K4.hiTab_flat
