-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndClaimsB.lean: the vectors of which the ties' and reads' weights are made,
read in a commutative ring: powers, sums, and the left and right weights of a tie.

Statements and proofs.
Main names:
  `powers_val`, `powers_size`: entry i of powers x n reads as x ^ i.
  `sumE_val`: the sum of a vector. `runSum_eq_sum`: runSum as a sum over a range.
  `val_radixPower`, `tieLeft_one`, `tieRight_one`: the weights of a tie where an array's row
    holds one row of symbols (J = 1).
Limits: J = 1 only, which powersF tests.

-/
import OnBytes.Tie.Pv.Tail.EndClaims
import OnBytes.Iop.RowLaws
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

theorem getD_map_range {α : Type} (f : Nat → α) (n i : Nat) (d : α) (h : i < n) :
    ((Array.range n).map f).getD i d = f i := by
  simp [Array.getD, h]

/-! ## Powers, sums, and the weights of a tie where a row holds one row of symbols -/

theorem powersLoop_size (x : E) : ∀ (n : Nat) (c : E) (a : Array E),
    (powersLoop x n c a).size = a.size + n
  | 0, _, _ => rfl
  | n + 1, c, a => by
    rw [powersLoop, powersLoop_size x n, Array.size_push]
    omega

theorem powersLoop_old (x : E) : ∀ (n : Nat) (c : E) (a : Array E) (j : Nat), j < a.size →
    (powersLoop x n c a).getD j zeroE = a.getD j zeroE
  | 0, _, _, _, _ => rfl
  | n + 1, c, a, j, h => by
    rw [powersLoop, powersLoop_old x n _ _ j (by rw [Array.size_push]; omega)]
    simp [Array.getD, Array.getElem_push, h, Nat.lt_succ_of_lt h]

theorem powersLoop_val (x : E) : ∀ (n : Nat) (c : E) (a : Array E) (i : Nat), i < n →
    ρ.val ((powersLoop x n c a).getD (a.size + i) zeroE) = ρ.val c * ρ.val x ^ i
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, c, a, 0, _ => by
    rw [powersLoop, Nat.add_zero, powersLoop_old x n _ _ a.size (by rw [Array.size_push]; omega)]
    simp [Array.getD]
  | n + 1, c, a, i + 1, h => by
    have e : a.size + (i + 1) = (a.push c).size + i := by rw [Array.size_push]; omega
    rw [powersLoop, e, powersLoop_val x n _ _ i (by omega), ρ.mul]
    ring

/-- Entry i of Model.powers x n reads as x^i. With it: vp[u], vt[u] = theta^u, rowX[mu][i] =
theta^(stepF i). -/
theorem powers_val (x : E) (n i : Nat) (h : i < n) :
    ρ.val ((powers x n).getD i zeroE) = ρ.val x ^ i := by
  have := powersLoop_val ρ x n oneE (Array.emptyWithCapacity n) i h
  simpa [powers, ρ.one] using this

theorem powers_size (x : E) (n : Nat) : (powers x n).size = n := by
  simp [powers, powersLoop_size]

theorem sumE_val (v : Array E) : ρ.val (sumE v) = (v.toList.map ρ.val).sum := by
  unfold sumE
  rw [← Array.foldl_toList, foldl_adds ρ.val addE ρ.val (fun r p => ρ.add r p), ρ.zero, zero_add]

/-- runSum (OnBytes/Model/HideLaws.lean) as a sum over a range. -/
theorem runSum_eq_sum (h : Nat → K) : ∀ (n i : Nat), runSum h n i = ∑ j ∈ Finset.range n, h (i + j)
  | 0, _ => by simp [runSum]
  | n + 1, i => by
    rw [runSum, runSum_eq_sum h n (i + 1), Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    omega

theorem val_radixPower (l : Nat) (hl : l < 3) :
    ρ.val (ofF (radixPower l)) = ((2 : K) ^ 20) ^ l := by
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
  · rw [show ofF (radixPower 0) = oneE by decide +kernel, ρ.one, pow_zero]
  · rw [show ofF (radixPower 1) = powE (addE oneE oneE) 20 by decide +kernel, ρ.pow, ρ.add, ρ.one,
      one_add_one_eq_two, pow_one]
  · rw [show ofF (radixPower 2) = powE (addE oneE oneE) 40 by decide +kernel, ρ.pow, ρ.add, ρ.one,
      one_add_one_eq_two, ← pow_mul]

theorem tieLeft_one (s : ShP) (rows lo wl : Array E) (hJ : s.J = 1)
    (h : tieLeft s rows lo = some wl) (i : Nat) (hi : i < s.m) :
    ρ.val (wl.getD i zeroE) = ((2 : K) ^ 20) ^ (i % 3)
      * (ρ.val (rows.getD (i / 3) zeroE) * ρ.val (lo.getD 0 zeroE)) := by
  unfold tieLeft at h
  split at h
  · cases h
  · have e := Option.some.inj h
    subst e
    rw [getD_map_range _ _ _ _ hi]
    simp only [lanes, hJ, Nat.div_one, Nat.mod_one]
    rw [OnBytes.scaleE_val ρ, val_radixPower ρ _ (Nat.mod_lt _ (by decide)), ρ.mul]

theorem tieRight_one (s : ShP) (lo gam wr : Array E) (hJ : s.J = 1)
    (h : tieRight s lo gam = some wr) (p : Nat) (hp : p < s.k) :
    ρ.val (wr.getD p zeroE) = ρ.val (gam.getD p zeroE) * ρ.val (lo.getD 0 zeroE) := by
  unfold tieRight at h
  split at h
  · cases h
  · have e := Option.some.inj h
    subst e
    rw [getD_map_range _ _ _ _ (by rw [hJ]; omega)]
    simp only [hJ, Nat.div_one, Nat.mod_one]
    rw [ρ.mul]

end OnBytes.Tie.Pv.Tail.Port
