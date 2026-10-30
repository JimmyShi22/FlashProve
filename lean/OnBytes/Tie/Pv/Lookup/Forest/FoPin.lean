-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPin.lean.
The row that sums the counts of a sub-proof's lookup, in the verifier's own form.

The flat function's row `TwV.rowNum` lists, for every row u of the joined table and every plane
j, the place of bit j of u's count with the weight 2^j; its target is the number of
keys that are not padding. The verifier adds up, over the columns of the planes' matrix, the
caller's sums over the rows with the weight 2^(row mod 32), from minus that number on.
This file states that the two are one claim, under every reading of the places that reads the place
that is no cell as 0. All is stated over a commutative ring K, on plain data.

Main names:
  `pinColK lm μ col`: the caller's sum for column col: over the 2^lm rows, 2^(row mod 32) times the
  entry.
  `countK h lm pin`: the verifier's third claim on the planes, as a value: minus (2^v - padding),
  plus the columns' sums.
  `pin_sum`: the value of the row's form is the sum of the columns' sums. Hypotheses on public
    numbers alone: NC ≤ 2^cK, 5 ≤ lm ≤ kT + 5.
  `rowNum_iff`: at a lawful shape, under the same bounds on lm, for a reading that reads the place
    that is no cell as 0, the row holds if and only if `countK` of the sums `pinColK` is 0.

Limits: that `pinColK` and `countK` are the verifier's functions on its own field elements is not
  stated here. Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPadFac
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneRows

set_option autoImplicit false

namespace Cb.Fo.Pin
open TwV Cb.Fo Finset _root_.Fo

section
variable {K : Type} [CommRing K]

/-- The caller's sum for a column. -/
def pinColK (lm : ℕ) (μ : Pl → K) (col : ℕ) : K :=
  ∑ row ∈ range (2 ^ lm), (2 : K) ^ (row % 32) * μ (.cell row col)

/-- The verifier's claim that the counts sum to the number of keys that are not padding, as a value.
-/
def countK (h : Sh) (lm : ℕ) (pin : ℕ → K) : K :=
  (List.range (h.NC * 2 ^ (h.kT + 5 - lm))).foldl (fun f col => f + pin col)
      (-((2 ^ h.v - h.padding : ℕ) : K))

theorem foldl_add_from (g : ℕ → K) : ∀ (n : ℕ) (a : K),
    (List.range n).foldl (fun f x => f + g x) a = a + ∑ x ∈ range n, g x
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range_succ, List.foldl_append, foldl_add_from g n a, sum_range_succ, ← add_assoc]
    rfl

theorem valS_flatMap {P : Type} (F : ℕ → List (P × K)) (μ : P → K) : ∀ n : ℕ,
    valS ((List.range n).flatMap F) μ = ∑ u ∈ range n, valS (F u) μ
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, valS_append, valS_flatMap F μ n, sum_range_succ]
    simp

/-- **The form of the row that sums the counts, by columns.** -/
theorem pin_sum (h : Sh) (lm jLK : ℕ) (θ : K) (μ : Pl → K) (h0 : μ .zero = 0)
    (hNC : h.NC ≤ 2 ^ h.cK)
    (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) :
    valS (rowNum (numsF h lm jLK θ)).cf μ = ∑ col ∈ range (h.NC * 2 ^ (h.kT + 5 - lm)),
        pinColK lm μ col := by
  -- the left side, by (t, c, j)
  have hL : valS (rowNum (numsF h lm jLK θ)).cf μ =
      ∑ u ∈ range (2 ^ h.cK * 2 ^ h.kT), ∑ j ∈ range 32, (2 : K) ^ j *
        (if u % 2 ^ h.cK < h.NC then
          μ (.cell (2 ^ 5 * (u / 2 ^ h.cK % 2 ^ (lm - 5)) + j)
            (2 ^ (h.kT + 5 - lm) * (u % 2 ^ h.cK) + u / 2 ^ h.cK / 2 ^ (lm - 5)))
        else 0) := by
    show valS ((List.range (2 ^ (h.kT + h.cK))).flatMap fun u =>
      (List.range 32).map fun j => ((numsF h lm jLK θ).bAt u j, (2 : K) ^ j)) μ = _
    rw [valS_flatMap, pow_add, Nat.mul_comm]
    refine sum_congr rfl fun u _ => ?_
    unfold valS
    rw [List.map_map, lsum]
    refine sum_congr rfl fun j _ => ?_
    show (2 : K) ^ j * μ ((numsF h lm jLK θ).bAt u j) = _
    rw [bAt_val h lm jLK θ μ h0]
  have hpos : ∀ n : ℕ, 0 < 2 ^ n := fun n => Nat.pos_of_ne_zero (by positivity)
  rw [hL, _root_.Fo.sum_mul, sum_comm, ← sum_subset (range_subset_range.2 hNC), Nat.mul_comm h.NC,
      _root_.Fo.sum_mul]
  · refine sum_congr rfl fun c hc => ?_
    have hc' : c < h.NC := mem_range.mp hc
    have hc2 : c < 2 ^ h.cK := lt_of_lt_of_le hc' hNC
    have e1 : ∀ t, (2 ^ h.cK * t + c) % 2 ^ h.cK = c := fun t => by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc2]
    have e2 : ∀ t, (2 ^ h.cK * t + c) / 2 ^ h.cK = t := fun t => by
      rw [Nat.mul_add_div (hpos _), Nat.div_eq_of_lt hc2, Nat.add_zero]
    simp only [e1, e2, if_pos hc']
    rw [show 2 ^ h.kT = 2 ^ (lm - 5) * 2 ^ (h.kT + 5 - lm) by
        rw [← pow_add]; congr 1; omega, _root_.Fo.sum_mul]
    refine sum_congr rfl fun b _ => ?_
    unfold pinColK
    rw [show 2 ^ lm = 2 ^ 5 * 2 ^ (lm - 5) by rw [← pow_add]; congr 1; omega, _root_.Fo.sum_mul]
    refine sum_congr rfl fun a ha => sum_congr rfl fun j hj => ?_
    have ha' : a < 2 ^ (lm - 5) := mem_range.mp ha
    have hj' : j < 32 := mem_range.mp hj
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ha', Nat.mul_add_div (hpos _), Nat.div_eq_of_lt ha',
      show (2 ^ 5 * a + j) % 32 = j by omega]
    rfl
  · intro c _ hc
    have hc' : ¬ c < h.NC := fun hh => hc (mem_range.mpr hh)
    refine sum_eq_zero fun t _ => sum_eq_zero fun j _ => ?_
    by_cases hc2 : c < 2 ^ h.cK
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc2, if_neg hc', mul_zero]
    · exact absurd (mem_range.mp ‹c ∈ range (2 ^ h.cK)›) hc2

/-- **The row that sums the counts holds if and only if the verifier's claim is 0.** -/
theorem rowNum_iff (h : Sh) (H : FoNums.ok h = true) (lm jLK : ℕ) (h5 : 5 ≤ lm)
    (hlm : lm ≤ h.kT + 5) (θ : K)
    (μ : Pl → K) (h0 : μ .zero = 0) :
    SRowHolds (rowNum (numsF h lm jLK θ)) μ ↔ countK h lm (pinColK lm μ) = 0 := by
  unfold SRowHolds countK
  rw [pin_sum h lm jLK θ μ h0 (ok_parts H).1.2.2.1 h5 hlm, PadFac.pin_target h H, foldl_add_from,
      neg_add_eq_zero, eq_comm]

end
end Cb.Fo.Pin
