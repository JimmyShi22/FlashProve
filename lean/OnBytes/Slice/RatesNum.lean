-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RatesNum.lean: an error count of a written round against a power of one half, by one
comparison of natural numbers.

OnBytes/Slice/Rates.lean takes a share of bad typed values to a share of bad written verifier
messages. The second share has three factors: the bias of the format's sampler, which is
(1 + 2^-128) to the number of the round's hash blocks; the first share; and one half to the number
of the round's test bits. This file writes all three as ratios of natural numbers, so that "the
share is at most 2^-k" follows from one inequality between natural numbers.

Main theorems.
 `kap_pow`     the bias as a ratio.
 `rate_pow`    the three factors together are at most 2^-k.
 `entry_pow`   the clause on one round's error count: it is at most 2^-k times the number of the
               round's written verifier messages.
 `lin_le`      an inequality a * q + b ≤ c * q with a ≤ c that holds at Q holds from Q on.

Not claimed here: any number.
-/
import OnBytes.Slice.Rates

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Run
open scoped ENNReal

/-- A ratio of natural numbers is at most another if the cross products say so. -/
theorem nat_div_le (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    (a : ℝ≥0∞) / (b : ℝ≥0∞) ≤ (c : ℝ≥0∞) / (d : ℝ≥0∞) := by
  have hb0 : (b : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  have hbt : (b : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top b
  rw [ENNReal.div_le_iff hb0 hbt]
  exact share_le a c d b hd h

/-- The product of two ratios of natural numbers. -/
theorem nat_div_mul (a b c d : ℕ) (hb : 0 < b) :
    (a : ℝ≥0∞) / (b : ℝ≥0∞) * ((c : ℝ≥0∞) / (d : ℝ≥0∞)) =
      ((a * c : ℕ) : ℝ≥0∞) / ((b * d : ℕ) : ℝ≥0∞) := by
  have hb0 : (b : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  have hbt : (b : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top b
  rw [Nat.cast_mul, Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl hb0) (Or.inl hbt)]
  ring

/-- The bias of one hash block, as a ratio. -/
theorem kapSl_ratio : kapSl 128 = ((2 ^ 128 + 1 : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞) := by
  have h0 : ((2 ^ 128 : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  have ht : ((2 ^ 128 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [Nat.cast_add, Nat.cast_one, ENNReal.add_div, ENNReal.div_self h0 ht, one_div]
  unfold kapSl
  rw [Nat.cast_pow, Nat.cast_ofNat]

/-- The bias of B hash blocks, as a ratio. -/
theorem kap_pow (B : ℕ) : kapSl 128 ^ B =
    (((2 ^ 128 + 1) ^ B : ℕ) : ℝ≥0∞) / (((2 ^ 128) ^ B : ℕ) : ℝ≥0∞) := by
  rw [kapSl_ratio, div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← div_eq_mul_inv, ← Nat.cast_pow,
    ← Nat.cast_pow]

/-- The bias of B blocks, times a share n / D, divided by two to the number W of test bits, is at
most 2^-k, by one comparison of natural numbers. -/
theorem rate_pow (B n D W k : ℕ) (hD : 0 < D)
    (h : (2 ^ 128 + 1) ^ B * n * 2 ^ k ≤ (2 ^ 128) ^ B * D * 2 ^ W) :
    kapSl 128 ^ B * ((n : ℝ≥0∞) / (D : ℝ≥0∞) / 2 ^ W) ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
  have e1 : (n : ℝ≥0∞) / (D : ℝ≥0∞) / 2 ^ W =
      (n : ℝ≥0∞) / (D : ℝ≥0∞) * (((1 : ℕ) : ℝ≥0∞) / ((2 ^ W : ℕ) : ℝ≥0∞)) := by
    rw [Nat.cast_one, one_div, Nat.cast_pow, Nat.cast_ofNat, ← div_eq_mul_inv]
  have e2 : (2 : ℝ≥0∞)⁻¹ ^ k = ((1 : ℕ) : ℝ≥0∞) / ((2 ^ k : ℕ) : ℝ≥0∞) := by
    rw [Nat.cast_one, one_div, Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]
  rw [e1, e2, kap_pow, nat_div_mul n D 1 (2 ^ W) hD,
    nat_div_mul _ _ _ _ (by positivity)]
  refine nat_div_le _ _ _ _ (by positivity) (by positivity) ?_
  calc (2 ^ 128 + 1) ^ B * (n * 1) * 2 ^ k = (2 ^ 128 + 1) ^ B * n * 2 ^ k := by ring
    _ ≤ (2 ^ 128) ^ B * D * 2 ^ W := h
    _ = 1 * ((2 ^ 128) ^ B * (D * 2 ^ W)) := by ring

/-- The clause on one round's error count, at 2^-k: e * w is at most 2^-k times the number of the
round's written verifier messages. e: the count among the typed values. w: the sampler's bound on
how many written messages go to one typed value. n / D: a share that bounds e. B, W: the round's
numbers of hash blocks and of test bits. -/
theorem entry_pow (d : PQ.RD) (hlog : d.entry.logN ≤ 64) (e n D B W k : ℕ)
    (hb : (bsRound .two d.entry d.kind).b = B) (hw : d.entry.work = W) (hD : 0 < D)
    (h : e * D ≤ n * nVals (Fmt.dsOf d.entry d.kind))
    (hnum : (2 ^ 128 + 1) ^ B * n * 2 ^ k ≤ (2 ^ 128) ^ B * D * 2 ^ W) :
    ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
      (2 : ℝ≥0∞)⁻¹ ^ k * (Fintype.card (wRound d).Chal : ℝ≥0∞) := by
  have h' : e * D ≤ n * Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) := by
    rw [card_vals_all]
    exact h
  refine (below_round_div d hlog e _ (share_le e n D _ hD h')).trans (mul_le_mul' ?_ le_rfl)
  rw [hb, hw]
  exact rate_pow B n D W k hD hnum

/-- An inequality a * q + b ≤ c * q with a ≤ c that holds at Q holds from Q on. -/
theorem lin_le (a b c Q q : ℕ) (hac : a ≤ c) (hq : Q ≤ q) (h : a * Q + b ≤ c * Q) :
    a * q + b ≤ c * q := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hq
  have h2 : a * r ≤ c * r := Nat.mul_le_mul_right r hac
  calc a * (Q + r) + b = a * Q + b + a * r := by ring
    _ ≤ c * Q + c * r := Nat.add_le_add h h2
    _ = c * (Q + r) := by ring

end OnBytes.Slice

#print axioms OnBytes.Slice.rate_pow
#print axioms OnBytes.Slice.entry_pow
#print axioms OnBytes.Slice.lin_le
