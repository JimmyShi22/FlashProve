-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cond/LifeTail.lean: a bound for the overrun term at few leaves. The chance that one given leaf of m
≥ 2 gets more than s of n sessions (`binTail n m s`, Compile/Spec.lean: an exact finite sum) is at
most 2^-e as soon as, for some number a, n ≤ 5 a and 3 a + e ≤ s + 1.

In standard terms: a tail bound for the binomial distribution: `binTail n m s` is
Pr[Bin(n, 1/m) > s]. A leaf is a further encoded index; a session is one call of the prover.
Statements and proofs: arithmetic. No protocol occurs. Nothing is assumed beyond
the hypotheses of the statements and whatever the arguments hold as proofs. Many statements of this
library are written twice: a definition in the namespace `Spec` states a proposition, and a theorem
of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: another bound of the library (`binTail_le_half_pow`, CompileK/CountsOverrun.lean) asks 2 n² ≤
(e + 1) m²: it serves at hundreds of thousands of leaves and says nothing at two (there it asks n² ≤
2 (e + 1)).

Main names:
  `Spec.life_tailSum`: if 1 ≤ m, then 2^(s+1) · Σ_{s < j ≤ n} C(n, j) (m - 1)^(n - j) ≤ (m + 1)^n
    (each summand is weighted by 2^j ≥ 2^(s+1); the binomial theorem at 2 + (m - 1)).
  `Spec.life_tail`: the bound told at the top (by `life_tailSum`; (m + 1) / m ≤ 3 / 2 for m ≥ 2;
    3^5 ≤ 2^8: so ((m + 1) / m)^n ≤ 2^(3 a)).
    In words: with n sessions thrown on at least two leaves, a given leaf gets no more than about
    0.6 n + e of them, except with probability at most 2^-e.

Limits: the bound is for one given leaf. That no leaf gets more than s sessions costs the factor m:
m · 2^-e.

The bound is coarse: the true threshold at two leaves is near n / 2. It is enough
where s is near two thirds of n. At one leaf it is false and not claimed: there binTail n 1 s = 1
for n > s. This file says nothing on a scheme. No number.

Terms: lean/GLOSSARY.md.
-/
import Cond.LifeMono

set_option autoImplicit false

namespace TopC
open Compile
open scoped ENNReal

namespace Spec

def life_tailSum : Prop :=
  ∀ n m s : ℕ,
    1 ≤ m → 2 ^ (s + 1) * (∑ j ∈ Finset.Icc (s + 1) n, n.choose j * (m - 1) ^ (n - j)) ≤ (m + 1) ^ n

/-- The overrun's tail at two leaves or more. -/
def life_tail : Prop :=
  ∀ n m s a e : ℕ, 2 ≤ m → n ≤ 5 * a → 3 * a + e ≤ s + 1 → binTail n m s ≤ ((2 : ℝ≥0∞) ^ e)⁻¹

end Spec

theorem life_tailSum : Spec.life_tailSum := by
  intro n m s hm
  have h1 : ∀ j ∈ Finset.Icc (s + 1) n,
      2 ^ (s + 1) * (n.choose j * (m - 1) ^ (n - j)) ≤ 2 ^ j * (m - 1) ^ (n - j) * n.choose j := by
    intro j hj
    calc
      2 ^ (s + 1) * (n.choose j * (m - 1) ^ (n - j)) ≤ 2 ^ j * (n.choose j * (m - 1) ^ (n - j)) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (Finset.mem_Icc.1 hj).1)
      _ = 2 ^ j * (m - 1) ^ (n - j) * n.choose j := by ring
  calc
    2 ^ (s + 1) * (∑ j ∈ Finset.Icc (s + 1) n, n.choose j * (m - 1) ^ (n - j)) =
        ∑ j ∈ Finset.Icc (s + 1) n, 2 ^ (s + 1) * (n.choose j * (m - 1) ^ (n - j)) :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Finset.Icc (s + 1) n, 2 ^ j * (m - 1) ^ (n - j) * n.choose j := Finset.sum_le_sum h1
    _ ≤ ∑ j ∈ Finset.range (n + 1), 2 ^ j * (m - 1) ^ (n - j) * n.choose j :=
        Finset.sum_le_sum_of_subset fun j hj =>
          Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2)
    _ = (2 + (m - 1)) ^ n := by rw [add_pow]; simp only [Nat.cast_id]
    _ = (m + 1) ^ n := by congr 1; omega

/-- The tail as one fraction. -/
theorem life_tailEq (n m s : ℕ) :
    binTail n m s =
      ((∑ j ∈ Finset.Icc (s + 1) n, n.choose j * (m - 1) ^ (n - j) : ℕ) : ℝ≥0∞) /
        (m : ℝ≥0∞) ^ n := by
  unfold binTail
  rw [Nat.cast_sum]
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.cast_mul, Nat.cast_pow]

theorem life_tail : Spec.life_tail := by
  intro n m s a e hm hn he
  rw [life_tailEq]
  generalize hS : (∑ j ∈ Finset.Icc (s + 1) n, n.choose j * (m - 1) ^ (n - j)) = S
  have h0 : 2 ^ (s + 1) * S ≤ (m + 1) ^ n := hS ▸ life_tailSum n m s (by omega)
  have h1 : (m + 1) ^ n * 2 ^ n ≤ 3 ^ n * m ^ n := by
    rw [← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (by omega) n
  have h2 : 3 ^ n * 2 ^ (5 * a - n) ≤ 2 ^ (8 * a) := by
    calc
      3 ^ n * 2 ^ (5 * a - n) ≤ 3 ^ n * 3 ^ (5 * a - n) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by norm_num) _)
      _ = 3 ^ (5 * a) := by rw [← pow_add]; congr 1; omega
      _ = (3 ^ 5) ^ a := pow_mul 3 5 a
      _ ≤ (2 ^ 8) ^ a := Nat.pow_le_pow_left (by norm_num) a
      _ = 2 ^ (8 * a) := (pow_mul 2 8 a).symm
  have h3 : 2 ^ (8 * a) * (S * 2 ^ e) ≤ 2 ^ (8 * a) * m ^ n := by
    calc 2 ^ (8 * a) * (S * 2 ^ e) = 2 ^ (e + 8 * a) * S := by rw [pow_add]; ring
      _ ≤ 2 ^ ((s + 1) + n + (5 * a - n)) * S :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ = (2 ^ (s + 1) * S) * 2 ^ n * 2 ^ (5 * a - n) := by rw [pow_add, pow_add]; ring
      _ ≤ (m + 1) ^ n * 2 ^ n * 2 ^ (5 * a - n) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h0)
      _ ≤ 3 ^ n * m ^ n * 2 ^ (5 * a - n) := Nat.mul_le_mul_right _ h1
      _ = (3 ^ n * 2 ^ (5 * a - n)) * m ^ n := by ring
      _ ≤ 2 ^ (8 * a) * m ^ n := Nat.mul_le_mul_right _ h2
  have h4 : S * 2 ^ e ≤ m ^ n := Nat.le_of_mul_le_mul_left h3 (pow_pos (by norm_num) _)
  have h5 : (S : ℝ≥0∞) * 2 ^ e ≤ (m : ℝ≥0∞) ^ n := by exact_mod_cast h4
  have hm0 : (m : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hmT : (m : ℝ≥0∞) ^ n ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top m)
  rw [ENNReal.div_le_iff hm0 hmT]
  calc (S : ℝ≥0∞) = ((S : ℝ≥0∞) * 2 ^ e) * ((2 : ℝ≥0∞) ^ e)⁻¹ := by
        rw [mul_assoc,
          ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero)
            (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), mul_one]
    _ ≤ (m : ℝ≥0∞) ^ n * ((2 : ℝ≥0∞) ^ e)⁻¹ := mul_le_mul' h5 le_rfl
    _ = ((2 : ℝ≥0∞) ^ e)⁻¹ * (m : ℝ≥0∞) ^ n := mul_comm _ _

end TopC
