-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ZetaArith.lean: arithmetic for the bound on the error term `OnBytes.WholeKey.zetaW`
(Johnson/WholeKey/Zeta.lean).

Summary. Lemmas on two library functions that occur in `zetaW` (`Prob.pOver`, Prob/Tail.lean;
`Rom.costTotal`, Rom/SpecHopCost.lean) and on natural numbers. No protocol, prover or file is named
here. The bound itself is in E2E/ZetaGeneral.lean, E2E/ZetaCaps.lean and E2E/ZetaAtCaps.lean.

Main results.
  `costTotal_le_of`: if each of at most k oracle names gets at most A queries with a secret and B
    without, and each secret has at least b bits, then `costTotal … t ≤ (t A + k A (B + A))
    / 2 ^ b`.
  `counts_le`: nine sums of products of M, n and nine numbers are at most `boundA M n`, if the nine
    numbers are at most 2 ^ 37, 2 ^ 25, 2 ^ 39 and six times 2 ^ 20.
  `numerator_caps`: for M = 0, n = 1, t ≤ 2 ^ 64 and CT, CL, CB ≤ 2 ^ 40: t A + (9 + CT + CL + CB) A
    (4 + A) ≤ 2 ^ 121 with A := `boundA 0 1`.

Terms: E2E/HidingTerms.lean.

Limits. Upper bounds, none proved to be tight. No security property is stated.

Definitions and helper lemmas.
  `boundA M n` := (M + 2) 2 ^ 32 + 2 ^ 37 + (M + 1) 2 ^ 25 + n 2 ^ 39; `boundA_eq`: the same in
    written numerals.
  `pOver_zero`: the overrun term is 0 if there are no more sessions than one copy serves.
  `div_pow_le`: a number of at most k bits divided by 2 ^ (k + j) is at most 2 ^ -j.
  `numerator_small`: `numerator_caps` without the three search limits: at most 2 ^ 105.


-/
import Rom.SpecHopCost
import Prob.Tail

set_option autoImplicit false

open scoped ENNReal

namespace AtPublicFiles.ZetaAt
open Rom Prob

/-- The overrun term is 0 if there are no more sessions than one copy serves. -/
theorem pOver_zero (M s n : ℕ) (h : n ≤ s) : pOver M s n = 0 := by
  unfold pOver binTail
  rw [hitTail_eq_zero (Nat.lt_succ_of_le h), mul_zero]

variable {S : OSpec}

/-- **The cost of the provers' hash queries, from bounds on the counts**: at most A queries with a
secret and B without at each of at most k oracle names, each secret of at least b bits. -/
theorem costTotal_le_of (e M ℓ : S.ι → ℕ) (os : Finset S.ι) (t A B b k : ℕ)
    (hM : ∀ o ∈ os, M o ≤ A) (he : ∀ o ∈ os, e o ≤ B) (hℓ : ∀ o ∈ os, b ≤ ℓ o)
    (hk : os.card ≤ k) :
    costTotal e M ℓ os t ≤ ((t * A + k * (A * (B + A)) : ℕ) : ℝ≥0∞) / 2 ^ b := by
  have hp : ∀ o ∈ os, (2 : ℝ≥0∞) ^ b ≤ 2 ^ ℓ o := fun o ho =>
    pow_le_pow_right₀ (by norm_num) (hℓ o ho)
  have h1 : os.sup (fun o => (M o : ℝ≥0∞) / 2 ^ ℓ o) ≤ (A : ℝ≥0∞) / 2 ^ b :=
    Finset.sup_le fun o ho => ENNReal.div_le_div (by exact_mod_cast hM o ho) (hp o ho)
  have h2 : ∑ o ∈ os, (M o : ℝ≥0∞) * (e o + M o : ℕ) / 2 ^ ℓ o ≤
      (k : ℝ≥0∞) * (((A * (B + A) : ℕ) : ℝ≥0∞) / 2 ^ b) := by
    calc ∑ o ∈ os, (M o : ℝ≥0∞) * (e o + M o : ℕ) / 2 ^ ℓ o
        ≤ ∑ _o ∈ os, ((A * (B + A) : ℕ) : ℝ≥0∞) / 2 ^ b := by
          refine Finset.sum_le_sum fun o ho => ENNReal.div_le_div ?_ (hp o ho)
          have : M o * (e o + M o) ≤ A * (B + A) :=
            Nat.mul_le_mul (hM o ho) (Nat.add_le_add (he o ho) (hM o ho))
          exact_mod_cast this
      _ = (os.card : ℝ≥0∞) * (((A * (B + A) : ℕ) : ℝ≥0∞) / 2 ^ b) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ≥0∞) * (((A * (B + A) : ℕ) : ℝ≥0∞) / 2 ^ b) := by
          gcongr
  unfold costTotal
  calc (t : ℝ≥0∞) * os.sup (fun o => (M o : ℝ≥0∞) / 2 ^ ℓ o) +
        ∑ o ∈ os, (M o : ℝ≥0∞) * (e o + M o : ℕ) / 2 ^ ℓ o
      ≤ (t : ℝ≥0∞) * ((A : ℝ≥0∞) / 2 ^ b) +
          (k : ℝ≥0∞) * (((A * (B + A) : ℕ) : ℝ≥0∞) / 2 ^ b) := by
        gcongr
    _ = ((t * A + k * (A * (B + A)) : ℕ) : ℝ≥0∞) / 2 ^ b := by
        rw [Nat.cast_add, Nat.cast_mul t A, Nat.cast_mul k (A * (B + A)), ENNReal.add_div,
          mul_div_assoc, mul_div_assoc]

/-- A natural number of at most k bits, over 2 ^ (k + j). -/
theorem div_pow_le (N k j : ℕ) (hN : N ≤ 2 ^ k) :
    ((N : ℕ) : ℝ≥0∞) / 2 ^ (k + j) ≤ (2⁻¹ : ℝ≥0∞) ^ j := by
  have h1 : ((N : ℕ) : ℝ≥0∞) ≤ 2 ^ k := by exact_mod_cast hN
  calc ((N : ℕ) : ℝ≥0∞) / 2 ^ (k + j) ≤ (2 : ℝ≥0∞) ^ k / 2 ^ (k + j) :=
        ENNReal.div_le_div_right h1 _
    _ = (2⁻¹ : ℝ≥0∞) ^ j := by
      rw [pow_add, ← ENNReal.inv_pow, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness)), ← mul_assoc,
        ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]

/-- The bound on the queries with a secret at one oracle name, for M + 1 copies and n sessions. -/
def boundA (M n : ℕ) : ℕ := (M + 2) * 2 ^ 32 + 2 ^ 37 + (M + 1) * 2 ^ 25 + n * 2 ^ 39

theorem boundA_eq (M n : ℕ) : boundA M n =
    (M + 2) * 4294967296 + 137438953472 + (M + 1) * 33554432 + n * 549755813888 := by
  unfold boundA
  norm_num

/-- **Nine counts are at most `boundA`**, from nine numbers: the leaves of three wirings, the rounds
of three protocols, the depths of three request trees. -/
theorem counts_le (M n lT lL lB r1 r2 r3 q1 q2 q3 : ℕ) (hT : lT ≤ 2 ^ 37) (hL : lL ≤ 2 ^ 25)
    (hB : lB ≤ 2 ^ 39) (h1 : r1 ≤ 2 ^ 20) (h2 : r2 ≤ 2 ^ 20) (h3 : r3 ≤ 2 ^ 20)
    (k1 : q1 ≤ 2 ^ 20) (k2 : q2 ≤ 2 ^ 20) (k3 : q3 ≤ 2 ^ 20) :
    (M + 2) * 2 ^ 32 + lT + (M + 1) * lL + n * lB ≤ boundA M n ∧
      1 + (M + 1) + n ≤ boundA M n ∧ q1 + (M + 1) * q2 + n * q3 ≤ boundA M n ∧
      1 ≤ boundA M n ∧ M + 1 ≤ boundA M n ∧ n ≤ boundA M n ∧ r1 ≤ boundA M n ∧
      (M + 1) * r2 ≤ boundA M n ∧ n * r3 ≤ boundA M n := by
  have hT' : lT ≤ 137438953472 := le_trans hT (by norm_num)
  have hL' : lL ≤ 33554432 := le_trans hL (by norm_num)
  have hB' : lB ≤ 549755813888 := le_trans hB (by norm_num)
  have h1' : r1 ≤ 1048576 := le_trans h1 (by norm_num)
  have h2' : r2 ≤ 1048576 := le_trans h2 (by norm_num)
  have h3' : r3 ≤ 1048576 := le_trans h3 (by norm_num)
  have k1' : q1 ≤ 1048576 := le_trans k1 (by norm_num)
  have k2' : q2 ≤ 1048576 := le_trans k2 (by norm_num)
  have k3' : q3 ≤ 1048576 := le_trans k3 (by norm_num)
  have a1 := Nat.mul_le_mul_left (M + 1) hL'
  have a2 := Nat.mul_le_mul_left n hB'
  have a3 := Nat.mul_le_mul_left (M + 1) h2'
  have a4 := Nat.mul_le_mul_left n h3'
  have a5 := Nat.mul_le_mul_left (M + 1) k2'
  have a6 := Nat.mul_le_mul_left n k3'
  have e32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  rw [boundA_eq, e32]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **At one copy, one session and at most 2 ^ 64 queries the numerator has at most 105 bits.** -/
theorem numerator_small (t : ℕ) (ht : t ≤ 2 ^ 64) :
    t * boundA 0 1 + 9 * (boundA 0 1 * (2 * (0 + 2) + boundA 0 1)) ≤ 2 ^ 105 := by
  have e : boundA 0 1 = 695818256384 := by rw [boundA_eq]
  rw [e]
  have ht' : t ≤ 18446744073709551616 := le_trans ht (by norm_num)
  have h := Nat.mul_le_mul_right 695818256384 ht'
  have p : (2 : ℕ) ^ 105 = 40564819207303340847894502572032 := by norm_num
  rw [p]
  linarith

/-- **The same with search limits of at most 2 ^ 40 in the three protocols: at most 121 bits.** -/
theorem numerator_caps (t CT CL CB : ℕ) (ht : t ≤ 2 ^ 64) (hT : CT ≤ 2 ^ 40) (hL : CL ≤ 2 ^ 40)
    (hB : CB ≤ 2 ^ 40) :
    t * boundA 0 1 + (9 + CT + CL + CB) * (boundA 0 1 * (2 * (0 + 2) + boundA 0 1)) ≤ 2 ^ 121 := by
  have e : boundA 0 1 = 695818256384 := by rw [boundA_eq]
  rw [e]
  have hK : 695818256384 * (2 * (0 + 2) + 695818256384) = 484163045920053229780992 := by norm_num
  rw [hK]
  have ht' : t ≤ 18446744073709551616 := le_trans ht (by norm_num)
  have hT' : CT ≤ 1099511627776 := le_trans hT (by norm_num)
  have hL' : CL ≤ 1099511627776 := le_trans hL (by norm_num)
  have hB' : CB ≤ 1099511627776 := le_trans hB (by norm_num)
  have hk : 9 + CT + CL + CB ≤ 3298534883337 := by linarith
  have h1 := Nat.mul_le_mul_right 695818256384 ht'
  have h2 := Nat.mul_le_mul_right 484163045920053229780992 hk
  have p : (2 : ℕ) ^ 121 = 2658455991569831745807614120560689152 := by norm_num
  rw [p]
  linarith

end AtPublicFiles.ZetaAt

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.ZetaAt.numerator_caps
#print axioms AtPublicFiles.ZetaAt.div_pow_le
#print axioms AtPublicFiles.ZetaAt.counts_le
#print axioms AtPublicFiles.ZetaAt.numerator_small
#print axioms AtPublicFiles.ZetaAt.pOver_zero
#print axioms AtPublicFiles.ZetaAt.costTotal_le_of
#print axioms AtPublicFiles.ZetaAt.boundA_eq
