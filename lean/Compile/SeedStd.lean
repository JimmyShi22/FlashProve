-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/SeedStd.lean: parts of a standard way to use the auxiliary oracle as a source of coins, for
every λ > 0.

An element of a set with M elements is obtained from m' separate bits by reduction modulo M, with
bias at most M / 2^(m' + 2), and with none if M is a power of two and m' ≥ log₂ M. `blocksStd` is
the case M = n + 1, m' = λ · m n. The bias of a reduction is `Prob.tv_natCast_fin_eq`,
`Prob.modBias_le` (Prob/Bias.lean). The oracle `OracleName.other` of Compile/Batch/Oracles.lean
takes a list of bits and answers with λ bits.

  `digNum`       λ bits as a number below 2^λ.
  `ptStd`        Seeds are the numbers below 2^λ; the query for the seed s and the counter j is the
                 λ bits of s followed by the binary digits of j (`pt_inj`: different pairs have
                 different queries).
  `blocksStd`    A small sample has 2^λ outcomes. A sample with exactly 2^λ outcomes is one small
                 sample. Any other sample with n + 1 outcomes is made from ⌊⌈log₂ (n + 1)⌉ / λ⌋ + 2
                 small ones, read as one number to the base 2^λ and reduced modulo n + 1.
  `bias_blocksStd_eq`, `bias_blocksStd_salt`, `bias_blocksStd_le`
                 The bias of a sample is that of the reduction; 0 for a sample with exactly 2^λ
                 outcomes; at most 2^-λ / 4 for every sample (λ > 0).
  `muStd`        The weight 0 for a sample with exactly 2^λ outcomes and 1 for every other.

Notation: `CoinPlan` (Rom/Blocks.lean): "how a uniform sample is made from small ones", with the
fields `w`: a natural number: "a small sample has w + 1 outcomes"; `m`: of type `ℕ → ℕ`: "the number
of small samples for a sample with n + 1 outcomes"; `φ`: of type
`(n : ℕ) → (Fin (m n) → Fin (w + 1)) → Fin (n + 1)`.

Limits: this file does not define how an answer of the oracle is read as a sample, and has no
theorem on a scheme. `blocksStd` wastes answers on samples with few outcomes that are no salts: a
sample with two outcomes takes two answers of λ bits.
-/
import Prob.Bias
import Mathlib.Data.Nat.Size
import Compile.SeedReplay

noncomputable section

open Rom Iop ZKCP Prob
open scoped ENNReal

namespace Compile
namespace Seed

/-- λ bits as a number below 2^λ -/
def digNum (lam : ℕ) : Dig lam ≃ Fin (2 ^ lam) :=
  (Equiv.arrowCongr (Equiv.refl (Fin lam)) finTwoEquiv.symm).trans finFunctionFinEquiv

theorem two_pow_sub_add (lam : ℕ) : 2 ^ lam - 1 + 1 = 2 ^ lam :=
  Nat.sub_add_cancel Nat.one_le_two_pow

/-- the query for the seed s and the counter j -/
def ptStd (lam : ℕ) (s : Fin (2 ^ lam - 1 + 1)) (j : ℕ) : List Bool :=
  (List.ofFn fun i : Fin lam => s.val.testBit i) ++ (List.range j.size).map j.testBit

theorem pt_inj (lam : ℕ) (s : Fin (2 ^ lam - 1 + 1)) (j : ℕ) (s' : Fin (2 ^ lam - 1 + 1))
    (j' : ℕ) (h : ptStd lam s j = ptStd lam s' j') : s = s' ∧ j = j' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  have hj : j = j' := by
    have hl : j.size = j'.size := by simpa using congrArg List.length h2
    rw [hl] at h2
    refine Nat.eq_of_testBit_eq fun i => ?_
    by_cases hi : i < j'.size
    · exact List.map_inj_left.1 h2 i (List.mem_range.2 hi)
    · rw [Nat.testBit_lt_two_pow
            (lt_of_lt_of_le (Nat.lt_size_self j)
              (Nat.pow_le_pow_right (by norm_num) (hl ▸ not_lt.1 hi))),
        Nat.testBit_lt_two_pow
          (lt_of_lt_of_le (Nat.lt_size_self j') (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi)))]
  refine ⟨Fin.ext (Nat.eq_of_testBit_eq fun i => ?_), hj⟩
  by_cases hi : i < lam
  · exact congrFun (List.ofFn_injective h1) ⟨i, hi⟩
  · have hs : ∀ t : Fin (2 ^ lam - 1 + 1), t.val.testBit i = false := fun t =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (lt_of_lt_of_eq t.2 (two_pow_sub_add lam))
        (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi)))
    rw [hs s, hs s']

variable {I X : Type} (lam K : ℕ)

/-- Samples made from samples with 2^λ outcomes. A sample with exactly 2^λ outcomes is one
small sample. -/
def blocksStd : CoinPlan where
  w := 2 ^ lam - 1
  m := fun n => if n + 1 = 2 ^ lam then 1 else Nat.clog 2 (n + 1) / lam + 2
  φ := fun n v => ⟨(finFunctionFinEquiv v).val % (n + 1), Nat.mod_lt _ n.succ_pos⟩

/-- the bias of a sample is that of the reduction modulo n + 1 of a uniform number below (2^λ)^(m
n) -/
theorem bias_blocksStd_eq (n : ℕ) :
    (blocksStd lam).bias n = modBias ((2 ^ lam - 1 + 1) ^ (blocksStd lam).m n) (n + 1) := by
  haveI : NeZero ((2 ^ lam - 1 + 1) ^ (blocksStd lam).m n) := ⟨by positivity⟩
  rw [← tv_natCast_fin_eq]
  show tv ((unif (Fin ((blocksStd lam).m n) → Fin (2 ^ lam - 1 + 1))).map fun v =>
        (⟨(finFunctionFinEquiv v).val % (n + 1), Nat.mod_lt _ n.succ_pos⟩ : Fin (n + 1)))
      (unif (Fin (n + 1))) = _
  rw [← map_unif_equiv (finFunctionFinEquiv (m := 2 ^ lam - 1 + 1) (n := (blocksStd lam).m n)),
    PMF.map_comp]
  rfl

/-- A sample with exactly 2^λ outcomes has no bias. -/
theorem bias_blocksStd_salt {n : ℕ} (h : n + 1 = 2 ^ lam) : (blocksStd lam).bias n = 0 := by
  have hm : (blocksStd lam).m n = 1 := if_pos h
  rw [bias_blocksStd_eq, hm, pow_one, two_pow_sub_add, h]
  unfold modBias
  rw [Nat.mod_self, Nat.zero_mul, Nat.cast_zero, ENNReal.zero_div]

/-- Under `hl`: the bias of a sample made from small ones is at most 2^-λ / 4. -/
theorem bias_blocksStd_le (hl : 0 < lam) (n : ℕ) :
    (blocksStd lam).bias n ≤ (((4 * 2 ^ lam : ℕ) : ℝ≥0∞))⁻¹ := by
  by_cases hs : n + 1 = 2 ^ lam
  · rw [bias_blocksStd_salt lam hs]
    exact zero_le _
  have hm : (blocksStd lam).m n = Nat.clog 2 (n + 1) / lam + 2 := if_neg hs
  obtain ⟨N, hN⟩ : ∃ N, N = (2 ^ lam - 1 + 1) ^ (blocksStd lam).m n := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by rw [hN]; positivity
  have hbig : (n + 1) * 2 ^ lam ≤ N := by
    rw [hN, two_pow_sub_add, ← pow_mul, hm]
    have h1 : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) := Nat.le_pow_clog (by norm_num) _
    have h2 : Nat.clog 2 (n + 1) + lam ≤ lam * (Nat.clog 2 (n + 1) / lam + 2) := by
      have := Nat.div_add_mod (Nat.clog 2 (n + 1)) lam
      have := Nat.mod_lt (Nat.clog 2 (n + 1)) hl
      rw [Nat.mul_add]
      omega
    calc (n + 1) * 2 ^ lam ≤ 2 ^ Nat.clog 2 (n + 1) * 2 ^ lam := Nat.mul_le_mul_right _ h1
      _ = 2 ^ (Nat.clog 2 (n + 1) + lam) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h2
  rw [bias_blocksStd_eq, ← hN]
  refine (modBias_le N (n + 1) hN0 n.succ_ne_zero).trans ?_
  have hc0 : ((4 * N : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero (by norm_num) hN0
  have hD0 : ((4 * 2 ^ lam : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) (by positivity)
  rw [ENNReal.div_le_iff hc0 (ENNReal.natCast_ne_top _), ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl hD0) (Or.inl (ENNReal.natCast_ne_top _))]
  have h4 : (n + 1) * (4 * 2 ^ lam) ≤ 4 * N := by
    calc (n + 1) * (4 * 2 ^ lam) = 4 * ((n + 1) * 2 ^ lam) := by ring
      _ ≤ 4 * N := Nat.mul_le_mul_left 4 hbig
  exact_mod_cast h4

/-- the weight of a sample: 0 if it has exactly 2^λ outcomes, else 1 -/
def muStd (k : ℕ) : ℕ := if k + 1 = 2 ^ lam then 0 else 1

theorem bias_blocksStd_mu (hl : 0 < lam) (k : ℕ) :
    (blocksStd lam).bias k ≤ muStd lam k * (((4 * 2 ^ lam : ℕ) : ℝ≥0∞))⁻¹ := by
  unfold muStd
  by_cases hs : k + 1 = 2 ^ lam
  · rw [bias_blocksStd_salt lam hs]
    exact zero_le _
  · rw [if_neg hs, Nat.cast_one, one_mul]
    exact bias_blocksStd_le lam hl k

end Seed
end Compile
