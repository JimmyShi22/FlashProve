-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Prob/TailLeaves.lean: the bound pOver M s n at s = 830,934, for a variable number M of leaves, and
at M = 16 and M = 256.

pOver M s n = M · Pr[Bin(n, 1/M) > s] bounds the probability that one of M leaves is drawn more than
s times in n uniform draws (Prob/Tail.lean). Prob/TailBlocks.lean has certificates for it
(inequalities between explicit natural numbers), and numbers at M = 1,024. A committer may make any
number of leaves, so here M is a variable.

The number 830,934 is the number for which these certificates were computed. No statement of this
library ties it to a protocol's budget. A leaf of this file is a copy: a further encoding of the
index, no leaf of a hash tree (`Prob.pOver (a.M + 1) u.s1 n`, Johnson/WholeKey/Assembly.lean). At
the library's numbers (`indexPrivacyNumbers`, E2E/PremisesAtFiles.lean: at most 44,040,191 columns of one table
may be read in all) a copy bears at most 688,127 sessions of one request each, at the counts 62 and
64 (`not_noProverSide_session`, same file).

1  A certificate in which M does not occur (`pOver_le_of_ratio`). In the upper bound of
   Prob/TailBlocks.lean a block of L terms from j on has the ratio ((n - j) / ((j + 1)(M - 1)))^L.
   If n ≤ c (M - 1) + j₀, where j₀ is the start of the first block, then n - j ≤ c (M - 1) in every
   block, and M - 1 cancels: the ratio is at most (c / (j + 1))^L. What remains of M is the factor M
   of the union bound, which is taken to be at most 2^a. So one comparison of explicit numbers gives
   (with `hr`, `hKL`, `hc` of its statement)
        pOver M s n ≤ 2^-e      for every M with 1 ≤ M ≤ 2^a and every n ≤ c (M - 1) + j₀, in
                                particular for every n ≤ c M if c ≤ j₀: c draws for each leaf.
   With one leaf (M = 1) the statement is that nothing is overrun in j₀ ≤ s draws.
2  The numbers for s = 830,934 and every M with 1 ≤ M ≤ 2^21 = 2,097,152: the docstrings of section
   2 (`pOver_leaves_le_400` and the theorems after it; `one_le_pOver_leaves`).
3  The numbers at M = 16 and M = 256, by certificates of Prob/TailBlocks.lean at these M (a little
   sharper than 2: in `pOver_le_of_blocks` n - j is taken at each block's start and not bounded once
   by c (M - 1), and the factor is M and not 2^21). pOver M 830934 n is
        M = 16:    at most 2^-140 up to n = 13,090,465;   2^-129 up to 13,097,962;
                   at most 2^-128 up to n = 13,098,653      and above 2^-128 from n = 13,126,959 on;
                   at most 2^-65  up to n = 13,149,130;
                   at most 2^-64  up to n = 13,150,070      and above 2^-64  from n = 13,190,959 on;
                   at most 2^-40  up to n = 13,174,940      and above 2^-40  from n = 13,226,959 on;
                   at most 1/2    up to n = 13,233,873      and at least 1   from n = 13,294,945 on.
        M = 256:   at most 2^-140 up to n = 209,303,514;   2^-129 up to 209,425,428;
                   at most 2^-128 up to n = 209,436,713   and above 2^-128 from n = 209,967,359 on;
                   at most 2^-65  up to n = 210,253,288;
                   at most 2^-64  up to n = 210,268,433   and above 2^-64 from n = 210,991,359 on;
                   at most 2^-40  up to n = 210,666,121   and above 2^-40 from n = 211,567,359 on;
                   at most 1/2    up to n = 211,574,407   and at least 1 from n = 212,719,105 on.
   Where the term crosses a level between the two numbers of a line is not decided here.

Notation: an overrun: some leaf is drawn more than s times (Prob/Tail.lean); the explicit natural
numbers of `pOver_le_of_ratio` and `pOver_le_of_ratio'`, in order: s e a c L K j; of
`pOver_le_of_blocks` (Prob/TailBlocks.lean): s e n₀ L K j; of `lt_pOver_of_blocks`: s e n₀ L K m; L,
K, j (or m): K blocks of L terms from j (or m) on.

Limits: these are statements on one term of a bound. None says that anything is lost when the term
is large, and none is a security level. The bounds are not sharp (the header of Prob/TailBlocks.lean
says why). There is no lower bound with M as a variable but `one_le_pOver_leaves`.

How the numbers were found. Outside Lean, with exact integers: for each level the largest c or n
(for an upper bound), or the least n (for a lower bound), at which the certificate holds, over the
numbers of blocks of 250 terms that were tried. Lean checks each certificate: comparisons of
explicit natural numbers of at most some 800,000 binary digits, by evaluation in the kernel.

Sections 3 and 4 are instances of theorems of Prob/TailBlocks.lean, but for the two "at least 1",
which are `one_le_pOver` of Prob/Tail.lean.
-/
import Prob.TailBlocks

set_option autoImplicit false

open scoped ENNReal

namespace Prob

/-! ## 1. A certificate in which the number of leaves does not occur -/

/-- the part of `upD` that does not depend on M: the product of (j + 1)^L over K blocks of L terms
from j on -/
def upJ (L : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | K + 1, j => (j + 1) ^ L * upJ L K (j + L)

theorem upJ_pos (L : ℕ) : ∀ K j : ℕ, 0 < upJ L K j
  | 0, _ => Nat.one_pos
  | K + 1, j => Nat.mul_pos (Nat.pow_pos (Nat.succ_pos j)) (upJ_pos L K (j + L))

theorem upD_eq (M L : ℕ) : ∀ K j : ℕ, upD M L K j = (M - 1) ^ (K * L) * upJ L K j
  | 0, j => by simp [upD, upJ]
  | K + 1, j => by
    rw [upD, upJ, upD_eq M L K (j + L), mul_pow, Nat.succ_mul, pow_add]
    ring

theorem upN_le (L a : ℕ) : ∀ K j n : ℕ, n ≤ a + j → upN n L K j ≤ a ^ (K * L)
  | 0, j, n, _ => by simp [upN]
  | K + 1, j, n, h =>
    calc upN n L (K + 1) j = (n - j) ^ L * upN n L K (j + L) := rfl
      _ ≤ a ^ L * a ^ (K * L) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) L) (upN_le L a K (j + L) n (by omega))
      _ = a ^ ((K + 1) * L) := by rw [Nat.succ_mul, pow_add, mul_comm]

/-- pOver M s n ≤ 2^(-e) for every M with 1 ≤ M ≤ 2^a and every n ≤ c (M - 1) + j, from one
comparison `hcert` of explicit numbers in which M does not occur (with `hr`, `hKL`, `hc`). -/
theorem pOver_le_of_ratio {M : ℕ} (hM : 0 < M) (s e a c L K j : ℕ) (hMa : M ≤ 2 ^ a)
    (hr : j + K * L = s + 1) (hKL : 0 < K * L) (hc : c < s + 2)
    (hcert : 2 ^ a * 2 ^ e * (s + 2) * c ^ (K * L) ≤ (s + 2 - c) * upJ L K j)
    {n : ℕ} (hn : n ≤ c * (M - 1) + j) :
    pOver M s n ≤ (2 ^ e : ℝ≥0∞)⁻¹ := by
  rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hM) with h1 | h1
  · -- one leaf: n ≤ j ≤ s, nothing is overrun
    subst h1
    rw [pOver_eq_zero 1 (by simp at hn; omega)]
    exact zero_le _
  · obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hn
    have hm : 0 < m := by omega
    have hf : (s + 2 - c) * m ≤ (s + 1 + 1) * (m + 1 - 1) - (c * m + j - (s + 1)) := by
      rw [Nat.add_sub_cancel, Nat.sub_mul]
      have h0 : c * m + j - (s + 1) ≤ c * m := by omega
      exact Nat.sub_le_sub_left h0 _
    have hD : upD (m + 1) L K j = m ^ (K * L) * upJ L K j := by rw [upD_eq, Nat.add_sub_cancel]
    refine pOver_le_of_blocks hM s e (c * m + j) L K j hr ?_ ?_ hn
    · refine Nat.mul_pos (lt_of_lt_of_le (Nat.mul_pos (by omega) hm) hf) ?_
      rw [hD]
      exact Nat.mul_pos (Nat.pow_pos hm) (upJ_pos L K j)
    · calc (m + 1) * 2 ^ e * ((s + 1 + 1) * (m + 1 - 1)) * upN (c * m + j) L K j
          ≤ 2 ^ a * 2 ^ e * ((s + 2) * m) * (c * m) ^ (K * L) := by
            rw [Nat.add_sub_cancel]
            exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hMa))
              (upN_le L (c * m) K j _ le_rfl)
        _ = 2 ^ a * 2 ^ e * (s + 2) * c ^ (K * L) * (m * m ^ (K * L)) := by
            rw [mul_pow]
            ring
        _ ≤ (s + 2 - c) * upJ L K j * (m * m ^ (K * L)) := Nat.mul_le_mul_right _ hcert
        _ = (s + 2 - c) * m * (m ^ (K * L) * upJ L K j) := by ring
        _ ≤ ((s + 1 + 1) * (m + 1 - 1) - (c * m + j - (s + 1))) * upD (m + 1) L K j := by
            rw [hD]
            exact Nat.mul_le_mul_right _ hf

/-- `pOver_le_of_ratio` for n ≤ c M, if c ≤ j: c draws for each leaf -/
theorem pOver_le_of_ratio' {M : ℕ} (hM : 0 < M) (s e a c L K j : ℕ) (hMa : M ≤ 2 ^ a)
    (hr : j + K * L = s + 1) (hKL : 0 < K * L) (hc : c < s + 2) (hcj : c ≤ j)
    (hcert : 2 ^ a * 2 ^ e * (s + 2) * c ^ (K * L) ≤ (s + 2 - c) * upJ L K j) {n : ℕ}
    (hn : n ≤ c * M) :
    pOver M s n ≤ (2 ^ e : ℝ≥0∞)⁻¹ := by
  refine pOver_le_of_ratio hM s e a c L K j hMa hr hKL hc hcert (le_trans hn ?_)
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.mul_succ]
  omega

/-! ## 2. At most 830,934 draws of one leaf, every number of leaves up to 2^21

Blocks of 250 terms. -/

section Leaves
variable {M n : ℕ} (hM : 0 < M) (hMa : M ≤ 2 ^ 21)
include hM hMa

/-- For 0 < M ≤ 2^21: pOver M 830934 n ≤ 2^(-400) up to n = 808,850 M. -/
theorem pOver_leaves_le_400 (hn : n ≤ 808850 * M) : pOver M 830934 n ≤ (2 ^ 400 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_ratio' hM 830934 400 21 808850 250 88 808935 hMa (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) hn

/-- For 0 < M ≤ 2^21: .. ≤ 2^(-140) up to n = 817,023 M. -/
theorem pOver_leaves_le_140 (hn : n ≤ 817023 * M) : pOver M 830934 n ≤ (2 ^ 140 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_ratio' hM 830934 140 21 817023 250 55 817185 hMa (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) hn

/-- For 0 < M ≤ 2^21: .. ≤ 2^(-128) up to n = 817,523 M. -/
theorem pOver_leaves_le_128 (hn : n ≤ 817523 * M) : pOver M 830934 n ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_ratio' hM 830934 128 21 817523 250 53 817685 hMa (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) hn

/-- For 0 < M ≤ 2^21: .. ≤ 2^(-65) up to n = 820,541 M. -/
theorem pOver_leaves_le_65 (hn : n ≤ 820541 * M) : pOver M 830934 n ≤ (2 ^ 65 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_ratio' hM 830934 65 21 820541 250 41 820685 hMa (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) hn

/-- For 0 < M ≤ 2^21: .. ≤ 2^(-64) up to n = 820,597 M. -/
theorem pOver_leaves_le_64 (hn : n ≤ 820597 * M) : pOver M 830934 n ≤ (2 ^ 64 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_ratio' hM 830934 64 21 820597 250 41 820685 hMa (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) hn

/-- For 0 < M ≤ 2^21: .. ≤ 2^(-40) up to n = 822,022 M. -/
theorem pOver_leaves_le_40 (hn : n ≤ 822022 * M) : pOver M 830934 n ≤ (2 ^ 40 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_ratio' hM 830934 40 21 822022 250 35 822185 hMa (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) hn

/-- For 0 < M ≤ 2^21: .. ≤ 1/2 up to n = 825,031 M. -/
theorem pOver_leaves_le_half (hn : n ≤ 825031 * M) : pOver M 830934 n ≤ (2 ^ 1 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_ratio' hM 830934 1 21 825031 250 23 825185 hMa (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) hn

end Leaves

/-- For M > 0, pOver M 830934 n is at least 1 from n = 830,934 M + 1 on: then some leaf is drawn
more than 830,934 times, whatever is drawn. -/
theorem one_le_pOver_leaves {M n : ℕ} (hM : 0 < M) (hn : 830934 * M < n) : 1 ≤ pOver M 830934 n :=
  one_le_pOver hM hn

/-! ## 3. Sixteen leaves -/

theorem pOver_16_le_140 {n : ℕ} (hn : n ≤ 13090465) : pOver 16 830934 n ≤ (2 ^ 140 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 140 13090465 250 51 818185 (by norm_num) (by decide +kernel) (by decide +kernel) hn

theorem pOver_16_le_129 {n : ℕ} (hn : n ≤ 13097962) : pOver 16 830934 n ≤ (2 ^ 129 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 129 13097962 250 49 818685 (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- pOver 16 830934 n ≤ 2^(-128) up to n = 13,098,653. -/
theorem pOver_16_le_128 {n : ℕ} (hn : n ≤ 13098653) : pOver 16 830934 n ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 128 13098653 250 49 818685 (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- It is above 2^(-128) from n = 13,126,959 on. -/
theorem lt_pOver_16_128 {n : ℕ} (hn : 13126959 ≤ n) : (2 ^ 128 : ℝ≥0∞)⁻¹ < pOver 16 830934 n :=
  lt_pOver_of_blocks (by norm_num) 830934 127 13126959 250 42 820435 (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) hn

theorem pOver_16_le_65 {n : ℕ} (hn : n ≤ 13149130) : pOver 16 830934 n ≤ (2 ^ 65 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 65 13149130 250 36 821935 (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- pOver 16 830934 n ≤ 2^(-64) up to n = 13,150,070. -/
theorem pOver_16_le_64 {n : ℕ} (hn : n ≤ 13150070) : pOver 16 830934 n ≤ (2 ^ 64 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 64 13150070 250 36 821935 (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- It is above 2^(-64) from n = 13,190,959 on. -/
theorem lt_pOver_16_64 {n : ℕ} (hn : 13190959 ≤ n) : (2 ^ 64 : ℝ≥0∞)⁻¹ < pOver 16 830934 n :=
  lt_pOver_of_blocks (by norm_num) 830934 63 13190959 250 26 824435 (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- pOver 16 830934 n ≤ 2^(-40) up to n = 13,174,940. -/
theorem pOver_16_le_40 {n : ℕ} (hn : n ≤ 13174940) : pOver 16 830934 n ≤ (2 ^ 40 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 40 13174940 250 30 823435 (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- It is above 2^(-40) from n = 13,226,959 on. -/
theorem lt_pOver_16_40 {n : ℕ} (hn : 13226959 ≤ n) : (2 ^ 40 : ℝ≥0∞)⁻¹ < pOver 16 830934 n :=
  lt_pOver_of_blocks (by norm_num) 830934 39 13226959 250 17 826685 (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- pOver 16 830934 n ≤ 1/2 up to n = 13,233,873. -/
theorem pOver_16_le_half {n : ℕ} (hn : n ≤ 13233873) : pOver 16 830934 n ≤ (2 ^ 1 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 1 13233873 250 15 827185 (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- It is at least 1 from n = 13,294,945 on. -/
theorem one_le_pOver_16 {n : ℕ} (hn : 13294945 ≤ n) : 1 ≤ pOver 16 830934 n :=
  one_le_pOver (by norm_num) (by omega)

/-! ## 4. 256 leaves -/

theorem pOver_256_le_140 {n : ℕ} (hn : n ≤ 209303514) : pOver 256 830934 n ≤ (2 ^ 140 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 140 209303514 250 53 817685 (by norm_num) (by decide +kernel) (by decide +kernel) hn

theorem pOver_256_le_129 {n : ℕ} (hn : n ≤ 209425428) : pOver 256 830934 n ≤ (2 ^ 129 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 129 209425428 250 51 818185 (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- pOver 256 830934 n ≤ 2^(-128) up to n = 209,436,713. -/
theorem pOver_256_le_128 {n : ℕ} (hn : n ≤ 209436713) : pOver 256 830934 n ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 128 209436713 250 51 818185 (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- It is above 2^(-128) from n = 209,967,359 on. -/
theorem lt_pOver_256_128 {n : ℕ} (hn : 209967359 ≤ n) : (2 ^ 128 : ℝ≥0∞)⁻¹ < pOver 256 830934 n :=
  lt_pOver_of_blocks (by norm_num) 830934 127 209967359 250 43 820185 (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) hn

theorem pOver_256_le_65 {n : ℕ} (hn : n ≤ 210253288) : pOver 256 830934 n ≤ (2 ^ 65 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 65 210253288 250 38 821435 (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- pOver 256 830934 n ≤ 2^(-64) up to n = 210,268,433. -/
theorem pOver_256_le_64 {n : ℕ} (hn : n ≤ 210268433) : pOver 256 830934 n ≤ (2 ^ 64 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 64 210268433 250 38 821435 (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- It is above 2^(-64) from n = 210,991,359 on. -/
theorem lt_pOver_256_64 {n : ℕ} (hn : 210991359 ≤ n) : (2 ^ 64 : ℝ≥0∞)⁻¹ < pOver 256 830934 n :=
  lt_pOver_of_blocks (by norm_num) 830934 63 210991359 250 27 824185 (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- pOver 256 830934 n ≤ 2^(-40) up to n = 210,666,121. -/
theorem pOver_256_le_40 {n : ℕ} (hn : n ≤ 210666121) : pOver 256 830934 n ≤ (2 ^ 40 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 40 210666121 250 32 822935 (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- It is above 2^(-40) from n = 211,567,359 on. -/
theorem lt_pOver_256_40 {n : ℕ} (hn : 211567359 ≤ n) : (2 ^ 40 : ℝ≥0∞)⁻¹ < pOver 256 830934 n :=
  lt_pOver_of_blocks (by norm_num) 830934 39 211567359 250 18 826435 (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- pOver 256 830934 n ≤ 1/2 up to n = 211,574,407. -/
theorem pOver_256_le_half {n : ℕ} (hn : n ≤ 211574407) : pOver 256 830934 n ≤ (2 ^ 1 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 1 211574407 250 17 826685 (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- It is at least 1 from n = 212,719,105 on. -/
theorem one_le_pOver_256 {n : ℕ} (hn : 212719105 ≤ n) : 1 ≤ pOver 256 830934 n :=
  one_le_pOver (by norm_num) (by omega)

end Prob
