-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Prob/TailBlocks.lean: binomial tails for very many draws, by certificates in natural numbers in
which M^n does not occur.

Prob/Tail.lean bounds the probability that one of M leaves is drawn more than s times in n uniform
draws by pOver M s n = M · Pr[Bin(n, 1/M) > s]. The inequalities of Prob/TailSharp.lean are exact,
but they contain M^n and powers (M - 1)^(n - j); for n about 10^9 such a number has some 10^10
binary digits. Here the number of draws enters through ratios and, in the lower bound, n + 1 only.

The method. Two neighbouring terms of the tail have the exact ratio tailTerm M n (j + 1) · (j + 1)(M
- 1) = tailTerm M n j · (n - j) (`tailTerm_succ_mul`, Prob/TailSharp.lean), and the ratio falls as j
grows. So over a block of L terms from j on the quotient tailTerm M n (j + L) / tailTerm M n j is
  * at most ((n - j) / ((j + 1)(M - 1)))^L (`tailTerm_block_le`; many blocks: `tailTerm_blocks_le`,
    with `upN`, `upD`),
  * and at least ((n - (j + L)) / ((j + L)(M - 1)))^L (`le_tailTerm_block`; `le_tailTerm_blocks`,
    with `loN`, `loD`).
Upper bound (`mul_tailCount_le_of_blocks`), M > 0 (not all hypotheses are named here: see its
statement): a term is at most M^n, and the tail is at most its first term times a geometric series
(`tailCount_mul_sub_le`, Prob/TailSharp.lean).
Lower bound (`le_mul_tailCount_of_blocks`), M > 1 (not all hypotheses are named here: see its
statement): the terms grow up to the term number
m = ⌊(n + 1) / M⌋ and fall from there (`tailTerm_le_mode`), so that term is at least the average
M^n / (n + 1) (`pow_le_mul_tailTerm_mode`), and the tail is at least its first term.
In both M^n cancels.

Section 6 has the numbers for M = 1,024 leaves and s = 830,934, at the levels 2^-425, 2^-128, 2^-64,
2^-40, 1/2 and 1. This s is used in `Over` (CompileK/CountsOverrun.lean); what it is: the head of
Prob/TailLeaves.lean.

Notation: `tailTerm M n j` (Prob/Tail.lean): the number of sequences of n leaves, out of M, in which
a fixed leaf occurs exactly j times; `tailCount M n r`: the number of such sequences in which it
occurs at least r times; L, K, j: K blocks of L terms from j on; `c` (in the two certificates of
section 4): a natural number, M · 2^e at `pOver_le_of_blocks`, `le_pOver_of_blocks`; the explicit
natural numbers of `pOver_le_of_blocks`, in order: s e n₀ L K j; of `lt_pOver_of_blocks`: s e n₀ L K
m.

Limits: the bounds are not sharp. In the upper bound a term at the start of the blocks is taken to
be M^n, in the lower bound the largest term is taken to be the average of all n + 1; each costs some
bits. Where pOver crosses any of these levels is not decided here: the numbers only enclose the
crossing, or bound it on one side. As in Prob/TailLeaves.lean (Limits): the numbers are statements
on one term (pOver) of a bound, and none is a security level.
-/
import Prob.TailSharp

set_option autoImplicit false

open scoped ENNReal

namespace Prob

/-! ## 1. One block -/

/-- Upper bound over L terms: every ratio in the block is at most the first. -/
theorem tailTerm_block_le (M n j : ℕ) :
    ∀ L : ℕ, tailTerm M n (j + L) * ((j + 1) * (M - 1)) ^ L ≤ tailTerm M n j * (n - j) ^ L
  | 0 => by simp
  | L + 1 => by
    have ih := tailTerm_block_le M n j L
    have e := tailTerm_succ_mul M n (j + L)
    calc
      tailTerm M n (j + (L + 1)) * ((j + 1) * (M - 1)) ^ (L + 1) =
          tailTerm M n (j + L + 1) * ((j + 1) * (M - 1)) * ((j + 1) * (M - 1)) ^ L := by
        rw [pow_succ, ← Nat.add_assoc]; ring
      _ ≤ tailTerm M n (j + L + 1) * ((j + L + 1) * (M - 1)) * ((j + 1) * (M - 1)) ^ L :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega)))
      _ = tailTerm M n (j + L) * ((j + 1) * (M - 1)) ^ L * (n - (j + L)) := by rw [e]; ring
      _ ≤ tailTerm M n j * (n - j) ^ L * (n - j) := Nat.mul_le_mul ih (by omega)
      _ = tailTerm M n j * (n - j) ^ (L + 1) := by rw [pow_succ]; ring

/-- Lower bound over i ≤ L terms: every ratio in the block is at least a / b, if a ≤ n - (j + L) and
(j + L)(M - 1) ≤ b. -/
theorem le_tailTerm_block (M n j L a b : ℕ) (ha : a ≤ n - (j + L)) (hb : (j + L) * (M - 1) ≤ b) :
    ∀ i : ℕ, i ≤ L → tailTerm M n j * a ^ i ≤ tailTerm M n (j + i) * b ^ i
  | 0, _ => by simp
  | i + 1, hi => by
    have ih := le_tailTerm_block M n j L a b ha hb i (by omega)
    have e := tailTerm_succ_mul M n (j + i)
    calc tailTerm M n j * a ^ (i + 1) = tailTerm M n j * a ^ i * a := by rw [pow_succ]; ring
      _ ≤ tailTerm M n (j + i) * b ^ i * (n - (j + i)) := Nat.mul_le_mul ih (by omega)
      _ = tailTerm M n (j + i + 1) * ((j + i + 1) * (M - 1)) * b ^ i := by rw [e]; ring
      _ ≤ tailTerm M n (j + i + 1) * b * b ^ i :=
          Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left _ (le_trans (Nat.mul_le_mul_right _ (by omega)) hb))
      _ = tailTerm M n (j + (i + 1)) * b ^ (i + 1) := by rw [pow_succ, ← Nat.add_assoc]; ring

/-! ## 2. Many blocks -/

/-- numerator (`upN`) and denominator (`upD`) of the upper bound over K blocks of L terms from j
on -/
def upN (n L : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | K + 1, j => (n - j) ^ L * upN n L K (j + L)
def upD (M L : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | K + 1, j => ((j + 1) * (M - 1)) ^ L * upD M L K (j + L)
/-- numerator (`loN`) and denominator (`loD`) of the lower bound over the same blocks -/
def loN (n L : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | K + 1, j => (n - (j + L)) ^ L * loN n L K (j + L)
def loD (M L : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | K + 1, j => ((j + L) * (M - 1)) ^ L * loD M L K (j + L)

theorem tailTerm_blocks_le (M n L : ℕ) :
    ∀ K j : ℕ, tailTerm M n (j + K * L) * upD M L K j ≤ tailTerm M n j * upN n L K j
  | 0, j => by simp [upD, upN]
  | K + 1, j => by
    have ih := tailTerm_blocks_le M n L K (j + L)
    have h1 := tailTerm_block_le M n j L
    have e : j + (K + 1) * L = j + L + K * L := by ring
    calc
      tailTerm M n (j + (K + 1) * L) * upD M L (K + 1) j =
          tailTerm M n (j + L + K * L) * upD M L K (j + L) * ((j + 1) * (M - 1)) ^ L := by
        rw [e, upD]; ring
      _ ≤ tailTerm M n (j + L) * upN n L K (j + L) * ((j + 1) * (M - 1)) ^ L :=
        Nat.mul_le_mul_right _ ih
      _ = tailTerm M n (j + L) * ((j + 1) * (M - 1)) ^ L * upN n L K (j + L) := by ring
      _ ≤ tailTerm M n j * (n - j) ^ L * upN n L K (j + L) := Nat.mul_le_mul_right _ h1
      _ = tailTerm M n j * upN n L (K + 1) j := by rw [upN]; ring

theorem le_tailTerm_blocks (M n L : ℕ) :
    ∀ K j : ℕ, tailTerm M n j * loN n L K j ≤ tailTerm M n (j + K * L) * loD M L K j
  | 0, j => by simp [loD, loN]
  | K + 1, j => by
    have ih := le_tailTerm_blocks M n L K (j + L)
    have h1 := le_tailTerm_block M n j L (n - (j + L)) ((j + L) * (M - 1)) le_rfl le_rfl L le_rfl
    have e : j + (K + 1) * L = j + L + K * L := by ring
    calc
      tailTerm M n j * loN n L (K + 1) j =
          tailTerm M n j * (n - (j + L)) ^ L * loN n L K (j + L) := by rw [loN]; ring
      _ ≤ tailTerm M n (j + L) * ((j + L) * (M - 1)) ^ L * loN n L K (j + L) :=
        Nat.mul_le_mul_right _ h1
      _ = tailTerm M n (j + L) * loN n L K (j + L) * ((j + L) * (M - 1)) ^ L := by ring
      _ ≤ tailTerm M n (j + L + K * L) * loD M L K (j + L) * ((j + L) * (M - 1)) ^ L :=
        Nat.mul_le_mul_right _ ih
      _ = tailTerm M n (j + (K + 1) * L) * loD M L (K + 1) j := by rw [e, loD]; ring

/-! ## 3. The largest term -/

/-- For M > 1 the terms grow while (j + 1) M ≤ n + 1, that is up to m = ⌊(n + 1) / M⌋. -/
theorem tailTerm_le_succ_of {M n j : ℕ} (hM : 1 < M) (h : (j + 1) * M ≤ n + 1) :
    tailTerm M n j ≤ tailTerm M n (j + 1) := by
  have e := tailTerm_succ_mul M n j
  have hD : 0 < (j + 1) * (M - 1) := Nat.mul_pos (by omega) (by omega)
  have hle : (j + 1) * (M - 1) ≤ n - j := by
    have : (j + 1) * (M - 1) + (j + 1) = (j + 1) * M := by
      obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega
  refine Nat.le_of_mul_le_mul_right ?_ hD
  calc tailTerm M n j * ((j + 1) * (M - 1)) ≤ tailTerm M n j * (n - j) := Nat.mul_le_mul_left _ hle
    _ = tailTerm M n (j + 1) * ((j + 1) * (M - 1)) := e.symm

/-- For M > 1 the terms fall once n + 1 ≤ (j + 1) M. -/
theorem tailTerm_succ_le_of {M n j : ℕ} (hM : 1 < M) (h : n + 1 ≤ (j + 1) * M) :
    tailTerm M n (j + 1) ≤ tailTerm M n j := by
  have e := tailTerm_succ_mul M n j
  have hD : 0 < (j + 1) * (M - 1) := Nat.mul_pos (by omega) (by omega)
  have hle : n - j ≤ (j + 1) * (M - 1) := by
    have : (j + 1) * (M - 1) + (j + 1) = (j + 1) * M := by
      obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega
  refine Nat.le_of_mul_le_mul_right ?_ hD
  calc tailTerm M n (j + 1) * ((j + 1) * (M - 1)) = tailTerm M n j * (n - j) := e
    _ ≤ tailTerm M n j * ((j + 1) * (M - 1)) := Nat.mul_le_mul_left _ hle

/-- For M > 1, no term is larger than the term number m, if m M ≤ n + 1 ≤ (m + 1) M. -/
theorem tailTerm_le_mode {M n m : ℕ} (hM : 1 < M) (h1 : m * M ≤ n + 1)
    (h2 : n + 1 ≤ (m + 1) * M) (j : ℕ) :
    tailTerm M n j ≤ tailTerm M n m := by
  rcases Nat.le_total j m with hj | hj
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    clear hj h2
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
      have h3 : (j + d + 1) * M ≤ n + 1 := by rw [← Nat.add_assoc] at h1; exact h1
      exact (ih (le_trans (Nat.mul_le_mul_right _ (by omega)) h3)).trans (tailTerm_le_succ_of hM h3)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    clear hj h1
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
      exact (tailTerm_succ_le_of hM
        (le_trans h2 (Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.le_add_right m d))))).trans ih

/-- Under the hypotheses of `tailTerm_le_mode`, the largest term is at least the average. -/
theorem pow_le_mul_tailTerm_mode
    {M n m : ℕ} (hM : 1 < M) (h1 : m * M ≤ n + 1) (h2 : n + 1 ≤ (m + 1) * M) :
    M ^ n ≤ (n + 1) * tailTerm M n m := by
  rw [← tailCount_zero (by omega : 0 < M) n]
  unfold tailCount
  calc
    ∑ j ∈ Finset.Ico 0 (n + 1), tailTerm M n j ≤ ∑ _j ∈ Finset.Ico 0 (n + 1), tailTerm M n m :=
      Finset.sum_le_sum fun j _ => tailTerm_le_mode hM h1 h2 j
    _ = (n + 1) * tailTerm M n m := by simp

/-! ## 4. The two certificates -/

/-- Upper bound: c · tailCount M n r ≤ M^n, r = j + K L, under `hM`, `hpos` and the certificate
`hcert`, in which M^n does not occur. -/
theorem mul_tailCount_le_of_blocks {M n : ℕ} (hM : 0 < M) (L K j c : ℕ)
    (hpos : 0 < ((j + K * L + 1) * (M - 1) - (n - (j + K * L))) * upD M L K j)
    (hcert : c * ((j + K * L + 1) * (M - 1)) * upN n L K j ≤
      ((j + K * L + 1) * (M - 1) - (n - (j + K * L))) * upD M L K j) :
    c * tailCount M n (j + K * L) ≤ M ^ n := by
  have h1 := tailCount_mul_sub_le M n (j + K * L)
  have h2 := tailTerm_blocks_le M n L K j
  have h3 : tailTerm M n j ≤ M ^ n := (tailTerm_le_tailCount M n j).trans (tailCount_le_pow hM n j)
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc
    c * tailCount M n (j + K * L) *
          (((j + K * L + 1) * (M - 1) - (n - (j + K * L))) * upD M L K j) =
        c * (tailCount M n (j + K * L) * ((j + K * L + 1) * (M - 1) - (n - (j + K * L)))) *
          upD M L K j := by ring
    _ ≤ c * (tailTerm M n (j + K * L) * ((j + K * L + 1) * (M - 1))) * upD M L K j :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
    _ = c * ((j + K * L + 1) * (M - 1)) * (tailTerm M n (j + K * L) * upD M L K j) := by ring
    _ ≤ c * ((j + K * L + 1) * (M - 1)) * (tailTerm M n j * upN n L K j) := Nat.mul_le_mul_left _ h2
    _ ≤ c * ((j + K * L + 1) * (M - 1)) * (M ^ n * upN n L K j) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h3)
    _ = M ^ n * (c * ((j + K * L + 1) * (M - 1)) * upN n L K j) := by ring
    _ ≤ M ^ n * (((j + K * L + 1) * (M - 1) - (n - (j + K * L))) * upD M L K j) :=
      Nat.mul_le_mul_left _ hcert

/-- Lower bound: M^n ≤ c · tailCount M n r, r = m + K L, with blocks that start at the largest term,
under the hypotheses below (`hcert` is the certificate). -/
theorem le_mul_tailCount_of_blocks {M n : ℕ} (hM : 1 < M) (L K m c : ℕ) (h1 : m * M ≤ n + 1)
    (h2 : n + 1 ≤ (m + 1) * M) (hpos : 0 < loN n L K m)
    (hcert : (n + 1) * loD M L K m ≤ c * loN n L K m) :
    M ^ n ≤ c * tailCount M n (m + K * L) := by
  have h3 := pow_le_mul_tailTerm_mode hM h1 h2
  have h4 := le_tailTerm_blocks M n L K m
  have h5 : M ^ n ≤ c * tailTerm M n (m + K * L) := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc M ^ n * loN n L K m ≤ (n + 1) * tailTerm M n m * loN n L K m := Nat.mul_le_mul_right _ h3
      _ = (n + 1) * (tailTerm M n m * loN n L K m) := by ring
      _ ≤ (n + 1) * (tailTerm M n (m + K * L) * loD M L K m) := Nat.mul_le_mul_left _ h4
      _ = tailTerm M n (m + K * L) * ((n + 1) * loD M L K m) := by ring
      _ ≤ tailTerm M n (m + K * L) * (c * loN n L K m) := Nat.mul_le_mul_left _ hcert
      _ = c * tailTerm M n (m + K * L) * loN n L K m := by ring
  exact h5.trans (Nat.mul_le_mul_left _ (tailTerm_le_tailCount M n _))

/-! ## 5. From natural numbers to pOver -/

/-- pOver M s n ≤ 2^(-e) for every n ≤ n₀, from a certificate `hcert` at n₀ (with `hM`, `hr`,
`hpos`). -/
theorem pOver_le_of_blocks {M : ℕ} (hM : 0 < M) (s e n₀ L K j : ℕ) (hr : j + K * L = s + 1)
    (hpos : 0 < ((s + 1 + 1) * (M - 1) - (n₀ - (s + 1))) * upD M L K j)
    (hcert : M * 2 ^ e * ((s + 1 + 1) * (M - 1)) * upN n₀ L K j ≤
      ((s + 1 + 1) * (M - 1) - (n₀ - (s + 1))) * upD M L K j)
    {n : ℕ} (hn : n ≤ n₀) :
    pOver M s n ≤ (2 ^ e : ℝ≥0∞)⁻¹ := by
  have h := mul_tailCount_le_of_blocks
    (n := n₀) hM L K j (M * 2 ^ e) (by rw [hr]; exact hpos) (by rw [hr]; exact hcert)
  rw [hr] at h
  exact (pOver_mono M s hn).trans ((pOver_le_inv_two_pow_iff hM s n₀ e).2 h)

/-- 2^(-e) ≤ pOver M s n for every n ≥ n₀, from a certificate `hcert` at n₀ (under the hypotheses
below). -/
theorem le_pOver_of_blocks {M : ℕ} (hM : 1 < M) (s e n₀ L K m : ℕ) (hr : m + K * L = s + 1)
    (h1 : m * M ≤ n₀ + 1) (h2 : n₀ + 1 ≤ (m + 1) * M) (hpos : 0 < loN n₀ L K m)
    (hcert : (n₀ + 1) * loD M L K m ≤ M * 2 ^ e * loN n₀ L K m) {n : ℕ} (hn : n₀ ≤ n) :
    (2 ^ e : ℝ≥0∞)⁻¹ ≤ pOver M s n := by
  have h := le_mul_tailCount_of_blocks hM L K m (M * 2 ^ e) h1 h2 hpos hcert
  rw [hr] at h
  exact ((inv_two_pow_le_pOver_iff (by omega) s n₀ e).2 h).trans (pOver_mono M s hn)

/-- Under the hypotheses of `le_pOver_of_blocks`, pOver M s n is above 2^(-(e + 1)). -/
theorem lt_pOver_of_blocks {M : ℕ} (hM : 1 < M) (s e n₀ L K m : ℕ) (hr : m + K * L = s + 1)
    (h1 : m * M ≤ n₀ + 1) (h2 : n₀ + 1 ≤ (m + 1) * M) (hpos : 0 < loN n₀ L K m)
    (hcert : (n₀ + 1) * loD M L K m ≤ M * 2 ^ e * loN n₀ L K m) {n : ℕ} (hn : n₀ ≤ n) :
    (2 ^ (e + 1) : ℝ≥0∞)⁻¹ < pOver M s n := by
  refine lt_of_lt_of_le ?_ (le_pOver_of_blocks hM s e n₀ L K m hr h1 h2 hpos hcert hn)
  rw [ENNReal.inv_lt_inv]
  have h : (2 : ℕ) ^ e < 2 ^ (e + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self e)
  exact_mod_cast h

/-! ## 6. The numbers for 1,024 leaves and at most 830,934 draws of one leaf

Blocks of 250 terms. In each instance but `one_le_pOver_1024` the explicit natural numbers are, in
order, s, e, n₀, L, K and the start j (or m) of the blocks, with j + K · L = s + 1 (`hr`). Each
certificate compares two numbers of at most some 800,000 binary digits. -/

/-- pOver 1024 830934 n ≤ 2^(-128) up to n = 837,637,172. -/
theorem pOver_1024_le_128 {n : ℕ} (hn : n ≤ 837637172) : pOver 1024 830934 n ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 128 837637172 250 51 818185 (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- It is above 2^(-128) from n = 839,869,439 on. -/
theorem lt_pOver_1024_128 {n : ℕ} (hn : 839869439 ≤ n) : (2 ^ 128 : ℝ≥0∞)⁻¹ < pOver 1024 830934 n :=
  lt_pOver_of_blocks (by norm_num) 830934 127 839869439 250 43 820185 (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- pOver 1024 830934 n ≤ 2^(-64) up to n = 840,937,935. -/
theorem pOver_1024_le_64 {n : ℕ} (hn : n ≤ 840937935) : pOver 1024 830934 n ≤ (2 ^ 64 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 64 840937935 250 38 821435 (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- It is above 2^(-64) from n = 843,965,439 on. -/
theorem lt_pOver_1024_64 {n : ℕ} (hn : 843965439 ≤ n) : (2 ^ 64 : ℝ≥0∞)⁻¹ < pOver 1024 830934 n :=
  lt_pOver_of_blocks (by norm_num) 830934 63 843965439 250 27 824185 (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- pOver 1024 830934 n ≤ 2^(-40) up to n = 842,508,557. -/
theorem pOver_1024_le_40 {n : ℕ} (hn : n ≤ 842508557) : pOver 1024 830934 n ≤ (2 ^ 40 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 40 842508557 250 32 822935 (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- It is above 2^(-40) from n = 846,269,439 on. -/
theorem lt_pOver_1024_40 {n : ℕ} (hn : 846269439 ≤ n) : (2 ^ 40 : ℝ≥0∞)⁻¹ < pOver 1024 830934 n :=
  lt_pOver_of_blocks (by norm_num) 830934 39 846269439 250 18 826435 (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- pOver 1024 830934 n ≤ 1/2 up to n = 846,039,140. -/
theorem pOver_1024_le_half {n : ℕ} (hn : n ≤ 846039140) : pOver 1024 830934 n ≤ (2 ^ 1 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 1 846039140 250 18 826435 (by norm_num) (by decide +kernel) (by decide +kernel) hn

/-- It is at least 1 from n = 850,876,417 on: then some leaf is drawn more than 830,934 times,
whatever is drawn. -/
theorem one_le_pOver_1024 {n : ℕ} (hn : 850876417 ≤ n) : 1 ≤ pOver 1024 830934 n :=
  one_le_pOver (by norm_num) (by omega)

/-- It is at most 2^(-425) up to n = 827,912,076. -/
theorem pOver_1024_le_425 {n : ℕ} (hn : n ≤ 827912076) : pOver 1024 830934 n ≤ (2 ^ 425 : ℝ≥0∞)⁻¹ :=
  pOver_le_of_blocks (by norm_num)
    830934 425 827912076 250 89 808685 (by norm_num) (by decide +kernel) (by decide +kernel) hn

end Prob
