-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Prob/Tail.lean: how often one of M leaves is drawn in n uniform draws.

Every draw names a leaf, uniformly among M leaves and independently of everything before it. How
likely is an overrun (some leaf is drawn more than s times), if a strategy chooses when to draw?

Order of arguments (all are natural numbers, so a swap is not caught by the type checker):
`tailCount M n r`, `hitTail M n r`, `binTail n M s`, `pOver M s n`, `pOverClosed M s n`.

Main statements.
* `card_hits_ge`, `pr_hits_ge`: in n independent uniform draws a fixed leaf is drawn at least r
  times with probability exactly hitTail M n r, an explicit finite sum (`binTail_eq_binomial`: the
  tail of Mathlib's binomial distribution).
* `pr_exists_hits_gt_le`: Pr[some leaf is drawn more than s times] <= pOver M s n = M * Pr[Bin(n,
  1/M) > s].
* `overPotential` and its lemmas, `pr_bind_le`, `pr_bind_uniform_le_overPotential`: the invariant
  behind an adaptive bound, for use in an induction over a game (Rom/Overrun.lean:
  `tv_le_potential`).
* `pOver_le_choose`, `pOver_le_closed`: the union-bound form M * C(n, s+1) / M^(s+1) and the closed
  form M * (e n / ((s+1) M))^(s+1).
* pOver is a union bound and not a probability: section 6.

Limits.
* Not in this file: the bound against a strategy that decides adaptively when to draw; only its
  invariant, `overPotential`, is here.
* Not in this file: the loads of the leaves, and the step to "a leaf is overloaded only if it is
  drawn more than s times". Both are arithmetic. Batches are not modelled either: a leaf that is
  drawn n' times computes at most n' s2 batches (at most s2 for each draw), so it is enough to count
  draws.

Only Mathlib is imported.
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Exponential
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal NNReal

namespace Prob

/-! ## 1. The counts

Everything about the binomial tail is first proved for natural numbers: tailCount M n r is the
number of sequences of n leaves (out of M) in which a fixed leaf occurs at least r times. -/

/-- The number of sequences of n leaves, out of M, in which a fixed leaf occurs exactly j times:
choose the j places, and fill each other place with one of the M - 1 other leaves. -/
def tailTerm (M n j : ℕ) : ℕ := n.choose j * (M - 1) ^ (n - j)

/-- The number of sequences of n leaves, out of M, in which a fixed leaf occurs at least r times
(`card_hits_ge` proves that it is this number). -/
def tailCount (M n r : ℕ) : ℕ := ∑ j ∈ Finset.Ico r (n + 1), tailTerm M n j

theorem tailTerm_eq_zero {M n j : ℕ} (h : n < j) : tailTerm M n j = 0 := by
  simp [tailTerm, Nat.choose_eq_zero_of_lt h]

/-- Pascal's rule for the terms: look at the first place of the sequence. -/
theorem tailTerm_succ_succ (M n j : ℕ) :
    tailTerm M (n + 1) (j + 1) = tailTerm M n j + (M - 1) * tailTerm M n (j + 1) := by
  unfold tailTerm
  rw [Nat.choose_succ_succ, Nat.add_sub_add_right, add_mul]
  congr 1
  rcases Nat.lt_or_ge n (j + 1) with h | h
  · simp [Nat.choose_eq_zero_of_lt h]
  · have e : n - j = (n - (j + 1)) + 1 := by omega
    rw [e, pow_succ]
    ring

theorem tailCount_eq_zero {M n r : ℕ} (h : n < r) : tailCount M n r = 0 := by
  unfold tailCount
  rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty]

/-- For M > 0, every sequence has the fixed leaf at least 0 times: the binomial theorem. -/
theorem tailCount_zero {M : ℕ} (hM : 0 < M) (n : ℕ) : tailCount M n 0 = M ^ n := by
  have h1 : 1 + (M - 1) = M := by omega
  calc tailCount M n 0 = (1 + (M - 1)) ^ n := by
        unfold tailCount tailTerm
        rw [Nat.Ico_zero_eq_range, add_pow]
        exact Finset.sum_congr rfl fun j _ => by rw [one_pow, one_mul, Nat.cast_id, mul_comm]
    _ = M ^ n := by rw [h1]

/-- The sum may run one step further: the extra term is 0. -/
theorem sum_Ico_tailTerm (M n r : ℕ) :
    ∑ j ∈ Finset.Ico r (n + 2), tailTerm M n j = tailCount M n r := by
  symm
  refine Finset.sum_subset (Finset.Ico_subset_Ico le_rfl (by omega)) fun j hj hj' => ?_
  rw [Finset.mem_Ico] at hj hj'
  exact tailTerm_eq_zero (by omega)

/-- The recursion of the tail: the first draw hits the fixed leaf (1 way) or misses it (M - 1
ways). -/
theorem tailCount_succ_succ (M n r : ℕ) :
    tailCount M (n + 1) (r + 1) = tailCount M n r + (M - 1) * tailCount M n (r + 1) := by
  calc tailCount M (n + 1) (r + 1)
      = ∑ j ∈ Finset.Ico r (n + 1), tailTerm M (n + 1) (j + 1) := by
        unfold tailCount
        rw [Finset.sum_Ico_add' (fun j => tailTerm M (n + 1) j) r (n + 1) 1]
    _ = ∑ j ∈ Finset.Ico r (n + 1), tailTerm M n j
          + (M - 1) * ∑ j ∈ Finset.Ico r (n + 1), tailTerm M n (j + 1) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => tailTerm_succ_succ M n j
    _ = tailCount M n r + (M - 1) * tailCount M n (r + 1) := by
        rw [Finset.sum_Ico_add' (fun j => tailTerm M n j) r (n + 1) 1, sum_Ico_tailTerm]
        rfl

/-- For M > 0, the recursion in the form that also covers r = 0 (subtraction of natural numbers
stops at 0). -/
theorem tailCount_succ {M : ℕ} (hM : 0 < M) (n r : ℕ) :
    tailCount M (n + 1) r = tailCount M n (r - 1) + (M - 1) * tailCount M n r := by
  cases r with
  | zero =>
    obtain ⟨q, rfl⟩ : ∃ q, M = q + 1 := ⟨M - 1, by omega⟩
    rw [Nat.zero_sub, tailCount_zero hM, tailCount_zero hM, Nat.add_sub_cancel]
    ring
  | succ r => rw [tailCount_succ_succ, Nat.add_sub_cancel]

/-- Asking for more hits leaves fewer sequences. -/
theorem tailCount_anti (M n : ℕ) {r r' : ℕ} (h : r ≤ r') : tailCount M n r' ≤ tailCount M n r :=
  Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico h le_rfl)

theorem tailCount_le_pow {M : ℕ} (hM : 0 < M) (n r : ℕ) : tailCount M n r ≤ M ^ n :=
  (tailCount_anti M n (Nat.zero_le r)).trans_eq (tailCount_zero hM n)

/-- For M > 0, one more draw cannot lower the share of sequences with at least r hits. -/
theorem mul_tailCount_le_succ {M : ℕ} (hM : 0 < M) (n r : ℕ) :
    M * tailCount M n r ≤ tailCount M (n + 1) r := by
  rw [tailCount_succ hM]
  have h := tailCount_anti M n (Nat.sub_le r 1)
  calc M * tailCount M n r = tailCount M n r + (M - 1) * tailCount M n r := by
        obtain ⟨q, rfl⟩ : ∃ q, M = q + 1 := ⟨M - 1, by omega⟩
        rw [Nat.add_sub_cancel]; ring
    _ ≤ tailCount M n (r - 1) + (M - 1) * tailCount M n r := Nat.add_le_add_right h _

/-- For M > 0, the union bound over the sets of r places, in natural numbers:
tailCount / M^n <= C(n, r) / M^r. -/
theorem tailCount_mul_pow_le {M : ℕ} (hM : 0 < M) (n r : ℕ) :
    tailCount M n r * M ^ r ≤ n.choose r * M ^ n := by
  induction n generalizing r with
  | zero =>
    cases r with
    | zero => simp [tailCount_zero hM]
    | succ r => simp [tailCount_eq_zero (Nat.succ_pos r)]
  | succ n ih =>
    cases r with
    | zero => simp [tailCount_zero hM]
    | succ r =>
      have h1 := ih r
      have h2 := ih (r + 1)
      have h3 : M - 1 ≤ M := Nat.sub_le M 1
      calc tailCount M (n + 1) (r + 1) * M ^ (r + 1)
          = (tailCount M n r * M ^ r) * M + (M - 1) * (tailCount M n (r + 1) * M ^ (r + 1)) := by
            rw [tailCount_succ_succ]; ring
        _ ≤ (n.choose r * M ^ n) * M + M * (n.choose (r + 1) * M ^ n) :=
            Nat.add_le_add (Nat.mul_le_mul_right _ h1) (Nat.mul_le_mul h3 h2)
        _ = (n + 1).choose (r + 1) * M ^ (n + 1) := by
            rw [Nat.choose_succ_succ]; ring

/-! ## 2. Sequences of n draws, counted

A tape is a sequence of n draws that is fixed in advance, ω : Fin n → L. -/

section Tape

variable {L : Type} [Fintype L] [DecidableEq L]

/-- A sum over all leaves of a quantity that has one value at the leaf k and another at all other
leaves. -/
theorem sum_ite_eq_add {R : Type} [Semiring R] (k : L) (x y : R) :
    ∑ a : L, (if a = k then x else y) = x + ((Fintype.card L - 1 : ℕ) : R) * y := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k), if_pos rfl]
  congr 1
  have h : ∀ a ∈ Finset.univ.erase k, (if a = k then x else y) = y :=
    fun a ha => if_neg (Finset.ne_of_mem_erase ha)
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k),
    Finset.card_univ, nsmul_eq_mul]

/-- How often the leaf k occurs in the sequence of draws ω. -/
def hits {n : ℕ} (ω : Fin n → L) (k : L) : ℕ := (Finset.univ.filter fun i => ω i = k).card

omit [Fintype L] in
theorem hits_cons {n : ℕ} (a : L) (ω : Fin n → L) (k : L) :
    hits (Fin.cons a ω : Fin (n + 1) → L) k = (if a = k then 1 else 0) + hits ω k := by
  unfold hits
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- The count is exact. Among the M^n sequences of n leaves, exactly tailCount M n r contain the
leaf k at least r times. -/
theorem card_hits_ge (n r : ℕ) (k : L) :
    (Finset.univ.filter fun ω : Fin n → L => r ≤ hits ω k).card
      = tailCount (Fintype.card L) n r := by
  have hM : 0 < Fintype.card L := Fintype.card_pos_iff.mpr ⟨k⟩
  induction n generalizing r with
  | zero =>
    cases r with
    | zero => simp [tailCount_zero hM]
    | succ r => simp [tailCount_eq_zero (Nat.succ_pos r), hits]
  | succ n ih =>
    have hs := sum_ite_eq_add k (Finset.univ.filter fun ω : Fin n → L => r - 1 ≤ hits ω k).card
      (Finset.univ.filter fun ω : Fin n → L => r ≤ hits ω k).card
    rw [Nat.cast_id] at hs
    rw [tailCount_succ hM, ← ih, ← ih, Finset.card_filter,
      ← (Fin.consEquiv fun _ : Fin (n + 1) => L).sum_comp, Fintype.sum_prod_type, ← hs]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.card_filter]
    by_cases h : a = k
    · rw [if_pos h]
      congr 1
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show r ≤ hits (Fin.cons a ω : Fin (n + 1) → L) k ↔ r - 1 ≤ hits ω k
      rw [hits_cons, if_pos h]
      omega
    · rw [if_neg h]
      congr 1
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show r ≤ hits (Fin.cons a ω : Fin (n + 1) → L) k ↔ r ≤ hits ω k
      rw [hits_cons, if_neg h, Nat.zero_add]

/-- The union bound over the leaves, counted. -/
theorem card_exists_hits_gt_le (n s : ℕ) :
    (Finset.univ.filter fun ω : Fin n → L => ∃ k, s < hits ω k).card
      ≤ Fintype.card L * tailCount (Fintype.card L) n (s + 1) := by
  calc (Finset.univ.filter fun ω : Fin n → L => ∃ k, s < hits ω k).card
      ≤ (Finset.univ.biUnion fun k : L =>
          Finset.univ.filter fun ω : Fin n → L => s + 1 ≤ hits ω k).card := by
        refine Finset.card_le_card fun ω hω => ?_
        simpa [Nat.succ_le_iff] using hω
    _ ≤ ∑ k : L, (Finset.univ.filter fun ω : Fin n → L => s + 1 ≤ hits ω k).card :=
        Finset.card_biUnion_le
    _ = Fintype.card L * tailCount (Fintype.card L) n (s + 1) := by
        simp only [card_hits_ge, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- With more than s * M draws some leaf is drawn more than s times, whatever the draws are. -/
theorem exists_hits_gt {n s : ℕ} (h : s * Fintype.card L < n) (ω : Fin n → L) : ∃ k, s < hits ω k :=
  Fintype.exists_lt_card_fiber_of_mul_lt_card ω (by rw [Fintype.card_fin, mul_comm]; exact h)

/-- Beyond s * M draws the union bound counts every sequence at least once. -/
theorem card_pow_le_mul_tailCount {n s : ℕ} (h : s * Fintype.card L < n) :
    Fintype.card L ^ n ≤ Fintype.card L * tailCount (Fintype.card L) n (s + 1) := by
  refine le_trans ?_ (card_exists_hits_gt_le (L := L) n s)
  have h2 : Fintype.card L ^ n = (Finset.univ : Finset (Fin n → L)).card := by simp
  rw [h2]
  exact Finset.card_le_card fun ω _ => Finset.mem_filter.2 ⟨Finset.mem_univ ω, exists_hits_gt h ω⟩

end Tape

/-- Beyond s * M draws the union bound counts every sequence at least once (the same, for M as a
number). -/
theorem pow_le_mul_tailCount {M n s : ℕ} (h : s * M < n) : M ^ n ≤ M * tailCount M n (s + 1) := by
  simpa using card_pow_le_mul_tailCount (L := Fin M) (n := n) (s := s) (by simpa using h)

/-! ## 3. The probabilities

In the statements on sequences of draws the type L of leaves is non-empty (M ≥ 1). -/

/-- Pr[Bin(n, 1/M) >= r], as an exact finite sum divided by M^n. Meant for M >= 1; at M = 0 the
value has no meaning (it can be ∞), while pOver 0 s n = 0. -/
def hitTail (M n r : ℕ) : ℝ≥0∞ := (tailCount M n r : ℝ≥0∞) / (M : ℝ≥0∞) ^ n

/-- Pr[Bin(n, 1/M) > s], as an exact finite sum divided by M^n:
the sum of C(n, j) (M - 1)^(n - j) over s < j <= n, over M^n. -/
def binTail (n M s : ℕ) : ℝ≥0∞ := hitTail M n (s + 1)

/-- The bound on the probability of an overrun: M * Pr[Bin(n, 1/M) > s], for M leaves, n draws, and
at most s draws allowed per leaf. It is the expected number of leaves that are drawn more than s
times (`pOver_eq_sum_pr`), so it can exceed 1 (section 6). -/
def pOver (M s n : ℕ) : ℝ≥0∞ := (M : ℝ≥0∞) * binTail n M s

/-- Comparing two fractions of natural numbers in ℝ≥0∞ by cross-multiplication. -/
theorem natCast_div_le_div_of_pos {a b c d : ℕ} (hc : 0 < c) (hd : 0 < d) (h : a * d ≤ b * c) :
    (a : ℝ≥0∞) / c ≤ (b : ℝ≥0∞) / d := by
  have hc0 : (c : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  have hd0 : (d : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl (ENNReal.natCast_ne_top d)),
    ← ENNReal.mul_div_right_comm, ENNReal.div_le_iff hc0 (ENNReal.natCast_ne_top c)]
  exact_mod_cast h

theorem hitTail_zero {M : ℕ} (hM : 0 < M) (n : ℕ) : hitTail M n 0 = 1 := by
  unfold hitTail
  rw [tailCount_zero hM, Nat.cast_pow]
  exact ENNReal.div_self (pow_ne_zero _ (Nat.cast_ne_zero.mpr hM.ne'))
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top M))

theorem hitTail_eq_zero {M n r : ℕ} (h : n < r) : hitTail M n r = 0 := by
  simp [hitTail, tailCount_eq_zero h]

theorem hitTail_anti (M n : ℕ) {r r' : ℕ} (h : r ≤ r') : hitTail M n r' ≤ hitTail M n r :=
  ENNReal.div_le_div_right (by exact_mod_cast tailCount_anti M n h) _

theorem hitTail_le_one {M : ℕ} (hM : 0 < M) (n r : ℕ) : hitTail M n r ≤ 1 :=
  (hitTail_anti M n (Nat.zero_le r)).trans_eq (hitTail_zero hM n)

theorem hitTail_le_succ {M : ℕ} (hM : 0 < M) (n r : ℕ) : hitTail M n r ≤ hitTail M (n + 1) r := by
  unfold hitTail
  rw [← Nat.cast_pow, ← Nat.cast_pow]
  refine natCast_div_le_div_of_pos (Nat.pow_pos hM) (Nat.pow_pos hM) ?_
  calc tailCount M n r * M ^ (n + 1) = (M * tailCount M n r) * M ^ n := by ring
    _ ≤ tailCount M (n + 1) r * M ^ n := Nat.mul_le_mul_right _ (mul_tailCount_le_succ hM n r)

/-- For M > 0, the law of total probability on the first draw: it hits the fixed leaf with
probability 1/M. -/
theorem hitTail_succ {M : ℕ} (hM : 0 < M) (n r : ℕ) :
    hitTail M (n + 1) r
      = (M : ℝ≥0∞)⁻¹ * (hitTail M n (r - 1) + ((M - 1 : ℕ) : ℝ≥0∞) * hitTail M n r) := by
  have hM0 : (M : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hMt : (M : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top M
  unfold hitTail
  rw [tailCount_succ hM, Nat.cast_add, Nat.cast_mul, pow_succ, div_eq_mul_inv, div_eq_mul_inv,
    div_eq_mul_inv, ENNReal.mul_inv (Or.inl (pow_ne_zero _ hM0)) (Or.inl (ENNReal.pow_ne_top hMt))]
  ring

section TapeProb

variable {L : Type} [Fintype L] [DecidableEq L] [Nonempty L]

omit [DecidableEq L] in
/-- Under the uniform distribution on sequences of n leaves (that is: n independent uniform draws),
the probability of an event is the number of its sequences over M^n. -/
theorem pr_tape {n : ℕ} (P : (Fin n → L) → Prop) [DecidablePred P] :
    (PMF.uniformOfFintype (Fin n → L)).toOuterMeasure {ω | P ω}
      = ((Finset.univ.filter P).card : ℝ≥0∞) / (Fintype.card L : ℝ≥0∞) ^ n := by
  rw [PMF.toOuterMeasure_apply_fintype, div_eq_mul_inv, ← nsmul_eq_mul, ← Finset.sum_const,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : P ω
  · simp [h, PMF.uniformOfFintype_apply]
  · simp [h]

/-- A fixed leaf. In n independent uniform draws from M leaves, the leaf k is drawn at least r times
with probability exactly hitTail M n r. -/
theorem pr_hits_ge (n r : ℕ) (k : L) :
    (PMF.uniformOfFintype (Fin n → L)).toOuterMeasure {ω | r ≤ hits ω k}
      = hitTail (Fintype.card L) n r := by
  rw [pr_tape, card_hits_ge, hitTail]

/-- In n independent uniform draws, the leaf k is drawn more than s times with probability exactly
binTail n M s. -/
theorem pr_hits_gt (n s : ℕ) (k : L) :
    (PMF.uniformOfFintype (Fin n → L)).toOuterMeasure {ω | s < hits ω k}
      = binTail n (Fintype.card L) s :=
  pr_hits_ge n (s + 1) k

/-- Some leaf. In n independent uniform draws from M leaves, the probability that some leaf is drawn
more than s times is at most pOver M s n = M * Pr[Bin(n, 1/M) > s]. -/
theorem pr_exists_hits_gt_le (n s : ℕ) :
    (PMF.uniformOfFintype (Fin n → L)).toOuterMeasure {ω | ∃ k, s < hits ω k}
      ≤ pOver (Fintype.card L) s n := by
  rw [pr_tape, pOver, binTail, hitTail, ← mul_div_assoc]
  exact ENNReal.div_le_div_right (by exact_mod_cast card_exists_hits_gt_le (L := L) n s) _

/-- pOver is the expected number of leaves that are drawn more than s times. -/
theorem pOver_eq_sum_pr (s n : ℕ) :
    pOver (Fintype.card L) s n
      = ∑ k : L, (PMF.uniformOfFintype (Fin n → L)).toOuterMeasure {ω | s < hits ω k} := by
  simp only [pr_hits_gt, pOver, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end TapeProb

/-! ## 4. The invariant of the adaptive bound

A game in which leaves are drawn one at a time, at moments that an adversary chooses, can be
analysed with one quantity: given how often each leaf has been drawn so far (c) and how many draws
are still allowed (m), overPotential s c m is the sum over the leaves of the probability that m
further draws bring that leaf above s. An induction over the game needs three lemmas: the potential
starts at pOver; it is at least 1 once an overrun has happened; a draw preserves its average. A
fourth, that giving up a draw does not raise it, is needed only in a game that can spend one of its
n draws without drawing. `avg_overPotential`, `overPotential_le_succ` and
`pr_bind_uniform_le_overPotential` take L non-empty. -/

section Potential

variable {L : Type} [Fintype L] [DecidableEq L]

/-- The sum, over the leaves k, of the probability that m further uniform draws hit k often enough
to bring its number of draws from c k to more than s (this probability is 1 if c k > s already). -/
def overPotential (s : ℕ) (c : L → ℕ) (m : ℕ) : ℝ≥0∞ :=
  ∑ k : L, hitTail (Fintype.card L) m (s + 1 - c k)

omit [DecidableEq L] in
/-- At the start, with no leaf drawn and n draws allowed, the potential is pOver. -/
theorem overPotential_zero (s n : ℕ) :
    overPotential s (fun _ : L => 0) n = pOver (Fintype.card L) s n := by
  simp [overPotential, pOver, binTail]

omit [DecidableEq L] in
/-- After an overrun the potential is at least 1. -/
theorem one_le_overPotential (s : ℕ) (c : L → ℕ) (m : ℕ) (h : ∃ k, s < c k) :
    1 ≤ overPotential s c m := by
  obtain ⟨k, hk⟩ := h
  have hM : 0 < Fintype.card L := Fintype.card_pos_iff.mpr ⟨k⟩
  have e : s + 1 - c k = 0 := by omega
  calc (1 : ℝ≥0∞) = hitTail (Fintype.card L) m (s + 1 - c k) := by rw [e, hitTail_zero hM]
    _ ≤ overPotential s c m :=
        Finset.single_le_sum (f := fun k => hitTail (Fintype.card L) m (s + 1 - c k))
          (fun _ _ => zero_le _) (Finset.mem_univ k)

/-- A uniform draw preserves the potential on average: the average, over the leaf a that is drawn,
of the potential with a counted once more and m draws left is the potential with m + 1 draws
left. -/
theorem avg_overPotential [Nonempty L] (s : ℕ) (c : L → ℕ) (m : ℕ) :
    ∑ a : L, (Fintype.card L : ℝ≥0∞)⁻¹ * overPotential s (Function.update c a (c a + 1)) m
      = overPotential s c (m + 1) := by
  have hM : 0 < Fintype.card L := Fintype.card_pos
  unfold overPotential
  rw [← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hitTail_succ hM, ← sum_ite_eq_add k]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a = k
  · subst h
    rw [if_pos rfl, Function.update_self, Nat.sub_add_eq]
  · rw [if_neg h, Function.update_of_ne (Ne.symm h)]

omit [DecidableEq L] in
/-- Not using a draw does not raise the potential. -/
theorem overPotential_le_succ [Nonempty L] (s : ℕ) (c : L → ℕ) (m : ℕ) :
    overPotential s c m ≤ overPotential s c (m + 1) :=
  Finset.sum_le_sum fun _ _ => hitTail_le_succ Fintype.card_pos _ _

omit [DecidableEq L] in
theorem overPotential_mono [Nonempty L] (s : ℕ) (c : L → ℕ) : Monotone (overPotential s c) :=
  monotone_nat_of_le_succ (overPotential_le_succ s c)

/-- A step of an induction over a game: a move whose outcome b has any discrete distribution p (a
coin, an oracle's answer, a message). If the bound v holds after every possible outcome, it holds
before the move. -/
theorem pr_bind_le {α β : Type} (p : PMF β) (f : β → PMF α) (E : Set α) (v : ℝ≥0∞)
    (h : ∀ b ∈ p.support, (f b).toOuterMeasure E ≤ v) : (p.bind f).toOuterMeasure E ≤ v := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc ∑' b, p b * (f b).toOuterMeasure E ≤ ∑' b, p b * v := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        by_cases hb : p b = 0
        · simp [hb]
        · gcongr
          exact h b ((PMF.mem_support_iff p b).2 hb)
    _ = v := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- A step of an induction over a game: a uniform draw of a leaf. If after the draw of a the
potential with a counted once more and m draws left is a bound, then before the draw the potential
with m + 1 draws left is. -/
theorem pr_bind_uniform_le_overPotential {α : Type} [Nonempty L] (f : L → PMF α) (E : Set α)
    (s m : ℕ) (c : L → ℕ)
    (h : ∀ a, (f a).toOuterMeasure E ≤ overPotential s (Function.update c a (c a + 1)) m) :
    ((PMF.uniformOfFintype L).bind f).toOuterMeasure E ≤ overPotential s c (m + 1) := by
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype, ← avg_overPotential]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [PMF.uniformOfFintype_apply]
  gcongr
  exact h a

end Potential


namespace Strategy

variable {L : Type}



variable [Fintype L] [Nonempty L]

variable [DecidableEq L]

omit [Fintype L] [Nonempty L] in
/-- The event "some leaf is above s" after one more draw of a, in terms of the counts so far. -/
theorem preimage_cons_over (s : ℕ) (c : L → ℕ) (a : L) :
    (fun l : List L => a :: l) ⁻¹' {l | ∃ k, s < c k + l.count k}
      = {l | ∃ k, s < Function.update c a (c a + 1) k + l.count k} := by
  ext l
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  refine exists_congr fun k => ?_
  by_cases hk : k = a
  · subst hk
    rw [Function.update_self, List.count_cons_self]
    omega
  · rw [Function.update_of_ne hk, List.count_cons_of_ne (Ne.symm hk)]





end Strategy

/-- The number of occurrences of k in the list of the draws is the number of draws that hit k. -/
theorem count_ofFn {L : Type} [DecidableEq L] {n : ℕ} (ω : Fin n → L) (k : L) :
    (List.ofFn ω).count k = hits ω k := by
  induction n with
  | zero => simp [hits]
  | succ n ih =>
    have h := hits_cons (ω 0) (fun i => ω i.succ) k
    rw [show (Fin.cons (ω 0) fun i => ω i.succ : Fin (n + 1) → L) = ω
        from Fin.cons_self_tail ω] at h
    rw [h, List.ofFn_succ, List.count_cons, ih, add_comm]
    simp

/-! ## 5. Monotonicity, the union-bound form and the closed form -/

theorem binTail_le_one {M : ℕ} (hM : 0 < M) (n s : ℕ) : binTail n M s ≤ 1 := hitTail_le_one hM n _

/-- For M > 0: more draws, a larger tail. -/
theorem binTail_mono {M : ℕ} (hM : 0 < M) (s : ℕ) : Monotone fun n => binTail n M s :=
  monotone_nat_of_le_succ fun n => hitTail_le_succ hM n (s + 1)

/-- A higher threshold: a smaller tail. -/
theorem binTail_anti (n M : ℕ) : Antitone fun s => binTail n M s :=
  fun _ _ h => hitTail_anti M n (Nat.succ_le_succ h)

/-- pOver grows with the number of draws. -/
theorem pOver_mono (M s : ℕ) : Monotone (pOver M s) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · intro a b _
    simp [pOver]
  · intro a b h
    exact mul_le_mul' le_rfl (binTail_mono hM s h)

/-- pOver falls when more draws are allowed per leaf. -/
theorem pOver_anti (M n : ℕ) : Antitone fun s => pOver M s n :=
  fun _ _ h => mul_le_mul' le_rfl (binTail_anti n M h)

/-- For M > 0, a fixed leaf is drawn more than s times with probability at most C(n, s+1) / M^(s+1):
the union bound over the sets of s + 1 draws. -/
theorem binTail_le_choose {M : ℕ} (hM : 0 < M) (n s : ℕ) :
    binTail n M s ≤ (n.choose (s + 1) : ℝ≥0∞) / (M : ℝ≥0∞) ^ (s + 1) := by
  unfold binTail hitTail
  rw [← Nat.cast_pow, ← Nat.cast_pow]
  exact natCast_div_le_div_of_pos
    (Nat.pow_pos hM) (Nat.pow_pos hM) (tailCount_mul_pow_le hM n (s + 1))

/-- The union-bound form: pOver M s n <= M * C(n, s+1) / M^(s+1). -/
theorem pOver_le_choose (M s n : ℕ) :
    pOver M s n ≤ (M : ℝ≥0∞) * ((n.choose (s + 1) : ℝ≥0∞) / (M : ℝ≥0∞) ^ (s + 1)) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [pOver]
  · exact mul_le_mul' le_rfl (binTail_le_choose hM n s)

/-- C(n, r) r^r <= e^r n^r, from C(n, r) <= n^r / r! and r^r / r! <= e^r. -/
theorem choose_mul_pow_le_exp (n r : ℕ) :
    (n.choose r : ℝ) * (r : ℝ) ^ r ≤ Real.exp 1 ^ r * (n : ℝ) ^ r := by
  have h1 : (n.choose r : ℝ) ≤ (n : ℝ) ^ r / (r.factorial : ℝ) := Nat.choose_le_pow_div r n
  have h2 : (r : ℝ) ^ r / (r.factorial : ℝ) ≤ Real.exp r :=
    Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg r) r
  have h3 : Real.exp r = Real.exp 1 ^ r := by rw [← Real.exp_nat_mul, mul_one]
  calc (n.choose r : ℝ) * (r : ℝ) ^ r ≤ (n : ℝ) ^ r / (r.factorial : ℝ) * (r : ℝ) ^ r := by gcongr
    _ = (n : ℝ) ^ r * ((r : ℝ) ^ r / (r.factorial : ℝ)) := by ring
    _ ≤ (n : ℝ) ^ r * Real.exp r := by gcongr
    _ = Real.exp 1 ^ r * (n : ℝ) ^ r := by rw [h3]; ring

/-- C(n, r) / M^r <= (e n / (r M))^r for r > 0, in ℝ≥0∞. -/
theorem choose_div_pow_le {r : ℕ} (hr : 0 < r) (M n : ℕ) :
    (n.choose r : ℝ≥0∞) / (M : ℝ≥0∞) ^ r
      ≤ (ENNReal.ofReal (Real.exp 1) * n / ((r : ℝ≥0∞) * M)) ^ r := by
  have hr0 : ((r : ℝ≥0∞) ^ r) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hr.ne')
  have hrt : ((r : ℝ≥0∞) ^ r) ≠ ∞ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top r)
  have key : (n.choose r : ℝ≥0∞) * (r : ℝ≥0∞) ^ r
      ≤ ENNReal.ofReal (Real.exp 1) ^ r * (n : ℝ≥0∞) ^ r := by
    have h := ENNReal.ofReal_le_ofReal (choose_mul_pow_le_exp n r)
    rwa [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_pow (Real.exp_pos 1).le,
      ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast] at h
  calc (n.choose r : ℝ≥0∞) / (M : ℝ≥0∞) ^ r
      = ((n.choose r : ℝ≥0∞) * (r : ℝ≥0∞) ^ r) / ((M : ℝ≥0∞) ^ r * (r : ℝ≥0∞) ^ r) :=
        (ENNReal.mul_div_mul_right _ _ hr0 hrt).symm
    _ ≤ (ENNReal.ofReal (Real.exp 1) ^ r * (n : ℝ≥0∞) ^ r) / ((M : ℝ≥0∞) ^ r * (r : ℝ≥0∞) ^ r) :=
        ENNReal.div_le_div_right key _
    _ = (ENNReal.ofReal (Real.exp 1) * n / ((r : ℝ≥0∞) * M)) ^ r := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow, mul_pow, ← ENNReal.inv_pow, mul_pow,
          mul_comm ((M : ℝ≥0∞) ^ r)]

/-- The closed expression M (e n / ((s+1) M))^(s+1). -/
def pOverClosed (M s n : ℕ) : ℝ≥0∞ :=
  (M : ℝ≥0∞) * (ENNReal.ofReal (Real.exp 1) * n / (((s + 1 : ℕ) : ℝ≥0∞) * M)) ^ (s + 1)

/-- The closed form: pOver M s n <= M (e n / ((s+1) M))^(s+1). -/
theorem pOver_le_closed (M s n : ℕ) : pOver M s n ≤ pOverClosed M s n :=
  (pOver_le_choose M s n).trans (mul_le_mul' le_rfl (choose_div_pow_le (Nat.succ_pos s) M n))


/-- For M > 0, the closed form as a real number, for figures. -/
theorem pOverClosed_eq_ofReal {M : ℕ} (hM : 0 < M) (s n : ℕ) :
    pOverClosed M s n
      = ENNReal.ofReal ((M : ℝ) * (Real.exp 1 * n / (((s : ℝ) + 1) * M)) ^ (s + 1)) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hs : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  unfold pOverClosed
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity)]
  simp [ENNReal.ofReal_natCast, ENNReal.ofReal_add]

/-! ## 6. pOver is not a probability: where it is above 1 and where below

pOver M s n is the expected number of leaves that are drawn more than s times. It never exceeds M.
For M > 0: it is at least 1 as soon as n > s M, where an overrun is certain; it can exceed 1
earlier, while an overrun is not yet certain (M = 4, s = 1, n = 4: pOver = 67/64, while four
different leaves may be drawn); and it is below 1 whenever the union-bound form is. Since pOver
grows with n, for fixed M > 0 and s there is one threshold in n, at most s M + 1; no closed form for
it is given. No statement of this file needs pOver <= 1. -/

theorem pOver_le_card (M s n : ℕ) : pOver M s n ≤ M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [pOver]
  · calc pOver M s n ≤ (M : ℝ≥0∞) * 1 := mul_le_mul' le_rfl (binTail_le_one hM n s)
      _ = M := mul_one _

theorem pOver_ne_top (M s n : ℕ) : pOver M s n ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top M) (pOver_le_card M s n)

/-- With at most s draws in all, no leaf can be drawn more than s times, and the bound is 0. -/
theorem pOver_eq_zero {s n : ℕ} (M : ℕ) (h : n ≤ s) : pOver M s n = 0 := by
  simp [pOver, binTail, hitTail_eq_zero (Nat.lt_succ_of_le h)]

/-- For M > 0 and n > s M, pOver is at least 1 (there an overrun is certain, by the pigeonhole
principle). -/
theorem one_le_pOver {M s n : ℕ} (hM : 0 < M) (h : s * M < n) : 1 ≤ pOver M s n := by
  have hp0 : ((M : ℝ≥0∞) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hM.ne')
  have hpt : ((M : ℝ≥0∞) ^ n) ≠ ∞ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top M)
  unfold pOver binTail hitTail
  rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hp0) (Or.inl hpt), one_mul]
  exact_mod_cast pow_le_mul_tailCount h

theorem pOver_four_one_four : pOver 4 1 4 = 67 / 64 := by
  have h : tailCount 4 4 2 = 67 := by decide
  unfold pOver binTail hitTail
  rw [h, ← mul_div_assoc]
  have e : ((4 : ℕ) : ℝ≥0∞) * ((67 : ℕ) : ℝ≥0∞) / ((4 : ℕ) : ℝ≥0∞) ^ 4
      = (67 * 4 : ℝ≥0∞) / (64 * 4 : ℝ≥0∞) := by
    congr 1 <;> norm_num
  rw [e, ENNReal.mul_div_mul_right _ _ (by norm_num) (by norm_num)]

/-- pOver passes 1 before an overrun is certain: 4 leaves, at most 1 draw each, 4 draws. -/
theorem one_lt_pOver_four_one_four : 1 < pOver 4 1 4 := by
  rw [pOver_four_one_four, ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  norm_num

/-- In the same example an overrun is not certain: four different leaves may be drawn. -/
theorem pr_overrun_four_one_four_lt_one :
    (PMF.uniformOfFintype (Fin 4 → Fin 4)).toOuterMeasure {ω | ∃ k, 1 < hits ω k} < 1 := by
  have hid : (id : Fin 4 → Fin 4) ∉
      Finset.univ.filter fun ω : Fin 4 → Fin 4 => ∃ k, 1 < hits ω k := by
    rw [Finset.mem_filter, not_and, not_exists]
    intro _ k
    have : hits (id : Fin 4 → Fin 4) k = 1 := by simp [hits, Finset.filter_eq']
    omega
  have hlt := Finset.card_lt_univ_of_notMem hid
  have hc : Fintype.card (Fin 4 → Fin 4) = 4 ^ 4 := by simp
  rw [hc] at hlt
  rw [pr_tape, Fintype.card_fin, ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num)),
    one_mul]
  exact_mod_cast hlt

/-- Where pOver is below 1: wherever the union-bound form is, that is if M * C(n, s+1) < M^(s+1). -/
theorem pOver_lt_one {M s n : ℕ} (h : M * n.choose (s + 1) < M ^ (s + 1)) : pOver M s n < 1 := by
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp at h
    · exact hM
  have hp0 : ((M : ℝ≥0∞) ^ (s + 1)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hM.ne')
  have hpt : ((M : ℝ≥0∞) ^ (s + 1)) ≠ ∞ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top M)
  refine (pOver_le_choose M s n).trans_lt ?_
  rw [← mul_div_assoc, ENNReal.div_lt_iff (Or.inl hp0) (Or.inl hpt), one_mul]
  exact_mod_cast h

/-! ## 7. The finite sum is the tail of the binomial distribution -/

theorem one_sub_inv_natCast {M : ℕ} (hM : 0 < M) :
    (1 : ℝ≥0∞) - (M : ℝ≥0∞)⁻¹ = ((M - 1 : ℕ) : ℝ≥0∞) * (M : ℝ≥0∞)⁻¹ := by
  have hM0 : (M : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hMt : (M : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top M
  have e : ((M - 1 : ℕ) : ℝ≥0∞) + 1 = M := by exact_mod_cast Nat.sub_add_cancel hM
  refine ENNReal.sub_eq_of_eq_add (ENNReal.inv_ne_top.2 hM0) ?_
  calc (1 : ℝ≥0∞) = (M : ℝ≥0∞) * (M : ℝ≥0∞)⁻¹ := (ENNReal.mul_inv_cancel hM0 hMt).symm
    _ = (((M - 1 : ℕ) : ℝ≥0∞) + 1) * (M : ℝ≥0∞)⁻¹ := by rw [e]
    _ = ((M - 1 : ℕ) : ℝ≥0∞) * (M : ℝ≥0∞)⁻¹ + (M : ℝ≥0∞)⁻¹ := by ring

/-- For M > 0, binTail in the usual notation: the sum over s < j <= n of C(n, j) p^j (1 - p)^(n -
j), with p = 1/M. -/
theorem binTail_eq_sum {M : ℕ} (hM : 0 < M) (n s : ℕ) :
    binTail n M s = ∑ j ∈ Finset.Ioc s n,
      (n.choose j : ℝ≥0∞) * ((M : ℝ≥0∞)⁻¹) ^ j * (1 - (M : ℝ≥0∞)⁻¹) ^ (n - j) := by
  have hI : Finset.Ico (s + 1) (n + 1) = Finset.Ioc s n := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  unfold binTail hitTail tailCount
  rw [hI, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j + (n - j) = n := by
    have := (Finset.mem_Ioc.1 hj).2
    omega
  have e : ((M : ℝ≥0∞) ^ n)⁻¹ = ((M : ℝ≥0∞)⁻¹) ^ j * ((M : ℝ≥0∞)⁻¹) ^ (n - j) := by
    rw [← pow_add, hjn, ENNReal.inv_pow]
  rw [one_sub_inv_natCast hM, mul_pow, e, tailTerm, Nat.cast_mul, Nat.cast_pow]
  ring

/-- binTail term by term, with the sum over s + 1 <= j <= n and each term divided by M^n. -/
theorem binTail_eq_sum_Icc (n M s : ℕ) :
    binTail n M s = ∑ j ∈ Finset.Icc (s + 1) n,
      (n.choose j : ℝ≥0∞) * ((M - 1 : ℕ) : ℝ≥0∞) ^ (n - j) / (M : ℝ≥0∞) ^ n := by
  have hI : Finset.Ico (s + 1) (n + 1) = Finset.Icc (s + 1) n := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  unfold binTail hitTail tailCount tailTerm
  rw [hI, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [Nat.cast_mul, Nat.cast_pow, div_eq_mul_inv]

/-- For M > 0, binTail n M s is Pr[Bin(n, 1/M) > s] for Mathlib's binomial distribution. -/
theorem binTail_eq_binomial {M : ℕ} (hM : 0 < M) (n s : ℕ) (h : ((M : ℝ≥0)⁻¹) ≤ 1) :
    binTail n M s = (PMF.binomial ((M : ℝ≥0)⁻¹) h n).toOuterMeasure {i | s < (i : ℕ)} := by
  have hc : (((M : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) = (M : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.coe_inv (Nat.cast_ne_zero.mpr hM.ne'), ENNReal.coe_natCast]
  have hF : Finset.Ioc s n = (Finset.range (n + 1)).filter fun j => s < j := by
    ext j
    simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_range]
    omega
  rw [binTail_eq_sum hM, PMF.toOuterMeasure_apply_fintype, hF, Finset.sum_filter,
    ← Fin.sum_univ_eq_sum_range (fun j => if s < j then
      (n.choose j : ℝ≥0∞) * ((M : ℝ≥0∞)⁻¹) ^ j * (1 - (M : ℝ≥0∞)⁻¹) ^ (n - j) else 0) (n + 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : s < (i : ℕ)
  · rw [if_pos hi, Set.indicator_of_mem (show i ∈ {i : Fin (n + 1) | s < (i : ℕ)} from hi),
      PMF.binomial_apply, hc, Fin.val_last]
    ring
  · rw [if_neg hi, Set.indicator_of_notMem (show i ∉ {i : Fin (n + 1) | s < (i : ℕ)} from hi)]

end Prob
