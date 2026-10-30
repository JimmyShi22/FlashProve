-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/Ends.lean: a smallness test (its mathematics: Alg/Range.lean) has two kinds of
equations: one for each matrix, row of symbols and combination (a tie), and one for each read and
combination. The verifier (OnBytes/Model/Tail.lean) adds them up, each under its own power of the
batching element. This file writes such a sum out as one linear form in the entries (the digits, the
symbols, a read's values: parameters here), and defines the exponents (`eTie`, `eRead`).
States. `tie_batch`, `read_batch`: the sum of a matrix's equations of the first kind, and of a
read's equations, under any weights, is the linear form with the coefficients `cTie`, `cSym`,
`cTie0`, and `cRead`, `cTab`, `cRead0`.
 - `eTie_inj`, `eRead_inj`, `eTie_lt_eRead`: no two equations have the same exponent.
 - `le_eTie`, `eRead_lt`: an exponent of the first kind is at least pc (a parameter; in use, the
   number of claims in the sub-proof's plan); with n reads, a read's exponent is below pc plus the
   number of indices.
Under. The two sums: no premise (0), over any commutative ring. The exponents: only that each index
(matrix, row of symbols, combination, read) is below its number.
Does not show.
 1. Nothing here names a routine of the verifier: that its claims have these coefficients and these
    exponents is compared by runs at small sizes, and is no theorem.
 2. The weights are parameters: that they are powers of one element is used nowhere.
 3. Nothing is said on who else writes on the rows that the two kinds of equations use.
Notes in full, with every limit at length, stand at the end of this file.

-/
import Alg.Range
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open Finset

/-! ## 1. A weighted sum of packings -/

section Algebra

variable {K : Type} [CommRing K]

/-- A sum over three times n numbers, three by three. -/
theorem sum_three (f : ℕ → K) : ∀ n : ℕ,
    ∑ x ∈ range (3 * n), f x = ∑ j ∈ range n, (f (3 * j) + f (3 * j + 1) + f (3 * j + 2))
  | 0 => by simp
  | n + 1 => by
      rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
        sum_range_succ, sum_three f n, sum_range_succ]
      ring

/-- A column, continued by 0. -/
def ext0 {m : ℕ} (a : Fin m → K) (n : ℕ) : K := if h : n < m then a ⟨n, h⟩ else 0

/-- A weighted sum of the packings of a column, as a weighted sum of its cells. -/
theorem packW (rad : ℤ) {m : ℕ} (y : ℕ → K) (a : Fin m → K) :
    ∑ i' : Fin (Alg.symRows m), y i' * Alg.pack rad a i' =
      ∑ i : Fin m, y ((i : ℕ) / 3) * (rad : K) ^ ((i : ℕ) % 3) * a i := by
  have hR : ∑ i : Fin m, y ((i : ℕ) / 3) * (rad : K) ^ ((i : ℕ) % 3) * a i =
      ∑ n ∈ range m, y (n / 3) * (rad : K) ^ (n % 3) * ext0 a n := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => y (n / 3) * (rad : K) ^ (n % 3) * ext0 a n) m]
    refine sum_congr rfl fun i _ => ?_
    rw [ext0, dif_pos i.2]
  have hle : m ≤ 3 * Alg.symRows m := by
    unfold Alg.symRows
    omega
  have hX : ∑ n ∈ range m, y (n / 3) * (rad : K) ^ (n % 3) * ext0 a n =
      ∑ n ∈ range (3 * Alg.symRows m), y (n / 3) * (rad : K) ^ (n % 3) * ext0 a n := by
    refine sum_subset (range_subset_range.2 hle) fun n _ hn => ?_
    rw [ext0, dif_neg (fun h => hn (mem_range.2 h)), mul_zero]
  rw [hR, hX, sum_three,
    Fin.sum_univ_eq_sum_range (fun j => y j * Alg.pack rad a j) (Alg.symRows m)]
  refine sum_congr rfl fun j _ => ?_
  have d0 : 3 * j / 3 = j := by omega
  have d1 : (3 * j + 1) / 3 = j := by omega
  have d2 : (3 * j + 2) / 3 = j := by omega
  have m0 : 3 * j % 3 = 0 := by omega
  have m1 : (3 * j + 1) % 3 = 1 := by omega
  have m2 : (3 * j + 2) % 3 = 2 := by omega
  rw [d0, d1, d2, m0, m1, m2]
  have l0 : Alg.lane a j 0 = ext0 a (3 * j) := rfl
  have l1 : Alg.lane a j 1 = ext0 a (3 * j + 1) := rfl
  have l2 : Alg.lane a j 2 = ext0 a (3 * j + 2) := rfl
  unfold Alg.pack
  rw [l0, l1, l2]
  ring

/-! ## 2. The sum of a matrix's ties, and of a read's equations -/

variable {m k tau : ℕ}

/-- A single tie, right side less left side: the packing of the combination that the digits give,
less the combination of the symbols. th: the drawn entries. -/
def tieGap (rad : ℤ) (lo beta : K) (th : Fin tau → Fin k → K)
    (sym : Fin (Alg.symRows m) → Fin k → K) (zl zh : Fin tau → Fin m → K) (u : Fin tau)
    (i' : Fin (Alg.symRows m)) : K :=
  Alg.pack rad (fun i => zl u i + lo * zh u i - beta) i' - ∑ c, th u c * sym i' c

/-- A single equation of a read, right side less left side. w: the read's weights on the rows of
cells; tab: its committed values, one for each column. -/
def readGap (lo beta : K) (th : Fin tau → Fin k → K) (w : ℕ → K) (tab : Fin k → K)
    (zl zh : Fin tau → Fin m → K) (u : Fin tau) : K :=
  ∑ i : Fin m, w i * (zl u i + lo * zh u i - beta) - ∑ c, th u c * tab c

/-- The coefficient of the low digit of combination u and row i of cells in the sum of the ties
under the weights P (row of symbols, combination). -/
def cTie (rad : ℤ) (P : ℕ → ℕ → K) (u i : ℕ) : K := P (i / 3) u * (rad : K) ^ (i % 3)

/-- The coefficient of the symbol in row i' of symbols and column c. -/
def cSym (P : ℕ → ℕ → K) (th : Fin tau → Fin k → K) (i' : ℕ) (c : Fin k) : K :=
  -∑ u : Fin tau, P i' u * th u c

/-- The constant. -/
def cTie0 (m tau : ℕ) (rad : ℤ) (beta : K) (P : ℕ → ℕ → K) : K :=
  -(beta * ∑ u : Fin tau, ∑ i : Fin m, cTie rad P u i)

/-- The sum of a matrix's ties under any weights, as a linear form in the digits and the symbols. -/
theorem tie_batch (rad : ℤ) (lo beta : K) (P : ℕ → ℕ → K) (th : Fin tau → Fin k → K)
    (sym : Fin (Alg.symRows m) → Fin k → K) (zl zh : Fin tau → Fin m → K) :
    ∑ i' : Fin (Alg.symRows m), ∑ u : Fin tau, P i' u * tieGap rad lo beta th sym zl zh u i' =
      ∑ u : Fin tau, ∑ i : Fin m, cTie rad P u i * zl u i +
        ∑ u : Fin tau, ∑ i : Fin m, lo * cTie rad P u i * zh u i +
        ∑ i' : Fin (Alg.symRows m), ∑ c, cSym P th i' c * sym i' c + cTie0 m tau rad beta P := by
  have h1 : ∀ u : Fin tau,
      ∑ i' : Fin (Alg.symRows m),
          P i' u * Alg.pack rad (fun i => zl u i + lo * zh u i - beta) i' =
        ∑ i : Fin m, cTie rad P u i * zl u i + ∑ i : Fin m, lo * cTie rad P u i * zh u i -
          beta * ∑ i : Fin m, cTie rad P u i := by
    intro u
    rw [packW rad (fun i' => P i' u), mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    unfold cTie
    ring
  have h2 : ∀ i' : Fin (Alg.symRows m),
      ∑ u : Fin tau, P i' u * ∑ c, th u c * sym i' c =
        ∑ c, (∑ u : Fin tau, P i' u * th u c) * sym i' c := by
    intro i'
    simp only [mul_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun c _ => sum_congr rfl fun u _ => by ring
  have hA : ∑ i' : Fin (Alg.symRows m), ∑ u : Fin tau,
        P i' u * Alg.pack rad (fun i => zl u i + lo * zh u i - beta) i' =
      ∑ u : Fin tau, ∑ i : Fin m, cTie rad P u i * zl u i +
        ∑ u : Fin tau, ∑ i : Fin m, lo * cTie rad P u i * zh u i -
        beta * ∑ u : Fin tau, ∑ i : Fin m, cTie rad P u i := by
    rw [sum_comm, sum_congr rfl fun u _ => h1 u, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  have hB : ∑ i' : Fin (Alg.symRows m), ∑ u : Fin tau, P i' u * ∑ c, th u c * sym i' c =
      ∑ i' : Fin (Alg.symRows m), ∑ c, (∑ u : Fin tau, P i' u * th u c) * sym i' c :=
    sum_congr rfl fun i' _ => h2 i'
  have hS : ∑ i' : Fin (Alg.symRows m), ∑ u : Fin tau,
        P i' u * tieGap rad lo beta th sym zl zh u i' =
      ∑ i' : Fin (Alg.symRows m), ∑ u : Fin tau,
          P i' u * Alg.pack rad (fun i => zl u i + lo * zh u i - beta) i' -
        ∑ i' : Fin (Alg.symRows m), ∑ u : Fin tau, P i' u * ∑ c, th u c * sym i' c := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i' _ => ?_
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun u _ => mul_sub _ _ _
  rw [hS, hA, hB]
  unfold cSym cTie0
  simp only [neg_mul, sum_neg_distrib]
  ring

/-- The coefficient of the low digit of combination u and row i of cells in the sum of a read's
equations under the weights Q. -/
def cRead (Q w : ℕ → K) (u i : ℕ) : K := Q u * w i

/-- The coefficient of the read's committed value at column c. -/
def cTab (Q : ℕ → K) (th : Fin tau → Fin k → K) (c : Fin k) : K := -∑ u : Fin tau, Q u * th u c

/-- The constant. -/
def cRead0 (m tau : ℕ) (beta : K) (Q w : ℕ → K) : K :=
  -(beta * ∑ u : Fin tau, ∑ i : Fin m, cRead Q w u i)

/-- The sum of a read's equations under any weights, as a linear form in the digits and the read's
committed values. -/
theorem read_batch (lo beta : K) (Q : ℕ → K) (th : Fin tau → Fin k → K) (w : ℕ → K)
    (tab : Fin k → K) (zl zh : Fin tau → Fin m → K) :
    ∑ u : Fin tau, Q u * readGap lo beta th w tab zl zh u =
      ∑ u : Fin tau, ∑ i : Fin m, cRead Q w u i * zl u i +
        ∑ u : Fin tau, ∑ i : Fin m, lo * cRead Q w u i * zh u i +
        ∑ c, cTab Q th c * tab c + cRead0 m tau beta Q w := by
  have h1 : ∀ u : Fin tau, Q u * ∑ i : Fin m, w i * (zl u i + lo * zh u i - beta) =
      ∑ i : Fin m, cRead Q w u i * zl u i + ∑ i : Fin m, lo * cRead Q w u i * zh u i -
        beta * ∑ i : Fin m, cRead Q w u i := by
    intro u
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    unfold cRead
    ring
  have h2 : ∑ u : Fin tau, Q u * ∑ c, th u c * tab c =
      ∑ c, (∑ u : Fin tau, Q u * th u c) * tab c := by
    simp only [mul_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun c _ => sum_congr rfl fun u _ => by ring
  have hS : ∑ u : Fin tau, Q u * readGap lo beta th w tab zl zh u =
      ∑ u : Fin tau, Q u * ∑ i : Fin m, w i * (zl u i + lo * zh u i - beta) -
        ∑ u : Fin tau, Q u * ∑ c, th u c * tab c := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun u _ => mul_sub _ _ _
  rw [hS, h2, sum_congr rfl fun u _ => h1 u, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  unfold cTab cRead0
  simp only [neg_mul, sum_neg_distrib]
  ring

end Algebra

/-! ## 3. The exponents -/

/-- tau rounded up to a power of two: how many consecutive indices a row of symbols, or a read, is
given. -/
def step (tau : ℕ) : ℕ := 2 ^ Nat.clog 2 tau

/-- The number of indices that a matrix with m rows of cells is given. -/
def span (tau m : ℕ) : ℕ := step tau * 2 ^ Nat.clog 2 (Alg.symRows m)

/-- The first index of matrix μ: the indices of the matrices before it. -/
def eqF (tau : ℕ) (m : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | μ + 1 => eqF tau m μ + span tau (m μ)

/-- The exponent of the tie of matrix μ, row i' of symbols, combination u. -/
def eTie (pc tau : ℕ) (m : ℕ → ℕ) (μ i' u : ℕ) : ℕ := pc + eqF tau m μ + i' * step tau + u

/-- The exponent of combination u of read number q, with NM matrices. -/
def eRead (pc tau : ℕ) (m : ℕ → ℕ) (NM q u : ℕ) : ℕ := pc + eqF tau m NM + q * step tau + u

theorem le_step (tau : ℕ) : tau ≤ step tau := Nat.le_pow_clog (by norm_num) tau

theorem eqF_mono (tau : ℕ) (m : ℕ → ℕ) {μ ν : ℕ} (h : μ ≤ ν) : eqF tau m μ ≤ eqF tau m ν := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (Nat.le_add_right _ _)

/-- An index inside a matrix is below the number of the matrix's indices. -/
theorem in_span {tau m i' u : ℕ} (hi : i' < Alg.symRows m) (hu : u < tau) :
    i' * step tau + u < span tau m := by
  have h1 : u < step tau := lt_of_lt_of_le hu (le_step tau)
  have h2 : i' + 1 ≤ 2 ^ Nat.clog 2 (Alg.symRows m) :=
    le_trans hi (Nat.le_pow_clog (by norm_num) _)
  calc i' * step tau + u < i' * step tau + step tau := Nat.add_lt_add_left h1 _
    _ = (i' + 1) * step tau := (Nat.succ_mul _ _).symm
    _ ≤ 2 ^ Nat.clog 2 (Alg.symRows m) * step tau := Nat.mul_le_mul_right _ h2
    _ = span tau m := Nat.mul_comm _ _

/-- Two numbers below the step, under multiples of the step. -/
theorem step_split {s a u b v : ℕ} (hu : u < s) (hv : v < s) (h : a * s + u = b * s + v) :
    a = b ∧ u = v := by
  have hs : 0 < s := lt_of_le_of_lt (Nat.zero_le _) hu
  have e1 : (a * s + u) / s = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt hu, Nat.zero_add]
  have e2 : (b * s + v) / s = b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt hv, Nat.zero_add]
  have hab : a = b := by rw [← e1, ← e2, h]
  subst hab
  exact ⟨rfl, Nat.add_left_cancel h⟩

/-- The ties of an earlier matrix have smaller exponents than those of a later one. -/
theorem eTie_lt_of_lt (pc tau : ℕ) (m : ℕ → ℕ) {μ ν i' u j v : ℕ} (h : μ < ν)
    (hi : i' < Alg.symRows (m μ)) (hu : u < tau) : eTie pc tau m μ i' u < eTie pc tau m ν j v := by
  have h1 := in_span hi hu
  have h2 : eqF tau m (μ + 1) ≤ eqF tau m ν := eqF_mono tau m h
  have h3 : eqF tau m (μ + 1) = eqF tau m μ + span tau (m μ) := rfl
  unfold eTie
  omega

/-- No two ties have the same exponent. -/
theorem eTie_inj (pc tau : ℕ) (m : ℕ → ℕ) {μ i' u ν j v : ℕ} (hi : i' < Alg.symRows (m μ))
    (hu : u < tau) (hj : j < Alg.symRows (m ν)) (hv : v < tau)
    (h : eTie pc tau m μ i' u = eTie pc tau m ν j v) : μ = ν ∧ i' = j ∧ u = v := by
  rcases Nat.lt_trichotomy μ ν with hl | he | hg
  · exact absurd h (ne_of_lt (eTie_lt_of_lt pc tau m hl hi hu))
  · subst he
    have h' : i' * step tau + u = j * step tau + v := by
      unfold eTie at h
      omega
    exact ⟨rfl, step_split (lt_of_lt_of_le hu (le_step tau)) (lt_of_lt_of_le hv (le_step tau)) h'⟩
  · exact absurd h.symm (ne_of_lt (eTie_lt_of_lt pc tau m hg hj hv))

/-- No two equations of reads have the same exponent. -/
theorem eRead_inj (pc tau : ℕ) (m : ℕ → ℕ) (NM : ℕ) {q u r v : ℕ} (hu : u < tau) (hv : v < tau)
    (h : eRead pc tau m NM q u = eRead pc tau m NM r v) : q = r ∧ u = v := by
  have h' : q * step tau + u = r * step tau + v := by
    unfold eRead at h
    omega
  exact step_split (lt_of_lt_of_le hu (le_step tau)) (lt_of_lt_of_le hv (le_step tau)) h'

/-- Every tie's exponent is below every read's. -/
theorem eTie_lt_eRead (pc tau : ℕ) (m : ℕ → ℕ) {NM μ i' u : ℕ} (q v : ℕ) (hμ : μ < NM)
    (hi : i' < Alg.symRows (m μ)) (hu : u < tau) :
    eTie pc tau m μ i' u < eRead pc tau m NM q v := by
  have h1 := in_span hi hu
  have h2 : eqF tau m (μ + 1) ≤ eqF tau m NM := eqF_mono tau m hμ
  have h3 : eqF tau m (μ + 1) = eqF tau m μ + span tau (m μ) := rfl
  unfold eTie eRead
  omega

/-- Every tie's exponent is below pc plus the first index behind the matrices. -/
theorem eTie_lt (pc tau : ℕ) (m : ℕ → ℕ) {NM μ i' u : ℕ} (hμ : μ < NM)
    (hi : i' < Alg.symRows (m μ)) (hu : u < tau) : eTie pc tau m μ i' u < pc + eqF tau m NM := by
  have h := eTie_lt_eRead pc tau m 0 0 hμ hi hu
  unfold eRead at h
  omega

/-- Every tie's exponent is at least pc. -/
theorem le_eTie (pc tau : ℕ) (m : ℕ → ℕ) (μ i' u : ℕ) : pc ≤ eTie pc tau m μ i' u := by
  unfold eTie
  omega

/-- With n reads, every exponent of a read is below pc plus the number of indices. -/
theorem eRead_lt (pc tau : ℕ) (m : ℕ → ℕ) (NM : ℕ) {n q u : ℕ} (hq : q < n) (hu : u < tau) :
    eRead pc tau m NM q u < pc + (eqF tau m NM + n * step tau) := by
  have h1 : u < step tau := lt_of_lt_of_le hu (le_step tau)
  have h2 : (q + 1) * step tau ≤ n * step tau := Nat.mul_le_mul_right _ hq
  have h3 : (q + 1) * step tau = q * step tau + step tau := Nat.succ_mul _ _
  unfold eRead
  omega

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.packW
#print axioms OnBytes.Tie.Pv.Tail.tie_batch
#print axioms OnBytes.Tie.Pv.Tail.read_batch
#print axioms OnBytes.Tie.Pv.Tail.eTie_inj
#print axioms OnBytes.Tie.Pv.Tail.eRead_inj
#print axioms OnBytes.Tie.Pv.Tail.eTie_lt_eRead
#print axioms OnBytes.Tie.Pv.Tail.eRead_lt

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/Tie/Pv/Tail/Ends.lean: the equations of a smallness test, added up under weights, as one
linear form in the committed entries; and the exponents under which the verifier adds them up.

Definitions, statements and proofs. A smallness test (its mathematics: Alg/Range.lean) has one
equation for each matrix, row of symbols and combination (a tie) and one for each read and
combination. The verifier in OnBytes/Model/Tail.lean never forms a single equation. It adds one
claim for each matrix and one for each read, and each claim is a sum of single equations, each under
its own power of the batching element. Here the sum is written out, for any weights: each committed
entry gets one closed coefficient. OnBytes/Tie/Pv/Tail/TestEnds.lean compares these coefficients,
entry by entry, with what the verifier's own routines leave at small sizes.

Main names:
  `packW`: a weighted sum of the packings of a column is a weighted sum of its cells: cell i has
    the weight of row i / 3 of symbols times the radix to the power i % 3.
  `tieGap`, `readGap`: a single tie and a single read, right side less left side.
  `cTie`, `cSym`, `cTie0`: the coefficient of a low digit, of a symbol, and the constant, in the sum
    of a matrix's ties under the weights P; a high digit has lo times that of its low digit.
  `cRead`, `cTab`, `cRead0`: the same for the sum of a read's equations under the weights Q.
  `tie_batch`, `read_batch`: the two sums are these linear forms. For all weights.
  `step`, `span`, `eqF`, `eTie`, `eRead`: the exponents: tau and each matrix's number of rows of
    symbols are rounded up to powers of two; pc is the number of claims in the sub-proof's plan.
  `eTie_inj`, `eRead_inj`, `eTie_lt_eRead`, `le_eTie`, `eTie_lt`, `eRead_lt`: no two equations have
    the same exponent, and all exponents lie from pc on and below pc plus the number of indices.

Limits: nothing here names a routine of the verifier: that its claims have these coefficients and
these exponents is compared by runs at small sizes, and is no theorem. The weights are letters: that
they are powers of one element is used nowhere. Nothing is said on who else writes on the rows that
the ties and the reads use.
-/
