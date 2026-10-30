-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/DigitsLaw.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: the entries of
the array of digits (Johnson/Desc/K8/Honest/Window.lean: `digitAt`) lie in the digits' ranges AT
EVERY DRAWN MATRIX: every low digit is below 2^10, every high digit below 2^8; and where no
combination leaves its window the two give the combination back. Statements and proofs. LEMMAS ON
THE HONEST PROVER's ARRAY; NONE OF THE LIBRARY's GOALS.
THE TWO BOUNDS HOLD BECAUSE `low` AND `high` ARE DEFINED AS REMAINDERS: they do not say that a
combination outside its window has digits: by the format's page (docs/format/11-1-machinery.md) it
has none, and there the two entries do not give it back.

  `low_lt`            a low digit is below 2^10, at every integer
  `high_lt`           a high digit is below 2^8, at every integer
  `digits_back`       low + 2^10 * high - 2^17 is the integer, in the window
  `rowAt_spec`        the matrix and the row that `rowAt` finds
  `rowAt_lt_sum`, `rowAt_lt`   a row that `rowAt` finds is below the number of all rows of cells
  `rowAt_from`, **`rowAt_at`**   row i of matrix mu, counted through all matrices (the rows of the
                       matrices in front, and i), is found as (mu, i); the first: from a list whose
                       first matrix has the number mu₀: as (mu₀ + mu, i)
  `comb_beyond`       a matrix beyond the list of columns has the combinations 0
  `comb_inWindow`     where `leaves` finds nothing: every combination of a row that `rowAt` finds
                       lies in the window
  **`digitAt_lt`**    AT ALL CELLS AND EVERY DRAWN MATRIX: an entry in the first half of the
                       columns is below 2^10, every other entry below 2^8
  `digitAt_rows`, `digitAt_columns`   beyond the array's tau rows, and beyond its columns, the entry
                       is 0
  **`digitAt_back`**  where `leaves` finds nothing: in a row below tau the two entries of a row of
                       cells give its combination back
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.WindowLawProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes.Model (lbz t2D0 t2D1)

/-- A low digit is below 2^10, at every integer. -/
theorem low_lt (z : ℤ) : low z < 2 ^ t2D0 := by
  have hl : lbz = 17 := rfl
  have h0 : t2D0 = 10 := rfl
  unfold low
  rw [hl, h0]
  omega

/-- A high digit is below 2^8, at every integer. -/
theorem high_lt (z : ℤ) : high z < 2 ^ t2D1 := by
  have hl : lbz = 17 := rfl
  have h0 : t2D0 = 10 := rfl
  have h8 : t2D1 = 8 := OnBytes.Model.t2D1_eq
  unfold high
  rw [hl, h0, h8]
  omega

/-- In the window the two digits give the integer back. -/
theorem digits_back (z : ℤ) (h : inWindow z = true) :
    (low z : ℤ) + 2 ^ t2D0 * (high z : ℤ) - 2 ^ lbz = z := by
  obtain ⟨h1, h2⟩ := (inWindow_iff z).1 h
  have hl : lbz = 17 := rfl
  have h0 : t2D0 = 10 := rfl
  have h8 : t2D1 = 8 := OnBytes.Model.t2D1_eq
  unfold low high
  rw [hl] at h1 h2 ⊢
  rw [h0, h8]
  omega

/-- The matrix and the row that `rowAt` finds: counted from the list's first matrix, a matrix of
the list, and a row below its number of rows. -/
theorem rowAt_spec : ∀ (ms : List Nat) (mu₀ r mu i : Nat), rowAt ms mu₀ r = some (mu, i) →
    mu₀ ≤ mu ∧ mu - mu₀ < ms.length ∧ i < ms.getD (mu - mu₀) 0
  | [], _, _, _, _, h => by simp [rowAt] at h
  | m :: ms, mu₀, r, mu, i, h => by
    unfold rowAt at h
    split at h
    · next hr =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      simpa using hr
    · obtain ⟨a, b, c⟩ := rowAt_spec ms (mu₀ + 1) (r - m) mu i h
      have e : mu - mu₀ = (mu - (mu₀ + 1)) + 1 := by omega
      refine ⟨by omega, by rw [List.length_cons]; omega, ?_⟩
      rw [e, List.getD_cons_succ]
      exact c

/-- A row that `rowAt` finds is below the sum of the list. -/
theorem rowAt_lt_sum : ∀ (ms : List Nat) (mu₀ r mu i : Nat), rowAt ms mu₀ r = some (mu, i) →
    r < ms.sum
  | [], _, _, _, _, h => by simp [rowAt] at h
  | m :: ms, mu₀, r, mu, i, h => by
    unfold rowAt at h
    rw [List.sum_cons]
    split at h
    · next hr => omega
    · have := rowAt_lt_sum ms (mu₀ + 1) (r - m) mu i h
      omega

/-- A row that `rowAt` finds is below the number of all rows of cells. -/
theorem rowAt_lt (p : Par) (r mu i : Nat) (h : rowAt p.ms 0 r = some (mu, i)) : r < allRows p := by
  unfold allRows
  rw [foldl_add, Nat.zero_add]
  exact rowAt_lt_sum p.ms 0 r mu i h

/-- Row i of the list's matrix mu, counted from the list's first matrix on, is found as
(mu₀ + mu, i), mu₀ being the number given to the list's first matrix. -/
theorem rowAt_from : ∀ (ms : List ℕ) (μ₀ μ i : ℕ), μ < ms.length → i < ms.getD μ 0 →
    rowAt ms μ₀ ((ms.take μ).sum + i) = some (μ₀ + μ, i)
  | [], _, _, _, h, _ => by simp at h
  | m :: ms, μ₀, 0, i, _, hi => by
    have hi' : i < m := by simpa using hi
    simp [rowAt, hi']
  | m :: ms, μ₀, μ + 1, i, h, hi => by
    have h' : μ < ms.length := by simpa using h
    have hi' : i < ms.getD μ 0 := by simpa using hi
    have e := rowAt_from ms (μ₀ + 1) μ i h' hi'
    unfold rowAt
    rw [List.take_succ_cons, List.sum_cons, if_neg (by omega)]
    have e2 : m + (ms.take μ).sum + i - m = (ms.take μ).sum + i := by omega
    rw [e2, e]
    exact congrArg some (Prod.ext (by show μ₀ + 1 + μ = μ₀ + (μ + 1); omega) rfl)

/-- **Row i of matrix mu, counted through all matrices, is found as (mu, i).** -/
theorem rowAt_at (ms : List ℕ) (μ i : ℕ) (h : μ < ms.length) (hi : i < ms.getD μ 0) :
    rowAt ms 0 ((ms.take μ).sum + i) = some (μ, i) := by
  rw [rowAt_from ms 0 μ i h hi, Nat.zero_add]

/-- A matrix beyond the list of columns has the combinations 0. -/
theorem comb_beyond (p : Par) (cell : CellsAt) (d : Array Int) (mu i u : Nat)
    (h : p.ks.length ≤ mu) : comb p cell d mu i u = 0 := by
  unfold comb
  rw [List.getD_eq_default _ _ h]
  rfl

/-- Where the program finds nothing, every combination of a row that `rowAt` finds lies in the
window. -/
theorem comb_inWindow (p : Par) (cell : CellsAt) (d : Array Int) (h : leaves p cell d = none)
    (r mu i u : Nat) (hr : rowAt p.ms 0 r = some (mu, i)) (hu : u < p.tau) :
    inWindow (comb p cell d mu i u) = true := by
  obtain ⟨_, _, hi⟩ := rowAt_spec p.ms 0 r mu i hr
  by_cases hmu : mu < p.ks.length
  · exact (leaves_none_iff p cell d).1 h mu hmu i (by simpa using hi) u hu
  · rw [comb_beyond p cell d mu i u (by omega)]
    rfl

/-- **The array's entries lie in the digits' ranges, at all cells and every drawn matrix.** -/
theorem digitAt_lt (p : Par) (cell : CellsAt) (d : Array Int) (u col : Nat) :
    digitAt p cell d u col < if col < allRows p then 2 ^ t2D0 else 2 ^ t2D1 := by
  unfold digitAt
  by_cases hc : col < allRows p
  · simp only [hc, if_true]
    cases hr : rowAt p.ms 0 col with
    | none => exact Nat.two_pow_pos _
    | some x =>
      obtain ⟨mu, i⟩ := x
      show (if u < p.tau then low (comb p cell d mu i u) else 0) < 2 ^ t2D0
      split
      · exact low_lt _
      · exact Nat.two_pow_pos _
  · simp only [hc, if_false]
    cases hr : rowAt p.ms 0 (col - allRows p) with
    | none => exact Nat.two_pow_pos _
    | some x =>
      obtain ⟨mu, i⟩ := x
      show (if u < p.tau then high (comb p cell d mu i u) else 0) < 2 ^ t2D1
      split
      · exact high_lt _
      · exact Nat.two_pow_pos _

/-- Beyond the array's rows the entry is 0. -/
theorem digitAt_rows (p : Par) (cell : CellsAt) (d : Array Int) (u col : Nat) (h : p.tau ≤ u) :
    digitAt p cell d u col = 0 := by
  have hn : ¬ u < p.tau := by omega
  unfold digitAt
  simp only [hn, if_false]
  split <;> rfl

/-- Beyond the array's columns the entry is 0. -/
theorem digitAt_columns (p : Par) (cell : CellsAt) (d : Array Int) (u col : Nat)
    (h : 2 * allRows p ≤ col) : digitAt p cell d u col = 0 := by
  have hc : ¬ col < allRows p := by omega
  unfold digitAt
  simp only [hc, if_false]
  cases hr : rowAt p.ms 0 (col - allRows p) with
  | none => rfl
  | some x =>
    obtain ⟨mu, i⟩ := x
    have := rowAt_lt p _ mu i hr
    omega

/-- **Where no combination leaves its window the two entries of a row of cells give its combination
back.** r: a row of cells, counted through all matrices. -/
theorem digitAt_back (p : Par) (cell : CellsAt) (d : Array Int) (h : leaves p cell d = none)
    (u r mu i : Nat) (hu : u < p.tau) (hr : rowAt p.ms 0 r = some (mu, i)) :
    (digitAt p cell d u r : ℤ) + 2 ^ t2D0 * (digitAt p cell d u (allRows p + r) : ℤ) - 2 ^ lbz =
      comb p cell d mu i u := by
  have hw := comb_inWindow p cell d h r mu i u hr hu
  have hlt := rowAt_lt p r mu i hr
  have e1 : digitAt p cell d u r = low (comb p cell d mu i u) := by
    unfold digitAt
    simp only [hlt, hu, if_true, hr]
  have e2 : digitAt p cell d u (allRows p + r) = high (comb p cell d mu i u) := by
    unfold digitAt
    have hn : ¬ allRows p + r < allRows p := by omega
    simp only [hn, hu, if_true, if_false, Nat.add_sub_cancel_left, hr]
  rw [e1, e2]
  exact digits_back _ hw

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.rowAt_lt
#print axioms VerifiableInference.Desc.First.K8.Honest.rowAt_at
#print axioms VerifiableInference.Desc.First.K8.Honest.digitAt_rows
#print axioms VerifiableInference.Desc.First.K8.Honest.digitAt_columns
#print axioms VerifiableInference.Desc.First.K8.Honest.digitAt_lt
#print axioms VerifiableInference.Desc.First.K8.Honest.digitAt_back
