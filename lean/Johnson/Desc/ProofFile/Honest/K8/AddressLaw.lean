-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/AddressLaw.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: THE
COLUMNS AT WHICH THE VERIFIER READS A DIGIT ARE THE COLUMNS AT WHICH `digitAt` LAYS IT. Statements
and proofs, on public numbers alone. SMALL LEMMAS; NONE OF THE LIBRARY's GOALS.

The verifier's state of the test has a number of columns a half (`mz`) and each matrix's first
column (`off`); `digitAt` (Johnson/Desc/K8/Honest/Window.lean) counts the rows of cells through the
list of matrices. The library has a test with code that ties the first to the matrices' rows:
`DgP.colsTest` (OnBytes/Tie/Pv/Lookup/Digits/PortCols.lean): the matrices' first columns follow one
another from 0 on, and the last matrix ends at mz.

  `DigitColsFit tl`       that test says yes; there is a matrix; the list has as many as are counted
  `rows_take`        the rows of cells of the first mu matrices, in two spellings
  `off_take`         **a matrix's first column is the number of the rows of cells in front of it**
  `mz_allRows`       **tl.mz = allRows (parOfTail tl)**
  `zzCol_low`, `zzCol_high`   the verifier's two columns for row i of matrix mu
  `digitAt_low`, `digitAt_high`   **at these columns `digitAt` has the low and the high digit of
                      that row's combination**
Limits. That a state of the test passes `DgP.colsTest` is a premise: a fact on the plan's make: by
reading, the routine that lays the matrices (OnBytes/Model/Tail.lean: `shapeF`) makes it so. That
what it returns has `DigitColsFit` is said by no theorem: owed.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.Digits
import Johnson.Desc.K8.Honest.DigitsLaw
import OnBytes.Tie.Pv.Lookup.Digits.PortCols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.K8 (Par)
open VerifiableInference.Desc.First.K8.Honest

/-- The library's test on the digits' columns says yes; there is a matrix; the list has as many
matrices as are counted. -/
structure DigitColsFit (tl : HTailF2) : Prop where
  cols : DgP.colsTest tl = true
  pos : 0 < tl.NM
  nm : tl.NM = tl.mats.size

/-- An array's entry and its list's. -/
theorem arrayGetD_list {α : Type} (arr : Array α) (n : ℕ) (d : α) :
    arr.getD n d = arr.toList.getD n d := by
  cases arr
  simp

/-- The sum of the first n values of a list, in two spellings. -/
theorem takeSum_range {α : Type} (l : List α) (f : α → ℕ) (d : α) : ∀ n, n ≤ l.length →
    ((l.map f).take n).sum = ((List.range n).map fun ν => f (l.getD ν d)).sum
  | 0, _ => by simp
  | n + 1, h => by
    have hn : n < (l.map f).length := by rw [List.length_map]; omega
    rw [List.sum_take_succ _ n hn, takeSum_range l f d n (by omega), List.range_succ,
      List.map_append, List.sum_append]
    have hl : n < l.length := by omega
    simp [List.getElem?_eq_getElem hl]

/-- The rows of cells of the first mu matrices, in two spellings. -/
theorem rows_take (tl : HTailF2) (μ : ℕ) (h : μ ≤ tl.mats.size) :
    ((parOfTail tl).ms.take μ).sum = ((List.range μ).map fun ν => (tl.mats.getD ν {}).m).sum := by
  have e := takeSum_range tl.mats.toList (·.m) {} μ (by simpa using h)
  unfold parOfTail
  rw [e]
  exact congrArg List.sum (List.map_congr_left fun ν _ => by rw [arrayGetD_list])

/-- The library's test, matrix by matrix. -/
theorem off_range (tl : HTailF2) (hc : DgP.colsTest tl = true) : ∀ μ, μ < tl.NM →
    tl.off.getD μ 0 = ((List.range μ).map fun ν => (tl.mats.getD ν {}).m).sum := by
  unfold DgP.colsTest at hc
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc
  obtain ⟨h', h00⟩ := hc
  intro μ
  induction μ with
  | zero => exact fun _ => h00
  | succ n ih =>
    intro hn
    have e := h' n (by omega)
    rw [if_pos hn] at e
    have e' : tl.off.getD (n + 1) 0 = tl.off.getD n 0 + (tl.mats.getD n {}).m := e.symm
    rw [e', ih (by omega), List.range_succ, List.map_append, List.sum_append]
    simp

/-- **A matrix's first column among the digits is the number of the rows of cells in front of it.**
-/
theorem off_take (tl : HTailF2) (h : DigitColsFit tl) (μ : ℕ) (hμ : μ < tl.NM) :
    tl.off.getD μ 0 = ((parOfTail tl).ms.take μ).sum := by
  rw [off_range tl h.cols μ hμ, rows_take tl μ (by have := h.nm; omega)]

/-- **The digits' number of columns a half is the number of all rows of cells.** -/
theorem mz_allRows (tl : HTailF2) (h : DigitColsFit tl) : tl.mz = allRows (parOfTail tl) := by
  have hc := h.cols
  unfold DgP.colsTest at hc
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc
  obtain ⟨n, hn⟩ : ∃ n, tl.NM = n + 1 := ⟨tl.NM - 1, by have := h.pos; omega⟩
  have e := hc.1 n (by omega)
  rw [if_neg (by omega)] at e
  have e' : tl.mz = tl.off.getD n 0 + (tl.mats.getD n {}).m := e.symm
  have hall : allRows (parOfTail tl) = ((parOfTail tl).ms.take tl.mats.size).sum := by
    unfold allRows
    rw [VerifiableInference.Desc.First.K8.foldl_add, Nat.zero_add, List.take_of_length_le]
    simp [parOfTail]
  rw [hall, rows_take tl _ (Nat.le_refl _), ← h.nm, hn, List.range_succ, List.map_append,
    List.sum_append, e', off_range tl h.cols n (by omega)]
  simp

/-- The place's rows of cells of matrix mu are the state's. -/
theorem ms_getD (tl : HTailF2) (μ : ℕ) (h : μ < tl.mats.size) :
    (parOfTail tl).ms.getD μ 0 = (tl.mats.getD μ {}).m := by
  simp [parOfTail, Array.getElem?_eq_getElem h]

/-- The verifier's column for the low digit of row i of matrix mu. -/
theorem zzCol_low (tl : HTailF2) (h : DigitColsFit tl) (μ i : ℕ) (hμ : μ < tl.NM)
    (hi : i < (tl.mats.getD μ {}).m) :
    (tl.zzCol μ 0 0).getD 0 + i = ((parOfTail tl).ms.take μ).sum + i := by
  have h0 : 0 < (tl.mats.getD μ {}).m := by omega
  have hb : (decide (μ < tl.NM) && decide (0 ≤ 1) && decide (0 < (tl.mats.getD μ {}).m)) =
      true := by
    rw [decide_eq_true hμ, decide_eq_true (Nat.zero_le 1), decide_eq_true h0]
    rfl
  unfold HTailF2.zzCol
  rw [if_pos hb, Option.getD_some, off_take tl h μ hμ]
  omega

/-- The verifier's column for the high digit of row i of matrix mu. -/
theorem zzCol_high (tl : HTailF2) (h : DigitColsFit tl) (μ i : ℕ) (hμ : μ < tl.NM)
    (hi : i < (tl.mats.getD μ {}).m) :
    (tl.zzCol μ 1 0).getD 0 + i =
      allRows (parOfTail tl) + (((parOfTail tl).ms.take μ).sum + i) := by
  have h0 : 0 < (tl.mats.getD μ {}).m := by omega
  have hb : (decide (μ < tl.NM) && decide (1 ≤ 1) && decide (0 < (tl.mats.getD μ {}).m)) =
      true := by
    rw [decide_eq_true hμ, decide_eq_true (Nat.le_refl 1), decide_eq_true h0]
    rfl
  unfold HTailF2.zzCol
  rw [if_pos hb, Option.getD_some, off_take tl h μ hμ, mz_allRows tl h]
  omega

/-- **At the verifier's column for it `digitAt` has the low digit of the row's combination.** -/
theorem digitAt_low (tl : HTailF2) (h : DigitColsFit tl) (a : CellsAt) (d : Array Int) (μ u i : ℕ)
    (hμ : μ < tl.NM) (hu : u < tl.tau) (hi : i < (tl.mats.getD μ {}).m) :
    digitAt (parOfTail tl) a d u ((tl.zzCol μ 0 0).getD 0 + i) =
      low (comb (parOfTail tl) a d μ i u) := by
  have hs : μ < tl.mats.size := h.nm ▸ hμ
  have hr := rowAt_at (parOfTail tl).ms μ i (by simpa [parOfTail] using hs)
    (by rw [ms_getD tl μ hs]; exact hi)
  have hlt := rowAt_lt (parOfTail tl) _ μ i hr
  have hu' : u < (parOfTail tl).tau := hu
  rw [zzCol_low tl h μ i hμ hi]
  unfold digitAt
  simp only [hlt, hu', if_true, hr]

/-- **The like for the high digit.** -/
theorem digitAt_high (tl : HTailF2) (h : DigitColsFit tl) (a : CellsAt) (d : Array Int) (μ u i : ℕ)
    (hμ : μ < tl.NM) (hu : u < tl.tau) (hi : i < (tl.mats.getD μ {}).m) :
    digitAt (parOfTail tl) a d u ((tl.zzCol μ 1 0).getD 0 + i) =
      high (comb (parOfTail tl) a d μ i u) := by
  have hs : μ < tl.mats.size := h.nm ▸ hμ
  have hr := rowAt_at (parOfTail tl).ms μ i (by simpa [parOfTail] using hs)
    (by rw [ms_getD tl μ hs]; exact hi)
  have hu' : u < (parOfTail tl).tau := hu
  have hn : ¬ allRows (parOfTail tl) + (((parOfTail tl).ms.take μ).sum + i) <
      allRows (parOfTail tl) := by omega
  rw [zzCol_high tl h μ i hμ hi]
  unfold digitAt
  simp only [hn, hu', if_true, if_false, Nat.add_sub_cancel_left, hr]

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.off_range
#print axioms ProofFile.Honest.K8.ms_getD
#print axioms ProofFile.Honest.K8.zzCol_low
#print axioms ProofFile.Honest.K8.zzCol_high
#print axioms ProofFile.Honest.K8.off_take
#print axioms ProofFile.Honest.K8.mz_allRows
#print axioms ProofFile.Honest.K8.digitAt_low
#print axioms ProofFile.Honest.K8.digitAt_high
#print axioms ProofFile.Honest.K8.DigitColsFit
#print axioms ProofFile.Honest.K8.arrayGetD_list
#print axioms ProofFile.Honest.K8.takeSum_range
#print axioms ProofFile.Honest.K8.rows_take
