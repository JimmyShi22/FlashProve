-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/First.lean: the running sums of columns that the Lean verifier keeps with the
drawn matrix of a smallness test are the numbers firstCol of the typed sizes.

When the verifier draws the matrix it also stores, for each matrix of the test, the index of that
matrix's first column among the columns of all matrices (the field cfFirst, set by drawMatrixF,
OnBytes/Model/Tail.lean): it walks the list of matrices and pushes the last number plus the
matrix's number of columns. foldSums reads the drawn list at (cfFirst[mu] + c) * tau + u. This file
says what that walk gives. Statements and proofs.

Main names:
  `walk_size`, `nm_of_walk`: the walk adds one entry for each matrix; so the verifier's test, at the
    draw, that the walk from the array that holds 0 alone has NM + 1 entries says that the
    record's number of matrices is the length of its list.
  `walk_keeps`: the walk leaves what stood in the array.
  `walk_get`: after the walk, the entry i places behind the last old entry is that entry plus the
    columns of the first i matrices.
  `sum_take`: the columns of the first i matrices, as a finite sum.
  `cfFirst_eq`: if the record's number of matrices is the length of its list, entry μ of the walk
    from the array that holds 0 alone is firstCol (sizeOf tl).size μ.

Limits: the walk is written out here as drawMatrixF has it; that the record's field cfFirst holds
its result after a run of drawMatrixF is read off the text and not proved here.
-/
import OnBytes.Tie.Pv.Tail.SizeOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open OnBytes OnBytes.Model Cb.Pv.Tail

/-- One step of the walk. -/
def walkStep (a : Array Nat) (M : TMat) : Array Nat := a.push (a.getD (a.size - 1) 0 + M.k)

/-- The walk adds one entry for each matrix. -/
theorem walk_size : ∀ (l : List TMat) (a : Array Nat),
    (l.foldl walkStep a).size = a.size + l.length
  | [], _ => rfl
  | M :: l, a => by
    rw [List.foldl_cons, walk_size l (walkStep a M), List.length_cons]
    simp only [walkStep, Array.size_push]
    omega

/-- What the verifier's test at the draw says of the record. -/
theorem nm_of_walk (tl : HTailF2)
    (h : (tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0]).size =
      tl.NM + 1) : tl.NM = tl.mats.size := by
  rw [← Array.foldl_toList] at h
  have hw := walk_size tl.mats.toList #[0]
  have h' : (tl.mats.toList.foldl walkStep #[0]).size = tl.NM + 1 := h
  rw [hw] at h'
  simp only [Array.length_toList] at h'
  have h1 : (#[0] : Array Nat).size = 1 := rfl
  omega

/-- The walk leaves what stood in the array. -/
theorem walk_keeps : ∀ (l : List TMat) (a : Array Nat) (j : ℕ), j < a.size →
    (l.foldl walkStep a).getD j 0 = a.getD j 0
  | [], _, _, _ => rfl
  | M :: l, a, j, hj => by
    rw [List.foldl_cons, walk_keeps l (walkStep a M) j (by simp [walkStep]; omega)]
    simp only [walkStep, Array.getD_eq_getD_getElem?, Array.getElem?_push]
    rw [if_neg (by omega)]

/-- After the walk: the entry i places behind the last old entry. -/
theorem walk_get : ∀ (l : List TMat) (a : Array Nat) (i : ℕ), 1 ≤ a.size → i ≤ l.length →
    (l.foldl walkStep a).getD (a.size - 1 + i) 0 =
      a.getD (a.size - 1) 0 + ((l.take i).map (·.k)).sum
  | [], a, i, _, hi => by
    have h0 : i = 0 := by simpa using hi
    subst h0
    simp
  | M :: l, a, 0, ha, _ => by
    rw [Nat.add_zero, walk_keeps (M :: l) a (a.size - 1) (by omega)]
    simp
  | M :: l, a, i + 1, ha, hi => by
    have hs : (walkStep a M).size = a.size + 1 := by simp [walkStep]
    have h := walk_get l (walkStep a M) i (by omega) (by simpa using hi)
    rw [hs, Nat.add_sub_cancel] at h
    rw [List.foldl_cons, show a.size - 1 + (i + 1) = a.size + i by omega, h]
    have hx : (walkStep a M).getD a.size 0 = a.getD (a.size - 1) 0 + M.k := by
      simp [walkStep, Array.getD_eq_getD_getElem?]
    rw [hx, List.take_succ_cons, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- The columns of the first i matrices, as a finite sum. -/
theorem sum_take (l : List TMat) (i : ℕ) (hi : i ≤ l.length) :
    ((l.take i).map (·.k)).sum = ∑ ν ∈ Finset.range i, (l.getD ν {}).k := by
  rw [← sum_range_getD (fun M : TMat => M.k) {} (l.take i), List.length_take, Nat.min_eq_left hi]
  refine Finset.sum_congr rfl fun ν hν => ?_
  have hlt : ν < i := Finset.mem_range.1 hν
  simp [List.getD_eq_getElem?_getD, hlt]

/-- The verifier's index of a matrix's first column is firstCol. -/
theorem cfFirst_eq (tl : HTailF2) (h : tl.NM = tl.mats.size) (μ : Fin (sizeOf tl).size.NM) :
    (tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0]).getD μ.val 0 =
      firstCol (sizeOf tl).size μ := by
  have hμ : μ.val ≤ tl.mats.toList.length := by
    have := μ.isLt
    have e : (sizeOf tl).size.NM = tl.NM := rfl
    simp only [Array.length_toList]
    omega
  have hw := walk_get tl.mats.toList #[0] μ.val (by simp) hμ
  rw [← Array.foldl_toList]
  show (tl.mats.toList.foldl walkStep #[0]).getD μ.val 0 = _
  have h0 : (#[0] : Array Nat).size - 1 + μ.val = μ.val := by simp
  rw [h0] at hw
  rw [hw, sum_take _ _ hμ]
  show _ = ∑ ν : Fin μ.val, (tl.mats.getD ν.val {}).k
  rw [Fin.sum_univ_eq_sum_range (fun i => (tl.mats.getD i {}).k)]
  simp

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.nm_of_walk
#print axioms OnBytes.Tie.Pv.Tail.walk_get
#print axioms OnBytes.Tie.Pv.Tail.cfFirst_eq
