-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/BlkLeavesRows.lean: the program's weights on the rows of the matrix, read in the
field.

`Wf.weightsOnRows` (OnBytes/Iop/Wf.lean) puts weights on a stretch of rows of the matrix as a list
of structured vectors (OnBytes/Iop/Tensor.lean): it cuts the stretch into aligned blocks of rows,
and each block's vector picks the block by the high bits of a row's number and reads a slice of one
written-out vector by the low bits. OnBytes/Slice/KeyLeaves.lean has these weights as a function of
the row's number (`rowsW`). This file shows that the entries of the program's vectors at a row, read
in the field and added up, are that function.

The loop over the blocks has a bound on its number of steps: the number of rows, which suffices
since each block has a row. The search for a block's size has the bound kRow, which needs nothing:
whatever size the search stops at, the block is aligned and fits.

Main theorems.
 `rowBlockBits_spec`   the block that the search finds is aligned, fits and has at most 2 ^ kRow
                       rows.
 `pairsVal_ones`, `denseIndex_range`   the two parts of a written-out factor's entry.
 `read_single`, `read_dense`, `read_block`   the entries of one block's vector.
 `read_weightsFrom`, `read_weightsOnRows`   the entries of all blocks' vectors, added up.
 `read_pendingRow_g`   the weights of the program's pending row, read, are those of the row over the
                       field.

Not claimed. Nothing on rows from 2 ^ kRow on. Nothing on a run on a view, on soundness or on
hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkLeavesRead
import OnBytes.Iop.TensorLaws

set_option autoImplicit false

namespace OnBytes.Slice.Leaves
open Prob Cb
open OnBytes.Params (WfRun WfPart WfLookup)
open OnBytes.Model (Reading)

/-- The reading of the laws on structured vectors is readE. -/
theorem gl_val (x : E) : Reading.gl.val x = readE x := rfl

/-! ## The search for a block's size -/

/-- The block that the search for a size finds is aligned, fits and has at most 2 ^ kRow rows, if
the block that it starts from does. -/
theorem rowBlockBits_spec (kRow start stop : ℕ) : ∀ (fuel d : ℕ), start % 2 ^ d = 0 →
    start + 2 ^ d ≤ stop → d ≤ kRow →
    start % 2 ^ Wf.rowBlockBits kRow start stop fuel d = 0 ∧
      start + 2 ^ Wf.rowBlockBits kRow start stop fuel d ≤ stop ∧
      Wf.rowBlockBits kRow start stop fuel d ≤ kRow
  | 0, _, h1, h2, h3 => ⟨h1, h2, h3⟩
  | fuel + 1, d, h1, h2, h3 => by
    unfold Wf.rowBlockBits
    split
    · next h =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      exact rowBlockBits_spec kRow start stop fuel (d + 1) h.1.2 h.2 h.1.1
    · exact ⟨h1, h2, h3⟩

/-! ## One block's vector -/

/-- Pairs (1, 1) give the factor 1 at every index. -/
theorem pairsVal_ones : ∀ (d j : ℕ),
    pairsVal Reading.gl (List.replicate d (oneE, oneE)) j = 1
  | 0, _ => rfl
  | d + 1, j => by
    rw [List.replicate_succ, pairsVal, pairsVal_ones d]
    by_cases h : (j % 2 == 1) = true
    · simp only [h, if_true, Reading.gl.one, mul_one]
    · simp only [h, Bool.false_eq_true, if_false, Reading.gl.one, mul_one]

/-- The index within a slice whose bits are the bits a, a + 1, .. of the vector's index. -/
theorem denseIndex_from : ∀ (d a i j : ℕ),
    denseIndex ((List.range' a d)) i j = 2 ^ i * (j / 2 ^ a % 2 ^ d)
  | 0, _, _, _ => by simp [denseIndex, Nat.mod_one]
  | d + 1, a, i, j => by
    rw [List.range'_succ, denseIndex, denseIndex_from d (a + 1) (i + 1) j, pow_succ 2 d,
      Nat.mul_comm (2 ^ d) 2, Nat.mod_mul, pow_succ 2 a, ← Nat.div_div_eq_div_mul, pow_succ 2 i]
    ring

/-- The index within a slice whose bits are the d lowest bits of the vector's index. -/
theorem denseIndex_range (d j : ℕ) :
    denseIndex ((List.range d).map (· + 0)) 0 j = j % 2 ^ d := by
  have e : (List.range d).map (· + 0) = List.range' 0 d := by
    rw [List.range_eq_range']
    simp
  rw [e, denseIndex_from, pow_zero, Nat.one_mul, Nat.div_one]

/-- A block of one row. -/
theorem read_single (kRow start row : ℕ) (x : E) (hs : start < 2 ^ kRow) (hr : row < 2 ^ kRow) :
    readE ((({ scalar := x } : Tensor).insertChoice 0 kRow start).entry row) =
      if row = start then readE x else 0 := by
  rw [← gl_val, Tensor.entry_insertChoice _ _ _ _ _ _ (Nat.zero_le _), pow_zero, Nat.div_one,
    Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs, Tensor.entry_val]
  by_cases h : row = start
  · rw [if_pos h, if_pos h]
    simp [pairsVal, Tensor.denseVal, gl_val]
  · rw [if_neg h, if_neg h, zero_mul]

/-- A row's number lies in an aligned block exactly if it has the block's high bits. -/
theorem in_block (d start row : ℕ) (h : start % 2 ^ d = 0) :
    row / 2 ^ d = start / 2 ^ d ↔ start ≤ row ∧ row < start + 2 ^ d := by
  have hp : 0 < 2 ^ d := Nat.two_pow_pos d
  have e1 := Nat.div_add_mod start (2 ^ d)
  have e2 := Nat.div_add_mod row (2 ^ d)
  have h2 := Nat.mod_lt row hp
  rw [h, Nat.add_zero] at e1
  constructor
  · intro he
    rw [he, e1] at e2
    omega
  · rintro ⟨a, b⟩
    rw [← e1] at a b
    have l1 : start / 2 ^ d ≤ row / 2 ^ d := by
      rw [Nat.le_div_iff_mul_le hp, Nat.mul_comm]
      exact a
    have l2 : row / 2 ^ d < start / 2 ^ d + 1 := by
      rw [Nat.div_lt_iff_lt_mul hp, Nat.add_mul, Nat.one_mul, Nat.mul_comm]
      exact b
    omega

/-- A block of 2 ^ d rows, d not 0. -/
theorem read_dense (kRow d start first row : ℕ) (values : Array E) (scale : E) (hd0 : d ≠ 0)
    (hd : d ≤ kRow) (ha : start % 2 ^ d = 0) (hs : start < 2 ^ kRow) (hr : row < 2 ^ kRow) :
    readE ((((({ scalar := scale } : Tensor).pushDense d).insertChoice d (kRow - d)
      (start / 2 ^ d)).setValues values first).entry row) =
      if start ≤ row ∧ row < start + 2 ^ d then
        readE scale * readV values (first + (row - start)) else 0 := by
  have hswap : ((({ scalar := scale } : Tensor).pushDense d).insertChoice d (kRow - d)
      (start / 2 ^ d)).setValues values first =
      ((({ scalar := scale } : Tensor).pushDense d).setValues values first).insertChoice d
        (kRow - d) (start / 2 ^ d) := rfl
  have hv : ((({ scalar := scale } : Tensor).pushDense d).setValues values first).vars = d := by
    show (([] : List (E × E)) ++ List.replicate d (oneE, oneE)).length = d
    simp
  have hpow : 2 ^ kRow = 2 ^ d * 2 ^ (kRow - d) := by rw [← pow_add, Nat.add_sub_cancel' hd]
  have q1 : row / 2 ^ d < 2 ^ (kRow - d) := Nat.div_lt_of_lt_mul (by rw [← hpow]; exact hr)
  have q2 : start / 2 ^ d < 2 ^ (kRow - d) := Nat.div_lt_of_lt_mul (by rw [← hpow]; exact hs)
  rw [hswap, ← gl_val, Tensor.entry_insertChoice _ _ _ _ _ _ (le_of_eq hv.symm),
    Nat.mod_eq_of_lt q1, Nat.mod_eq_of_lt q2]
  by_cases h : row / 2 ^ d = start / 2 ^ d
  · have hb := (in_block d start row ha).1 h
    rw [if_pos h, if_pos hb, one_mul, Tensor.entry_val]
    have hu : unshift d (kRow - d) row = row % 2 ^ d := by
      unfold unshift
      rw [Nat.add_sub_cancel' hd, Nat.div_eq_of_lt hr, Nat.mul_zero, Nat.add_zero]
    rw [hu]
    have hp : pairsVal Reading.gl
        ((({ scalar := scale } : Tensor).pushDense d).setValues values first).pairs
        (row % 2 ^ d) = 1 := by
      show pairsVal Reading.gl (([] : List (E × E)) ++ List.replicate d (oneE, oneE)) _ = 1
      rw [List.nil_append, pairsVal_ones]
    have hdv : ((({ scalar := scale } : Tensor).pushDense d).setValues values first).denseVal
        Reading.gl (row % 2 ^ d) = readV values (first + (row - start)) := by
      unfold Tensor.denseVal
      have hne :
          ((({ scalar := scale } : Tensor).pushDense d).setValues values first).denseVars.isEmpty =
            false := by
        show (([] : List ℕ) ++ (List.range d).map (· + 0)).isEmpty = false
        cases d with
        | zero => exact absurd rfl hd0
        | succ d => simp [List.range_succ]
      rw [hne]
      show Reading.gl.val (values.getD (first + denseIndex (([] : List ℕ) ++
        (List.range d).map (· + 0)) 0 (row % 2 ^ d)) zeroE) = _
      rw [List.nil_append, denseIndex_range, Nat.mod_mod]
      have hm : row % 2 ^ d = row - start := by
        have e1 := Nat.div_add_mod start (2 ^ d)
        have e2 := Nat.div_add_mod row (2 ^ d)
        rw [ha, Nat.add_zero] at e1
        rw [h, e1] at e2
        omega
      rw [hm]
      rfl
    rw [hp, hdv, mul_one]
    rfl
  · rw [if_neg h, if_neg fun hb => h ((in_block d start row ha).2 hb), zero_mul]

/-- One block's vector, as the loop writes it. -/
theorem read_block (kRow d start first row : ℕ) (values : Array E) (scale : E) (hd : d ≤ kRow)
    (ha : start % 2 ^ d = 0) (hs : start < 2 ^ kRow) (hr : row < 2 ^ kRow) :
    readE ((if d == 0 then
        ({ scalar := mulE (values.getD first zeroE) scale } : Tensor).insertChoice 0 kRow start
      else
        ((({ scalar := scale } : Tensor).pushDense d).insertChoice d (kRow - d)
          (start / 2 ^ d)).setValues values first).entry row) =
      if start ≤ row ∧ row < start + 2 ^ d then
        readE scale * readV values (first + (row - start)) else 0 := by
  by_cases h0 : d = 0
  · subst h0
    rw [if_pos (beq_self_eq_true 0), read_single kRow start row _ hs hr, pow_zero]
    by_cases h : row = start
    · subst h
      rw [if_pos rfl, if_pos ⟨le_refl _, by omega⟩, Nat.sub_self, Nat.add_zero, readE_mul, mul_comm]
      rfl
    · rw [if_neg h, if_neg (by omega)]
  · rw [if_neg (by simpa using h0)]
    exact read_dense kRow d start first row values scale h0 hd ha hs hr

/-! ## All blocks -/

/-- The entries of all blocks' vectors at a row, added up. -/
theorem read_weightsFrom (kRow : ℕ) (values : Array E) (scale : E) (stop row : ℕ)
    (hstop : stop ≤ 2 ^ kRow) (hr : row < 2 ^ kRow) : ∀ (fuel start first : ℕ),
    stop - start ≤ fuel →
    ((Wf.weightsFrom kRow values scale stop fuel start first).map fun t =>
      readE (t.entry row)).sum =
      if start ≤ row ∧ row < stop then readE scale * readV values (first + (row - start)) else 0
  | 0, start, first, h => by
    rw [if_neg (by omega)]
    rfl
  | fuel + 1, start, first, h => by
    unfold Wf.weightsFrom
    by_cases hlt : start < stop
    · rw [if_pos hlt]
      obtain ⟨g1, g2, g3⟩ := rowBlockBits_spec kRow start stop kRow 0
        (by rw [pow_zero, Nat.mod_one]) (by rw [pow_zero]; omega) (Nat.zero_le _)
      simp only []
      generalize Wf.rowBlockBits kRow start stop kRow 0 = d at g1 g2 g3
      have hp : 0 < 2 ^ d := Nat.two_pow_pos d
      rw [List.map_cons, List.sum_cons, read_block kRow d start first row values scale g3 g1
        (by omega) hr, read_weightsFrom kRow values scale stop row hstop hr fuel _ _ (by omega)]
      by_cases h1 : start ≤ row ∧ row < start + 2 ^ d
      · rw [if_pos h1, if_neg (by omega), if_pos ⟨h1.1, by omega⟩, add_zero]
      · rw [if_neg h1, zero_add]
        by_cases h2 : start + 2 ^ d ≤ row ∧ row < stop
        · rw [if_pos h2, if_pos ⟨by omega, h2.2⟩,
            show first + 2 ^ d + (row - (start + 2 ^ d)) = first + (row - start) by omega]
        · rw [if_neg h2, if_neg (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]
      rfl

/-- The program's weights on a stretch of rows, read, are the weights over the field. -/
theorem read_weightsOnRows (kRow firstRow : ℕ) (values : Array E) (first count : ℕ) (scale : E)
    (row : ℕ) (h : firstRow + count ≤ 2 ^ kRow) (hr : row < 2 ^ kRow) :
    ((Wf.weightsOnRows kRow firstRow values first count scale).map fun t =>
      readE (t.entry row)).sum =
      rowsW firstRow (values.toList.map readE) first count (readE scale) row := by
  unfold Wf.weightsOnRows rowsW
  rw [read_weightsFrom kRow values scale _ row h hr count firstRow first (by omega)]
  have e : readV values (first + (row - firstRow)) =
      (values.toList.map readE).getD (first + (row - firstRow)) 0 := by
    rw [readV_eq_readL]
    unfold readL
    by_cases hl : first + (row - firstRow) < values.toList.length
    · rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hl),
        List.getElem_map]
    · rw [List.getD_eq_default _ _ (by omega),
        List.getD_eq_default _ _ (by rw [List.length_map]; omega), readE_zero]
  rw [e]

/-! ## The pending row -/

/-- Every row that a run reads, for every digit of the lookup, is one of the first R rows. -/
def RowsIn' (l : WfLookup) (R : ℕ) (runs : List WfRun) : Prop :=
  ∀ r ∈ runs, ∀ w ∈ l.digitWeight.zipIdx, r.firstRow + w.2 * r.stride + r.places ≤ R

/-- The public elements of a lookup, read. pad: what a place of padding holds. -/
def lkOf (l : WfLookup) (pad : GE) : LkF :=
  ⟨readE (OnBytes.ofF l.offset), pad, l.digitWeight.map fun w => readE (OnBytes.ofF w)⟩

/-- Numbering the members of a list and applying a function to them can be exchanged. -/
theorem map_zipIdx {α β : Type} (f : α → β) : ∀ (l : List α) (k : ℕ),
    (l.map f).zipIdx k = (l.zipIdx k).map fun x => (f x.1, x.2)
  | [], _ => rfl
  | a :: l, k => by
    rw [List.map_cons, List.zipIdx_cons, List.zipIdx_cons, List.map_cons, map_zipIdx f l]

/-- The sum of lists laid one behind the other is the sum of their sums. -/
theorem sum_flatMap {α : Type} (f : α → List GE) : ∀ l : List α,
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.sum_append, sum_flatMap f l, List.map_cons, List.sum_cons]

/-- The weights of the program's pending row at a row of the matrix, read and added up, are the
weights of the row over the field. Asked: every row that a run reads is below 2 ^ kRow. -/
theorem read_pendingRow_g (m : Wf.Matrix) (l : WfLookup) (p : WfPart) (claim : Lkp.Keys)
    (e : Array E) (pad : GE) (row : ℕ) (hr : row < 2 ^ m.kRow)
    (h : RowsIn' l (2 ^ m.kRow) p.runs) :
    ((Wf.pendingRow m l p claim e).g.map fun t => readE (t.entry row)).sum =
      (pendingRowF m.kCol (lkOf l pad) p.runs (readKeys claim) (e.toList.map readE)).g row := by
  show ((p.runs.flatMap fun r => l.digitWeight.zipIdx.flatMap fun w =>
      Wf.weightsOnRows m.kRow (r.firstRow + w.2 * r.stride) e r.firstPlace r.places
        (OnBytes.ofF w.1)).map fun t => readE (t.entry row)).sum =
    (p.runs.flatMap fun r =>
      (l.digitWeight.map fun w => readE (OnBytes.ofF w)).zipIdx.map fun w =>
      rowsW (r.firstRow + w.2 * r.stride) (e.toList.map readE) r.firstPlace r.places w.1 row).sum
  rw [List.map_flatMap, sum_flatMap, sum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun r hrun => ?_)
  rw [List.map_flatMap, sum_flatMap, map_zipIdx, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun w hw => ?_)
  exact read_weightsOnRows m.kRow _ e _ _ _ row (h r hrun w hw) hr

end OnBytes.Slice.Leaves
