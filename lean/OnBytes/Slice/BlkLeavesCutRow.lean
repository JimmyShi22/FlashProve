-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/BlkLeavesCutRow.lean: a row of the program on the matrix, read and cut at the matrix's
rows: the program's pending row and the row over the field are equal.

A row of the program on the matrix has its weights on the matrix's rows as structured vectors on
kRow variables. OnBytes/Iop/Tensor.lean says of the entry of such a vector that bits of the index
above the variables are not looked at. So the weights, read at every number
(OnBytes/Slice/BlkLeavesTop.lean: `readTRow`), need not be 0 from 2 ^ kRow on; no theorem here says
what they are there. The row over the field (OnBytes/Slice/KeyLeaves.lean: `pendingRowF`) has the
weight 0 outside the rows that its runs read. So the two cannot be taken to be equal as rows over
the field, though each holds of a matrix exactly if the other does.

This file has the reading that is cut at a number of rows (`readTRowAt R`): the weight of a row
below R is the read one, that of every other number is 0. At the number of the matrix's rows the
program's pending row, so read, is the row over the field (`read_pendingRow_eq`). Whether a row
holds of a matrix of R rows does not hang on the cut at R (`cut_holds`).

Main definitions: `TRowF.cut`, `readTRowAt`.
Main theorems: `cut_g_lt`, `cut_g_ge`, `cut_cut`, `cut_holds`, `pendingRowF_g_ge`,
`pendingRowF_cut`, `read_pendingRow_eq`.

Not claimed. Nothing on other rows of the program. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkLeavesTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Slice.Leaves
open Prob Cb
open OnBytes.Params (WfRun WfPart WfLookup)
open OnBytes.Slice.PscF (World)

/-- A row on the matrix, cut at R rows: the weight of every number from R on is 0. -/
def TRowF.cut (R : ℕ) (r : TRowF) : TRowF :=
  { r with g := fun row => if row < R then r.g row else 0 }

/-- A row of the program on the matrix, read and cut at R rows. -/
def readTRowAt (R : ℕ) (t : TensorRow) : TRowF := (readTRow t).cut R

/-- Below the cut the weights stay. -/
theorem cut_g_lt (R : ℕ) (r : TRowF) (row : ℕ) (h : row < R) : (r.cut R).g row = r.g row :=
  if_pos h

/-- From the cut on the weights are 0. -/
theorem cut_g_ge (R : ℕ) (r : TRowF) (row : ℕ) (h : R ≤ row) : (r.cut R).g row = 0 :=
  if_neg (Nat.not_lt.2 h)

/-- The column point stays. -/
theorem cut_psi (R : ℕ) (r : TRowF) : (r.cut R).psi = r.psi := rfl

/-- The mask form stays. -/
theorem cut_masks (R : ℕ) (r : TRowF) : (r.cut R).masks = r.masks := rfl

/-- The target stays. -/
theorem cut_target (R : ℕ) (r : TRowF) : (r.cut R).target = r.target := rfl

/-- A row whose weights are 0 from R on is its own cut at R. -/
theorem cut_eq_self (R : ℕ) (r : TRowF) (h : ∀ row, R ≤ row → r.g row = 0) : r.cut R = r := by
  obtain ⟨g, psi, masks, target⟩ := r
  unfold TRowF.cut
  congr 1
  funext row
  by_cases hr : row < R
  · exact if_pos hr
  · rw [if_neg hr]
    exact (h row (Nat.le_of_not_lt hr)).symm

/-- A second cut at the same number changes nothing. -/
theorem cut_cut (R : ℕ) (r : TRowF) : (r.cut R).cut R = r.cut R :=
  cut_eq_self R _ fun row h => cut_g_ge R r row h

/-- Whether a row holds of a matrix of R rows does not hang on the cut at R. -/
theorem cut_holds (R : ℕ) (r : TRowF) (W : World) (M : ℕ → ℕ → GE) (kCol : ℕ) :
    (r.cut R).Holds W M R kCol ↔ r.Holds W M R kCol := by
  unfold TRowF.Holds
  have e : ∑ a ∈ Finset.range R, ∑ c ∈ Finset.range (2 ^ kCol),
      (r.cut R).g a * eqW (r.cut R).psi c * M a c =
      ∑ a ∈ Finset.range R, ∑ c ∈ Finset.range (2 ^ kCol), r.g a * eqW r.psi c * M a c :=
    Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c _ => by
      rw [cut_g_lt R r a (Finset.mem_range.1 ha), cut_psi]
  rw [e]
  rfl

/-- The row over the field has the weight 0 from R on, if every row that a run reads is one of the
first R. -/
theorem pendingRowF_g_ge (kCol : ℕ) (L : LkF) (runs : List WfRun) (claim : KeysF) (e : List GE)
    (R : ℕ) (h : RowsIn L R runs) (row : ℕ) (hr : R ≤ row) :
    (pendingRowF kCol L runs claim e).g row = 0 := by
  refine List.sum_eq_zero fun v hv => ?_
  obtain ⟨r, hrun, hv⟩ := List.mem_flatMap.1 hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
  have := h r hrun w hw
  unfold rowsW
  exact if_neg (by omega)

/-- So it is its own cut at R. -/
theorem pendingRowF_cut (kCol : ℕ) (L : LkF) (runs : List WfRun) (claim : KeysF) (e : List GE)
    (R : ℕ) (h : RowsIn L R runs) :
    (pendingRowF kCol L runs claim e).cut R = pendingRowF kCol L runs claim e :=
  cut_eq_self R _ (pendingRowF_g_ge kCol L runs claim e R h)

/-- The program's pending row, read and cut at the matrix's rows, is the row over the field. -/
theorem read_pendingRow_eq (m : Wf.Matrix) (l : WfLookup) (p : WfPart) (claim : Lkp.Keys)
    (e : Array E) (pad : GE) (h : RowsIn (lkOf l pad) m.rows p.runs) :
    readTRowAt m.rows (Wf.pendingRow m l p claim e) =
      pendingRowF m.kCol (lkOf l pad) p.runs (readKeys claim) (e.toList.map readE) := by
  have hk : m.rows ≤ 2 ^ m.kRow := le_two_pow_ceilLog2 m.rows
  have h' : RowsIn' l (2 ^ m.kRow) p.runs := fun r hr w hw =>
    le_trans (rowsIn'_of pad h r hr w hw) hk
  have hg : (readTRowAt m.rows (Wf.pendingRow m l p claim e)).g =
      (pendingRowF m.kCol (lkOf l pad) p.runs (readKeys claim) (e.toList.map readE)).g := by
    funext row
    by_cases hr : row < m.rows
    · rw [readTRowAt, cut_g_lt _ _ _ hr]
      exact read_pendingRow_g m l p claim e pad row (lt_of_lt_of_le hr hk) h'
    · rw [readTRowAt, cut_g_ge _ _ _ (Nat.le_of_not_lt hr),
        pendingRowF_g_ge _ _ _ _ _ _ h row (Nat.le_of_not_lt hr)]
  have hpsi : (readTRowAt m.rows (Wf.pendingRow m l p claim e)).psi =
      (pendingRowF m.kCol (lkOf l pad) p.runs (readKeys claim) (e.toList.map readE)).psi :=
    List.map_take
  have ht : (readTRowAt m.rows (Wf.pendingRow m l p claim e)).target =
      (pendingRowF m.kCol (lkOf l pad) p.runs (readKeys claim) (e.toList.map readE)).target := by
    show readE (subE claim.target (mulE (Wf.coveredSum p e) (OnBytes.ofF l.offset))) = _
    rw [readE_sub, readE_mul, read_coveredSum]
    rfl
  have hm : (readTRowAt m.rows (Wf.pendingRow m l p claim e)).masks =
      (pendingRowF m.kCol (lkOf l pad) p.runs (readKeys claim) (e.toList.map readE)).masks := rfl
  generalize readTRowAt m.rows (Wf.pendingRow m l p claim e) = A at hg hpsi ht hm
  generalize pendingRowF m.kCol (lkOf l pad) p.runs (readKeys claim) (e.toList.map readE) = B
    at hg hpsi ht hm
  cases A
  cases B
  simp only at hg hpsi ht hm
  subst hg hpsi ht hm
  rfl

end OnBytes.Slice.Leaves

#print axioms OnBytes.Slice.Leaves.cut_g_lt
#print axioms OnBytes.Slice.Leaves.cut_g_ge
#print axioms OnBytes.Slice.Leaves.cut_psi
#print axioms OnBytes.Slice.Leaves.cut_masks
#print axioms OnBytes.Slice.Leaves.cut_target
#print axioms OnBytes.Slice.Leaves.cut_eq_self
#print axioms OnBytes.Slice.Leaves.cut_cut
#print axioms OnBytes.Slice.Leaves.cut_holds
#print axioms OnBytes.Slice.Leaves.pendingRowF_g_ge
#print axioms OnBytes.Slice.Leaves.pendingRowF_cut
#print axioms OnBytes.Slice.Leaves.read_pendingRow_eq
