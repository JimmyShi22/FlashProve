-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkRowRead.lean: an open row of the program's statement, read in the field.

A row of the statement (OnBytes/Iop/Ground.lean: Row) says that a linear form of the sent messages'
entries has a public value. The program has a function for the row's whole coefficient on one entry
(Row.coefficient). Here a row is read as that function, read in the field, with the target, read
(readRow). The laws on the batching of rows (OnBytes/Iop/RowLaws.lean, OnBytes/Iop/MaskLaws.lean:
combine_main_member, combine_mask_member) state what a batched row holds in the same terms.

The row that a sumcheck without kept maps puts aside has coefficients on mask entries alone
(Row.addMasks on an empty row). It reads as RowF.ofMasks of the mask form and the target, read.

Main definitions: RowF, readRow, RowF.ofMasks.

Main theorems: addMasks_eq, readRow_addMasks, rowU_nil.

Not claimed. Nothing on rows with structured vectors, runs or whole vectors. Nothing on what a row
means for sent messages, and nothing on where a mask entry lies in a group's table.

-/
import OnBytes.Iop.RowLaws
import OnBytes.Slice.BlkPscRead
import OnBytes.Slice.BlkRead

set_option autoImplicit false

namespace OnBytes.Slice
open Prob Cb

/-- A row, read in the field: its coefficient on each entry (oracle message, table, index), and its
target. -/
structure RowF where
  coef : ℕ → Part → ℕ → GE
  target : GE

/-- **How a row of the statement is read.** -/
def readRow (r : Row) : RowF := ⟨fun o p i => readE (r.coefficient o p i), readE r.target⟩

/-- The row with the coefficients of a mask form, and a target. An entry that occurs twice in the
form has the sum of its coefficients. -/
def RowF.ofMasks (m : PscF.MaskForm) (t : GE) : RowF where
  coef o p i := (m.map fun e =>
    if e.1.oracle = o ∧ Part.mask = p then (if e.1.index = i then e.2 else 0) else 0).sum
  target := t

/-- A mask form's entry as a coefficient on a single entry of a mask table. -/
def singleOf (t : Slot × E) : Single := ⟨t.1.oracle, .mask, t.1.index, t.2⟩

/-- Adding a mask form to a row appends its entries to the row's single entries. -/
theorem addMasks_eq : ∀ (m : MaskForm) (r : Row),
    r.addMasks m = { r with units := r.units ++ (m.map singleOf).toArray }
  | [], r => by
    show r = _
    simp
  | t :: m, r => by
    show (r.addUnit t.1.oracle .mask t.1.index t.2).addMasks m = _
    rw [addMasks_eq m]
    show ({ r with units := r.units.push (singleOf t) ++ (m.map singleOf).toArray } : Row) = _
    simp

/-- **The row of a mask form and a target, read.** -/
theorem readRow_addMasks (m : MaskForm) (t : E) :
    readRow (({ target := t } : Row).addMasks m) = RowF.ofMasks (readForm m) (readE t) := by
  rw [addMasks_eq]
  unfold readRow RowF.ofMasks
  refine congrArg₂ RowF.mk (funext fun o => funext fun p => funext fun i => ?_) rfl
  have h := Row.coefficient_val rdE
    ({ target := t, units := #[] ++ (m.map singleOf).toArray } : Row) o p i
  refine h.trans ?_
  simp only [List.map_nil, List.sum_nil, zero_add, add_zero, Array.empty_append, readForm,
    List.map_map]
  rfl

/-- The row of a run without kept maps: the run's mask form and target. -/
theorem rowU_nil (o : Psc.Out) (row : Row) (h : Psc.rowU o [] = some row) :
    row = ({ target := o.rowTarget } : Row).addMasks o.rowMasks := by
  unfold Psc.rowU at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

end OnBytes.Slice
