-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BaseGk.lean: the program's own claim on the last group, as the last case of its
proximity test takes it.

OnBytes/Slice/BlkRead.lean reads a row on a group, as the program (the Lean verifier in OnBytes/)
holds it, as a statement, with the group's own numbers of row variables (`stmGk`). The last group
has one row variable for its main table and none for its mask table, while its stage has no row
variable. This file says what that reading is at the one row of each of the stage's tables. These
are the three hypotheses on the claim in OnBytes/Slice/BaseLast.lean's and BaseOpen.lean's theorems
on the last case.

It also meets the condition `FixLaw` of OnBytes/Slice/BaseLast.lean for a form without a written-out
factor (OnBytes/Slice/BlkFoldVec.lean).

Main theorems: `claim_of_stmGk`, `fixLaw_of_plain`.
Not claimed. That a form which the program holds has no written-out factor.
-/
import OnBytes.Slice.BaseOpen
import OnBytes.Slice.BlkRead
import OnBytes.Slice.BlkFoldVec

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run

/-- The vertex whose digits are all 0 has the number 0. -/
theorem rowNo_false (k : ℕ) : Sz.rowNo (fun _ : Fin k => false) = 0 := by
  simp [Sz.rowNo]

/-- The program's row on the last group, read with one row variable on the main table and none on
the mask table, at the first row of each table. -/
theorem claim_of_stmGk (s : Sg) (row : GroupRow) :
    (stmGk s 1 0 row).1 = readE row.target ∧
      (∀ j : Fin s.C.l,
        (stmGk s 1 0 row).2 (.inl (fun _ => false, j)) = readE (row.c.entry (2 * j.val))) ∧
      ∀ j : Fin s.Z.l, (stmGk s 1 0 row).2 (.inr (fun _ => false, j)) = readV row.d j.val := by
  refine ⟨rfl, fun j => ?_, fun j => ?_⟩
  · show readE (row.c.entry (Sz.rowNo (fun _ => false) + 2 ^ 1 * j.val)) = _
    rw [rowNo_false, Nat.zero_add, pow_one]
  · show readV row.d (Sz.rowNo (fun _ => false) + 2 ^ 0 * j.val) = _
    rw [rowNo_false, Nat.zero_add, pow_zero, Nat.one_mul]

/-- A form without a written-out factor, each of whose tensors has a variable, meets what is asked
of the fixing of its lowest variable at 0. -/
theorem fixLaw_of_plain (f : Form) (hp : PlainForm f) (hv : ∀ v ∈ f.tensors, 1 ≤ v.vars) :
    FixLaw f [zeroE] := fun p => formAt_fixLow_range f hp [zeroE] hv oneE p

end OnBytes.Slice

#print axioms OnBytes.Slice.claim_of_stmGk
#print axioms OnBytes.Slice.fixLaw_of_plain
#print axioms OnBytes.Slice.rowNo_false
