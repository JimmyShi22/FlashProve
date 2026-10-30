-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LabelByList.lean: THE READER OF AN ARRAY's NUMBER OUT OF ITS
NAME (`K1.labelNo`, Honest/K1/FirstData.lean) AND THE SIZES THAT THE PACKED CELLS' VALUES STATE
(`K1.cellsVals`, there), EACH WITH A TWIN THAT LEAN's KERNEL REDUCES, AND THAT THE TWINS ARE THE
ORIGINALS. Definitions with code; statements with their proofs. Guests in this folder: facts on
another folder's terms, typed for the tests by Lean's kernel beside them.

WHY. Lean's kernel does not reduce `String.Slice.toNat?`. THE LIBRARY's TOOL FOR THAT IS
Johnson/Unfolds/SliceFoldl.lean: `toNatL` on a list of characters, with `slice_toNat?_eq`. Its head
says how to use it at a closed statement: rewrite, then ask the kernel. `K1.labelNo` stands inside
`K1.cellsVals`, inside data that closed tests read through several definitions: so here the
rewriting is done once, as equations between definitions.

  `labelNoL`, `labelNo_eq`   `K1.labelNo`'s text over the library's `toNatL`; it is `K1.labelNo`
  `cellsValsL`, `cellsVals_eq`   the like for `K1.cellsVals`
  `labelsW`         BY LEAN's KERNEL: the twin reads 0 … 8 out of "M0" … "M8", and nothing out of
                    "U3", "ZZ", "BZ", "M", "M01" and "Mx"

Limits. Equations and one closed fact. Nothing on any layout, datum or run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K1.FirstData
import Johnson.Unfolds.SliceFoldl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes.HonestTrace (Sz packedCells arrayLabel)
open OnBytes.Slice (toF)
open Johnson.Unfolds (toNatL slice_toNat?_eq)

/-- `K1.labelNo`'s text over the library's `toNatL`. -/
def labelNoL (name : String) : Option Nat :=
  (if name.startsWith "M" then toNatL (name.drop 1).copy.toList else none).bind fun mu =>
    if arrayLabel mu == name then some mu else none

/-- **The twin is the original.** -/
theorem labelNo_eq (name : String) : K1.labelNo name = labelNoL name := by
  unfold K1.labelNo labelNoL
  rw [slice_toNat?_eq]

/-- `K1.cellsVals`'s text over `labelNoL`. -/
def cellsValsL (S : Sz) : ArrayVals :=
  { size := fun l name =>
      (labelNoL name).bind fun mu => (S.matAt l mu).bind fun x =>
        if (S.arrayNo x.1 x.2).isSome then some (S.packedShape l mu) else none
    val := fun R _ l name i c =>
      match labelNoL name with
      | some mu => .inl (packedCells S R.cells.cell l mu i c)
      | none => .inl (toF 0) }

/-- **The twin is the original.** -/
theorem cellsVals_eq (S : Sz) : K1.cellsVals S = cellsValsL S := by
  unfold K1.cellsVals cellsValsL
  simp only [labelNo_eq]
  rfl

set_option maxRecDepth 1000000 in
/-- **The twin reads the nine names, and refuses six others.** -/
theorem labelsW :
    (((List.range 9).all fun mu => labelNoL (arrayLabel mu) == some mu) &&
      ["U3", "ZZ", "BZ", "M", "M01", "Mx"].all fun n => labelNoL n == none) = true := by
  decide +kernel

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.labelNoL
#print axioms ProofFile.Honest.K2.Law.labelNo_eq
#print axioms ProofFile.Honest.K2.Law.cellsValsL
#print axioms ProofFile.Honest.K2.Law.cellsVals_eq
#print axioms ProofFile.Honest.K2.Law.labelsW
