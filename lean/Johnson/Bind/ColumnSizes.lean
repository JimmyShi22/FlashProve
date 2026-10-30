-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ColumnSizes.lean: THE COLUMN AND THE DIGITS AT THE LIBRARY'S TWO SIZES. The general
theorems of Johnson/Bind/Column.lean and Johnson/Bind/Digits.lean are taken at the full size and at
the small example's size: their premises on numbers are paid by evaluation.

Why. One text of the running committer (Johnson/Bind/Twin.lean) is taken at any shape, and one
theorem ties its columns to the library's honest table at any sizes. Here it is shown that the
theorem's premise is met at both sizes that the library has: so it is empty at neither.

Main names (namespace `Bind.Column`).
  `shFull`, `shSmall`: the two shapes, as numerals.
  `agree_full`, `agree_small`: they have the numbers of `frS` and `srS`
    (OnBytes/Slice/FullRecLink.lean, OnBytes/Slice/SmallRecLink.lean); the pads begin at 402,653,181
    and at 524,285.
  **`column_full`**, **`column_small`**: `ColumnAgrees` there: no premise.
  **`entry_full`**, **`entry_small`**: `EntryAgrees` there: no premise.

Limits. Those of Johnson/Bind/ColumnDefs.lean. At the small size the library has the honest side of
a stored table (`codingCells srS srZ 524285 numsSmall`) and no description of a protocol over it:
the two statements at the small size speak of that honest side alone. That `shSmall` is the shape of
a stored example of the programs is not shown here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Bind.Column
import Johnson.Bind.Digits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.Column
open OnBytes.Slice OnBytes.Flat
open VerifiableInference.OnPublicFiles (numsRef)
open Bind.Twin (Shape)

/-- The full size's shape. -/
def shFull : Shape := ⟨32, 402653184, 44040191, 11, 1, 40⟩

/-- The small example's shape. -/
def shSmall : Shape := ⟨23, 524288, 65535, 8, 1, 40⟩

theorem agree_full : Agree shFull frS 402653181 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem agree_small : Agree shSmall srS 524285 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The column at the full size.** -/
theorem column_full : ColumnAgrees frS frZ 402653181 numsRef shFull := columnAgrees agree_full

/-- **The column at the small example's size.** -/
theorem column_small : ColumnAgrees srS srZ 524285 numsSmall shSmall := columnAgrees agree_small

/-- **The digits at the full size.** -/
theorem entry_full : EntryAgrees frS frZ 402653181 numsRef :=
  entryAgrees frS frZ 402653181 numsRef full_fits.1

/-- **The digits at the small example's size.** -/
theorem entry_small : EntryAgrees srS srZ 524285 numsSmall :=
  entryAgrees srS srZ 524285 numsSmall small_fits.1

end Bind.Column

end

#print axioms Bind.Column.agree_full
#print axioms Bind.Column.agree_small
#print axioms Bind.Column.column_full
#print axioms Bind.Column.column_small
#print axioms Bind.Column.entry_full
#print axioms Bind.Column.entry_small
