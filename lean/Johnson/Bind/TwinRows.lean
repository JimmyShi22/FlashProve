-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinRows.lean: the plain encoder of the committer that runs, row by row.

`columnOf S (laid S T) x` (Johnson/Bind/Twin.lean) is the column at a position: one symbol of every
row. `laid` holds all rows' messages and tails at once. A program that wants a few columns of a
large table goes the other way: it makes one row's lists once and that row's symbols at all wanted
positions (`rowSymbols`). This file says that the two give the same symbols.
Main theorems:
   `columnOf_laid`: the column at x is, row by row, `Fmt.M1.symF` at the row's message and tail;
   `rowSymbols_eq`: for a row b below 2^v, `rowSymbols S T xs b` is, position by position, entry b
      of the column.
No Mathlib.
Limits. Equations between this library's own terms. No program of this library calls `rowSymbols`.

-/
import Johnson.Bind.Twin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

/-- The symbols of the row b at given positions, by the plain encoder. The row's lists are made
once.
-/
def rowSymbols (S : Shape) (T : Table) (xs : List Nat) (b : Nat) : List UInt64 :=
  let m := message S T b
  let t := tailOf S T b
  xs.map fun x => Fmt.M1.symF S.code x m t

/-- The column at x, row by row. -/
theorem columnOf_laid (S : Shape) (T : Table) (x : Nat) :
    columnOf S (laid S T) x =
      (List.range S.rows).map fun b => Fmt.M1.symF S.code x (message S T b) (tailOf S T b) := by
  unfold columnOf laid
  rw [List.map_map]
  rfl

/-- **A row's symbols are the columns' entries at that row.** -/
theorem rowSymbols_eq (S : Shape) (T : Table) (xs : List Nat) (b : Nat) (hb : b < S.rows) :
    rowSymbols S T xs b = xs.map fun x => (columnOf S (laid S T) x).getD b 0 := by
  unfold rowSymbols
  refine List.map_congr_left fun x _ => ?_
  have hl : b < ((List.range S.rows).map fun b =>
      Fmt.M1.symF S.code x (message S T b) (tailOf S T b)).length := by
    rw [List.length_map, List.length_range]
    exact hb
  rw [columnOf_laid, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    List.getElem_map, List.getElem_range]

end Bind.Twin

#print axioms Bind.Twin.columnOf_laid
#print axioms Bind.Twin.rowSymbols_eq
