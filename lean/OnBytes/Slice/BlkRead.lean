-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkRead.lean: how the data of the program's blocks are read in the field.

The program's verifier is made of blocks (OnBytes/Iop/). Between the blocks of a proximity test it
holds one linear claim, as a record of words: a row on a group's tables (`GroupRow`), or a claim on
the rows that a fold hands on (`SingleRows`). OnBytes/Slice/Stage.lean fixes how the format's
records are read as statements of the library's relations. This file fixes the same for the
program's records, once for all blocks, with the same conventions: if a table has 2^k rows, what is
in row b at place j is found at the index that is the number of b plus 2^k * j.

Main definitions.
 `formAt`, `coefAt`    an entry of a form, and a row's coefficient on an entry of a table.
 `rowOn`, `groupOn`    a row, and a row on a group, read at an index of either table.
 `vecGk`, `stmGk`      a row on a group: the vector of coefficients, and the statement, read with
                      the group's own numbers of row bits; `vecG`, `stmG` with the stage's.
 `vecS`, `stmS`        a claim on the three folded rows, likewise.
 `symS`                the symbols that the program has read of the three folded rows.
 `rdE`                 the reading of an element, as a record with its laws.
No theorem is in this file but `rdE_val`, `vecG_eq_vecGk` and `stmG_eq`, which hold by definition.

Not claimed. Nothing on what a block computes. Kept members of a group are not read: `vecG` looks
at the forms on the group's own two tables alone, `vecS` at those on the three folded rows alone.
-/
import OnBytes.Slice.Stage
import OnBytes.Slice.ProgField
import OnBytes.Iop.TensorLaws
import OnBytes.Iop.Fold

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## The reading

An element of the program is read by `readE`, an entry of an array or a list of them by `readV` or
`readL` (OnBytes/Slice/ProgField.lean, with what the program's arithmetic reads as). As a map that
respects 0, 1, sums, differences and products the reading is `Model.Reading.gl`
(OnBytes/Model/HideLaws.lean): at it the laws on tensors and forms of OnBytes/Iop/TensorLaws.lean
are used. -/

/-- The reading of the program's elements, under a short name. -/
abbrev rdE : Model.Reading GE := Model.Reading.gl

/-- The record reads an element as `readE` does. -/
theorem rdE_val (a : E) : rdE.val a = readE a := rfl

/-! ## Forms and rows -/

/-- Entry i of a form, in the field. -/
def formAt (c : Form) (i : ℕ) : GE := readE (c.entry i)

/-- The coefficient of a row on entry i of a table of the oracle message number o, in the field. -/
def coefAt (r : Row) (o : ℕ) (part : Part) (i : ℕ) : GE := readE (r.coefficient o part i)

/-- A row's coefficients on the two tables of the oracle message number o, read at an index of the
main table (left) or of the mask table (right). -/
def rowOn (r : Row) (o : ℕ) : ℕ ⊕ ℕ → GE := Sum.elim (coefAt r o .main) (coefAt r o .mask)

/-- A row on a group, read at an index of the group's main table (left) or of its mask table
(right). -/
def groupOn (G : GroupRow) : ℕ ⊕ ℕ → GE := Sum.elim (formAt G.c) (readV G.d)

/-! ## Claims -/

section
variable (s : Sg)

/-- The coefficients of the program's row on a group whose main table has 2^k rows and whose mask
table has 2^h rows. The group may have more rows than the stage: the stage's rows are its first. -/
def vecGk (k h : ℕ) (G : GroupRow) : s.cIn.J → GE
  | .inl x => formAt G.c (Sz.rowNo x.1 + 2 ^ k * x.2.val)
  | .inr x => readV G.d (Sz.rowNo x.1 + 2 ^ h * x.2.val)

/-- The program's row on a group, as a statement, read with the group's own numbers of row
bits. -/
def stmGk (k h : ℕ) (G : GroupRow) : GE × (s.cIn.J → GE) := (readE G.target, vecGk s k h G)

/-- The coefficients of the program's row on a group that has the stage's numbers of rows. -/
def vecG (G : GroupRow) : s.cIn.J → GE
  | .inl x => formAt G.c (Sz.rowNo x.1 + 2 ^ (s.h + s.g) * x.2.val)
  | .inr x => readV G.d (Sz.rowNo x.1 + 2 ^ s.h * x.2.val)

/-- The program's row on a group that has the stage's numbers of rows, as a statement. -/
def stmG (G : GroupRow) : GE × (s.cIn.J → GE) := (readE G.target, vecG s G)

/-- With the stage's numbers of row bits the two vectors of coefficients are one. -/
theorem vecG_eq_vecGk (G : GroupRow) : vecG s G = vecGk s (s.h + s.g) s.h G := by
  funext j
  rcases j with x | x <;> rfl

/-- With the stage's numbers of row bits the two statements are one. -/
theorem stmG_eq (G : GroupRow) : stmG s G = stmGk s (s.h + s.g) s.h G :=
  Prod.ext rfl (vecG_eq_vecGk s G)

/-- The coefficients of the program's claim on the three folded rows: on the main row's message, on
the carried mask row's, on the fresh mask row's. -/
def vecS (R : SingleRows) : s.cMid.J → GE
  | .inl j => formAt R.c j.val
  | .inr (.inl j) => readV (R.d.getD 0 #[]) j.val
  | .inr (.inr j) => readV (R.d.getD 1 #[]) j.val

/-- The program's claim on the three folded rows, as a statement. -/
def stmS (R : SingleRows) : GE × (s.cMid.J → GE) := (readE R.target, vecS s R)

/-- The symbols that the program has read of the three folded rows at the position x. The array
y holds, for each listed position in turn, one symbol for each row. -/
def symS (R : SingleRows) (pos : Positions) (y : Array E) (x : ℕ) : s.cMid.Aa → GE
  | .inl _ => readV y ((pos.indexOf x).getD 0 * R.rows)
  | .inr (.inl _) => readV y ((pos.indexOf x).getD 0 * R.rows + R.maskRow 0)
  | .inr (.inr _) => readV y ((pos.indexOf x).getD 0 * R.rows + R.maskRow 1)

end

end OnBytes.Slice

#print axioms OnBytes.Slice.rdE_val
#print axioms OnBytes.Slice.vecG_eq_vecGk
#print axioms OnBytes.Slice.stmG_eq
