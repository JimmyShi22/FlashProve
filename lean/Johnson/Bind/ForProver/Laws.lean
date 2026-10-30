-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/Laws.lean: laws on the encoded index's column for an honest prover
(Johnson/Bind/ForProver/Enc.lean). Statements and proofs; general in the shape.

Main names (namespace `Bind.ForProver`).
   `words_columnOf`, `encAt_words`: read as words, the column of `encAt` is the column of the
      stand-in committer on byte strings (`Bind.Twin.columnOf`, Johnson/Bind/Twin.lean). This is a
      way there and back (a word below p, read in the field and written again): it says nothing on
      what the table holds.
   `encAt_length`, `encAt_beyond`: a column has 2^v entries; from 2^a on there is none.
   `randOf c`, **`columnOf_randOf`**: the committer's coins c, read in the field. At these the table
      of this folder and the committer's own table `Bind.Twin.Table.of entry c` have the same
      columns: at every shape, whatever the raw words and the salts.
   `coinsOf ρ salt`, `randOf_coinsOf`: every value ρ of the frame's type of coins is `randOf` of
      some coins of the committer, at any salts.
   `toF_message`, `toF_tailOf`: `rowMsgF` below l and `rowTailF` below r
      (Johnson/Bind/ForProver/Rows.lean) are the committer's message and tail of a row, read in the
      field. (Where 3 s exceeds l the committer's list goes on with pads from l on; `rowMsgF` is 0.)
   `rowValueF sh entry ρ b z`: the value at z of the row's polynomial: its lowest r coefficients are
      `rowTailF`, the next l are `rowMsgF`. A sum; no term of a type of polynomials.
   **`encAt_values`**: the column of `encAt` at a position x below 2^a is, row by row, that value
      at the position's point (`Fmt.M1.point`, read in the field).
   `encW_fit`, `encW_item`, `encW_unfit`: `encW` is `encAt` at the item 0 where the test `rowsFit`
      passes; it gives nothing at another item, and nothing where the test fails.
   **`encW_values`**: `encAt_values` off a public part, where the test passes.
Limits. Equations between this library's own terms. Nothing here says that the points of two
positions differ (the library has it for a ≤ 32: `OnBytes.Slice.toF_point_inj`,
OnBytes/Slice/Points.lean; at files in scope, where the maker of the public part returns, at
positions below 2^32: `points_inScope`, Johnson/Bind/ForProver/ShapeInScope.lean), that a table
decodes, or what the matrix holds. Where the
maker of the public part returns, in the goals' scope `rowsFit` passes and the shape is the full
size's (`rowsFit_inScope`, `shapeOf_inScope`, ShapeInScope.lean); at other files `rowsFit` is not
shown here (by reading, `made_parts`, `sized_tests`, `linOk_ok`, `rowsFit_of_ok` give it); that it
returns the side library proves at the library's written copies of the two stored sets, in scope
(StartAtWrittenFiles.lean), and Johnson/Second/Seam/SeatFacts.lean evaluates at its written copies
of the small stored example's files, which are out of scope; no theorem of this file says that it
returns at any files. `rowsFit_of_ok` (Johnson/Bind/ForProver/K14Rows.lean) gives the test from the
verifier's own test on the shape. Nothing on the OOD answers, on a hash tree or on a commitment ID.
This file writes no honest prover. Nothing on completeness, on index privacy or on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.Enc
import Johnson.Bind.Column
import Johnson.Bind.TwinRows
import OnBytes.Slice.SimBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes.Slice (toF ofF)
open ProofFile.Honest (TableRand Weights)
open Bind.Twin (Shape Table columnOf laid message tailOf residue)

/-! ### Lists -/

/-- Entry i of a function's values at 0, 1, .., n - 1. -/
theorem getD_map_range {α : Type} (f : ℕ → α) (n i : ℕ) (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact h),
    List.getElem_map, List.getElem_range]

/-! ### The column as words -/

/-- A column of the stand-in committer, read in the field and written again, is itself: each of its
words is below p. -/
theorem words_columnOf (sh : Shape) (rows : List (List UInt64 × List UInt64)) (x : ℕ) :
    ((columnOf sh rows x).map toF).map ofF = columnOf sh rows x := by
  rw [List.map_map]
  refine (List.map_congr_left fun w hw => ?_).trans (List.map_id _)
  show ofF (toF w) = id w
  rw [Bind.Column.ofF_toF, Bind.Twin.residue_of_ok w (Bind.Column.ok_columnOf _ _ _ w hw)]
  rfl

/-- **Read as words, the column is the committer's.** -/
theorem encAt_words (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (x : ℕ)
    (hx : x < 2 ^ sh.a) :
    (encAt sh entry ρ x).map (fun c => c.map ofF) =
      some (columnOf sh (laid sh (tableOfRand entry ρ)) x) := by
  unfold encAt
  rw [if_pos hx]
  show some (((columnOf sh (laid sh (tableOfRand entry ρ)) x).map toF).map ofF) = _
  rw [List.map_map]
  refine congrArg some ((List.map_congr_left fun w hw => ?_).trans (List.map_id _))
  show ofF (toF w) = id w
  rw [Bind.Column.ofF_toF, Bind.Twin.residue_of_ok w (Bind.Column.ok_columnOf _ _ _ w hw)]
  rfl

/-- A column has an entry for each row. -/
theorem encAt_length (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (x : ℕ)
    (c : List Cb.Gl.F) (h : encAt sh entry ρ x = some c) : c.length = 2 ^ sh.v := by
  unfold encAt at h
  by_cases hx : x < 2 ^ sh.a
  · rw [if_pos hx] at h
    cases h
    rw [List.length_map, Bind.Column.length_columnOf]
  · rw [if_neg hx] at h
    cases h

/-- From 2^a on there is no column. -/
theorem encAt_beyond (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (x : ℕ)
    (hx : 2 ^ sh.a ≤ x) : encAt sh entry ρ x = none := by
  unfold encAt
  rw [if_neg (Nat.not_lt.2 hx)]

/-! ### One table with the committer -/

/-- The committer's coins, read in the field: a word counts modulo p. The salts are left out. -/
def randOf (c : Bind.Twin.Coins) : TableRand :=
  ⟨fun b j => toF (c.pad b j), fun b q => toF (c.tail b q)⟩

/-- **At the committer's coins, read in the field, the columns are the committer's own.** -/
theorem columnOf_randOf (sh : Shape) (entry : ℕ → ℕ → UInt64) (c : Bind.Twin.Coins) :
    columnOf sh (laid sh (tableOfRand entry (randOf c))) =
      columnOf sh (laid sh (Table.of entry c)) := by
  funext x
  rw [Bind.Twin.columnOf_laid, Bind.Twin.columnOf_laid]
  refine List.map_congr_left fun b _ => Bind.Twin.symF_congr _ _ _ _ _ _ ?_ ?_
  · show ((List.range sh.plain).map (entry b) ++
        (List.range sh.pads).map fun j => ofF (toF (c.pad b j))).map residue =
      ((List.range sh.plain).map (entry b) ++ (List.range sh.pads).map (c.pad b)).map residue
    simp only [Bind.Column.ofF_toF]
    rw [List.map_append, List.map_append, Bind.Twin.map_residue_range]
  · show ((List.range sh.r).map fun q => ofF (toF (c.tail b q))).map residue =
      ((List.range sh.r).map (c.tail b)).map residue
    simp only [Bind.Column.ofF_toF]
    exact Bind.Twin.map_residue_range _ _

/-- Coins of the committer that are read as given coins in the field: each written as its word
below p; the salts are the argument, by its text: no law of this file reads them. -/
def coinsOf (ρ : TableRand) (salt : ℕ → ByteArray) : Bind.Twin.Coins :=
  ⟨fun b q => ofF (ρ.tail b q), fun b j => ofF (ρ.pad b j), salt⟩

/-- **Every value of the frame's type of coins is the reading of some coins of the committer.** -/
theorem randOf_coinsOf (ρ : TableRand) (salt : ℕ → ByteArray) : randOf (coinsOf ρ salt) = ρ := by
  have e1 : (fun b j => toF (ofF (ρ.pad b j))) = ρ.pad := by
    funext b j
    exact OnBytes.Slice.toF_ofF _
  have e2 : (fun b q => toF (ofF (ρ.tail b q))) = ρ.tail := by
    funext b q
    exact OnBytes.Slice.toF_ofF _
  show (⟨fun b j => toF (ofF (ρ.pad b j)), fun b q => toF (ofF (ρ.tail b q))⟩ : TableRand) = ρ
  rw [e1, e2]

/-! ### A row in the field -/

/-- Entry e of the committer's message of the row b, read in the field. -/
theorem toF_message (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (b e : ℕ)
    (he : e < sh.l) :
    toF ((message sh (tableOfRand entry ρ) b).getD e 0) = rowMsgF sh entry ρ b e := by
  show toF (((List.range sh.plain).map (entry b) ++
    (List.range sh.pads).map fun j => ofF (ρ.pad b j)).getD e 0) = _
  unfold rowMsgF
  by_cases hp : e < sh.plain
  · rw [if_pos hp, List.getD_append _ _ _ _ (by rw [List.length_map, List.length_range]; exact hp),
      getD_map_range _ _ _ _ hp]
  · have hq : e - sh.plain < sh.pads := by
      unfold Bind.Twin.Shape.plain Bind.Twin.Shape.pads at *
      omega
    rw [if_neg hp, if_pos he,
      List.getD_append_right _ _ _ _
        (by rw [List.length_map, List.length_range]; exact Nat.le_of_not_lt hp),
      List.length_map, List.length_range, getD_map_range _ _ _ _ hq, OnBytes.Slice.toF_ofF]

/-- Entry q of the committer's tail of the row b, read in the field. -/
theorem toF_tailOf (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (b q : ℕ)
    (hq : q < sh.r) :
    toF ((tailOf sh (tableOfRand entry ρ) b).getD q 0) = rowTailF ρ b q := by
  show toF (((List.range sh.r).map fun q => ofF (ρ.tail b q)).getD q 0) = ρ.tail b q
  rw [getD_map_range _ _ _ _ hq, OnBytes.Slice.toF_ofF]

/-! ### The column as values of the rows' polynomials -/

/-- The value at z of the polynomial of the row b: the lowest r coefficients are the tail's entries,
the next l the message's. -/
def rowValueF (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (b : ℕ) (z : Cb.Gl.F) :
    Cb.Gl.F :=
  (∑ q ∈ Finset.range sh.r, z ^ q * rowTailF ρ b q) +
    ∑ j ∈ Finset.range sh.l, z ^ (sh.r + j) * rowMsgF sh entry ρ b j

/-- **The column at a position is, row by row, the value of the row's polynomial at the position's
point.** -/
theorem encAt_values (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (x : ℕ)
    (hx : x < 2 ^ sh.a) :
    encAt sh entry ρ x =
      some ((List.range (2 ^ sh.v)).map fun b =>
        rowValueF sh entry ρ b (toF (Fmt.M1.point sh.a x))) := by
  unfold encAt
  rw [if_pos hx, Bind.Twin.columnOf_laid, List.map_map]
  refine congrArg some (List.map_congr_left fun b _ => ?_)
  show toF (Fmt.M1.symF sh.code x (message sh (tableOfRand entry ρ) b)
    (tailOf sh (tableOfRand entry ρ) b)) = _
  rw [OnBytes.Slice.toF_symF]
  show (∑ q ∈ Finset.range sh.r, toF (Fmt.M1.point sh.a x) ^ q *
        toF ((tailOf sh (tableOfRand entry ρ) b).getD q 0)) +
      ∑ j ∈ Finset.range sh.l, toF (Fmt.M1.point sh.a x) ^ (sh.r + j) *
        toF ((message sh (tableOfRand entry ρ) b).getD j 0) = _
  unfold rowValueF
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun q hq => ?_)
    (Finset.sum_congr rfl fun j hj => ?_)
  · rw [toF_tailOf sh entry ρ b q (Finset.mem_range.1 hq)]
  · rw [toF_message sh entry ρ b j (Finset.mem_range.1 hj)]

/-! ### Off the public part -/

/-- At the item 0, where the test passes. -/
theorem encW_fit (Z : ProofFile.Pub) (w : Weights) (rc : ℕ → TableRand) (x : ℕ)
    (h : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true) :
    encW Z w rc 0 x =
      encAt (shapeOf Z) (entryAtF (linOf Z).kLo (linOf Z).matrixRows (shapeOf Z).v w.entry) (rc 0)
        x := by
  unfold encW
  rw [if_pos ⟨rfl, h⟩]

/-- Nothing at another item. -/
theorem encW_item (Z : ProofFile.Pub) (w : Weights) (rc : ℕ → TableRand) (item x : ℕ) (h : item ≠ 0) :
    encW Z w rc item x = none := by
  unfold encW
  rw [if_neg fun k => h k.1]

/-- Nothing where the test fails. -/
theorem encW_unfit (Z : ProofFile.Pub) (w : Weights) (rc : ℕ → TableRand) (item x : ℕ)
    (h : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = false) :
    encW Z w rc item x = none := by
  unfold encW
  rw [if_neg fun k => by rw [h] at k; exact Bool.noConfusion k.2]

/-- **Off a public part, where the test passes: the column at the item 0 is, row by row, the value
of the row's polynomial at the position's point.** -/
theorem encW_values (Z : ProofFile.Pub) (w : Weights) (rc : ℕ → TableRand) (x : ℕ)
    (hfit : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true)
    (hx : x < 2 ^ (shapeOf Z).a) :
    encW Z w rc 0 x =
      some ((List.range (2 ^ (shapeOf Z).v)).map fun b =>
        rowValueF (shapeOf Z) (entryOfPub Z w) (rc 0) b (toF (Fmt.M1.point (shapeOf Z).a x))) := by
  rw [encW_fit Z w rc x hfit]
  exact encAt_values (shapeOf Z) (entryOfPub Z w) (rc 0) x hx

end Bind.ForProver

#print axioms Bind.ForProver.getD_map_range
#print axioms Bind.ForProver.words_columnOf
#print axioms Bind.ForProver.encAt_words
#print axioms Bind.ForProver.encAt_length
#print axioms Bind.ForProver.encAt_beyond
#print axioms Bind.ForProver.columnOf_randOf
#print axioms Bind.ForProver.randOf_coinsOf
#print axioms Bind.ForProver.toF_message
#print axioms Bind.ForProver.toF_tailOf
#print axioms Bind.ForProver.encAt_values
#print axioms Bind.ForProver.encW_fit
#print axioms Bind.ForProver.encW_item
#print axioms Bind.ForProver.encW_unfit
#print axioms Bind.ForProver.encW_values
#print axioms Bind.ForProver.randOf
#print axioms Bind.ForProver.coinsOf
#print axioms Bind.ForProver.rowValueF
