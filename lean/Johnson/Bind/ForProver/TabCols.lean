-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/TabCols.lean: WHERE THE TEST `rowsFit` PASSES, `encW` GIVES AT THE ITEM 0, AT
EVERY POSITION, A COLUMN OF THE DECLARED WIDTH; WHERE MOREOVER THE CODE HAS AT MOST 2^32 POSITIONS,
EACH WORD OF IT, READ, IS THE PROGRAMS' GENERATOR ROW APPLIED TO THAT ROW BEFORE ENCODING, in the
text of the own rows of the honest side of the linear claim's shared rounds (the shared chain)
(`ProofFile.Honest.K14.rowsOf`). Definitions, statements and proofs.

Why. Laws that carry the constraint (loc_x) to a state of a run take a committed table as a letter,
with premises on it. The library's `locAt_of_rows` and `nearAt_of_foldRowsB`
(Johnson/Desc/K14/Law/NearRows.lean) take what `tab_at` shows (their hcol), with the number of the
state's coefficients in the place of 2^v. Here `cols_at` shows the width and `tab_at` that equation,
of the words of `encW`, in that form: the left side reads the table's words as an array with the
filler 0; the right side is the library's `genK` (Johnson/Desc/K14/Law/NearRows.lean).

Main names (namespace `Bind.ForProver`).
  `storedW Z w rc item x`: `encW`'s column written as words.
  **`storedWords_encW`**: at a prover whose field `stored` is `encW Z`, the words that a run reads
    of it (`ProofFile.Honest.Prover.storedWords`, Johnson/Desc/ProofFile/Honest/Frame.lean) are `storedW
    Z`. `storedWords_encW_at`: the same at a prover that reads the index in another type, through a
    reader of it.
  **`cols_at`**: where the test `rowsFit` passes: at the declared item and every position below 2^a,
    a the declared depth, there is a column, and it has the declared width (`declaredAt`,
    Johnson/Bind/ForProver/Declared.lean).
  **`tab_at`**: where moreover the code has at most 2^32 positions: at every such position and every
    row below 2^v: the row's word in the column, read, is `genK` at `rowsOf` of that row, read.
  **`locEq_stored`**: under the same two premises, at every such position: the equation (loc_x)
    (`Desc.K14.Law.LocEq`) holds between these words and the folded row that the shared rounds'
    honest side lays, at the coefficients eq(gamma, r) (by `locEq_at_words`,
    Johnson/Bind/ForProver/JoinsLoc.lean).

Limits. One committed table; which of the protocol's tables it is, the first or a copy, is not said
here. Z ranges over all values of the structure `ProofFile.Pub`, made of three public files or not; that
the two public premises hold is said elsewhere of every Z that the maker of the public part returns
at files in the goals' scope (`rowsFit_inScope`, `a_inScope`,
Johnson/Bind/ForProver/ShapeInScope.lean; Johnson/Bind/ForProver/InScope.lean); that it returns at
any files is no theorem of this file. No theorem of this file applies to `storedW` a law that takes
what `cols_at` and `tab_at` show as premises: in this file that the forms fit is read, not compiled.
That any prover's field `stored` is `encW Z`, at its own reader of the index where it has one, is a
premise of `storedWords_encW` and `storedWords_encW_at` and is said of no prover here. Nothing on
the other things that these laws ask (the OOD answers, the key, the seeds; together at one input:
Johnson/Bind/ForProver/FiveAt.lean). At the reading `Reading.gl` and at no other. No completeness of
any protocol, no index privacy; nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.JoinsLoc
import Johnson.Bind.ForProver.Declared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes.Model (Reading)
open OnBytes.Slice (toF ofF)
open ProofFile.Honest (TableRand)
open Desc.K14.Law (genK)

/-- `encW`'s column, written as words. -/
def storedW (Z : ProofFile.Pub) (w : ProofFile.Honest.Weights) (rc : ℕ → TableRand) (item x : ℕ) :
    Option (List UInt64) :=
  (encW Z w rc item x).map fun c => c.map ofF

/-- **At a prover whose field `stored` is `encW Z` a run reads `storedW Z`.** -/
theorem storedWords_encW {Xi Ky Tr X₀ X : Type}
    (H : ProofFile.Honest.Prover ProofFile.Honest.Weights (ℕ → TableRand) Xi Ky Tr X₀ X) (Z : ProofFile.Pub)
    (h : H.stored = encW Z) : H.storedWords = storedW Z := by
  funext w rc item x
  unfold ProofFile.Honest.Prover.storedWords storedW
  rw [h]

/-- The same at a prover that reads the index in another type, through a reader of it. -/
theorem storedWords_encW_at {W₀ Xi Ky Tr X₀ X : Type}
    (H : ProofFile.Honest.Prover W₀ (ℕ → TableRand) Xi Ky Tr X₀ X) (Z : ProofFile.Pub)
    (weights : W₀ → ProofFile.Honest.Weights) (h : ∀ w, H.stored w = encW Z (weights w)) (w : W₀) :
    H.storedWords w = storedW Z (weights w) := by
  funext rc item x
  unfold ProofFile.Honest.Prover.storedWords storedW
  rw [h]

section
variable (Z : ProofFile.Pub)
  (hfit : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true)
  (w : ProofFile.Honest.Weights) (rc : ℕ → TableRand)
include hfit

/-- **Where `rowsFit` passes, at the declared item and every position there is a column of the
declared width.** -/
theorem cols_at (l : List (ℕ × ℕ)) (p : ℕ) (hp : p < 2 ^ (declaredAt Z l).sh.a) :
    ∃ u, storedW Z w rc (declaredAt Z l).item p = some u ∧
      u.length = (declaredAt Z l).sh.W := by
  have hs := encW_some Z l w rc p hfit hp
  obtain ⟨col, hcol⟩ := Option.isSome_iff_exists.1 hs
  refine ⟨col.map ofF, ?_, ?_⟩
  · show (encW Z w rc 0 p).map (fun c => c.map ofF) = _
    rw [hcol]
    rfl
  · rw [List.length_map]
    exact encW_width Z l w rc p col hcol

/-- **Where `rowsFit` passes and the code has at most 2^32 positions, each word of the column, read,
is the programs' generator row applied to that row before encoding.** -/
theorem tab_at (ha : (shapeOf Z).a ≤ 32) (x : ℕ) (hx : x < 2 ^ (linOf Z).fold.index.code.logN)
    (r : ℕ) (hr : r < (linOf Z).fold.index.rows) :
    Reading.gl.val (OnBytes.ofF (((storedW Z w rc 0 x).getD []).toArray.getD r 0)) =
      genK Reading.gl (linOf Z).fold x (fun j => Reading.gl.val
        (ProofFile.Honest.K14.rowsOf (linOf Z) w ⟨(rc 0).pad, (rc 0).tail⟩ r j)) := by
  have hs := encW_some Z [] w rc x hfit hx
  obtain ⟨col, hcol⟩ := Option.isSome_iff_exists.1 hs
  have hc := encAt_of_encW Z w rc x col hcol
  have e : (fun j => Reading.gl.val
      (ProofFile.Honest.K14.rowsOf (linOf Z) w ⟨(rc 0).pad, (rc 0).tail⟩ r j)) =
      fun j => Reading.gl.val (rowLaidE (linOf Z) w (rc 0) r j) :=
    funext fun j => by rw [rowsOf_eq (linOf Z) w (rc 0) hfit r j hr]
  unfold storedW
  rw [hcol, e, Option.map_some, Option.getD_some, words_getD]
  exact symbol_is_generatorRow (linOf Z) ha x hx w (rc 0) col hc r hr

/-- **(loc_x)'s equation at the words of `encW`'s column**, under the same two premises: the column
in the form in which `Desc.K14.Law.LocAt` reads a table's. -/
theorem locEq_stored (ha : (shapeOf Z).a ≤ 32) (x : ℕ)
    (hx : x < 2 ^ (linOf Z).fold.index.code.logN) (psi : List OnBytes.E) :
    Desc.K14.Law.LocEq Reading.gl (linOf Z).fold
      (OnBytes.generatorAt (linOf Z).fold.index.code x)
      (fun r => Reading.gl.val (Desc.K14.Law.eqE (psi.drop (linOf Z).kLo) r)) (2 ^ (shapeOf Z).v)
      (fun r => Reading.gl.val (OnBytes.ofF (((storedW Z w rc 0 x).getD []).toArray.getD r 0)))
      (fun k => Reading.gl.val (Desc.K14.Honest.uAtE (linOf Z) psi
        (ProofFile.Honest.K14.rowsOf (linOf Z) w ⟨(rc 0).pad, (rc 0).tail⟩) k)) := by
  obtain ⟨col, hcol⟩ := Option.isSome_iff_exists.1 (encW_some Z [] w rc x hfit hx)
  have e : (storedW Z w rc 0 x).getD [] = col.map ofF := by
    unfold storedW
    rw [hcol]
    rfl
  rw [e]
  exact locEq_at_words Z w rc x col hcol ha psi

end

end Bind.ForProver

#print axioms Bind.ForProver.storedWords_encW
#print axioms Bind.ForProver.storedWords_encW_at
#print axioms Bind.ForProver.cols_at
#print axioms Bind.ForProver.tab_at
#print axioms Bind.ForProver.locEq_stored
#print axioms Bind.ForProver.storedW
