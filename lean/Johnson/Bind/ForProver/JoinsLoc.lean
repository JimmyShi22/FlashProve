-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/JoinsLoc.lean: JOINS: the equation (loc_x) of the linear claim's shared
rounds (the shared chain), as Johnson/Bind/ForProver/LocHonest.lean has it, AT `encW` OFF A VALUE OF
`ProofFile.Pub`, and with the column as words, in the form in which the description's own constraint reads
it. Statements and proofs.

Main names (namespace `Bind.ForProver`).
  `fit_of_encW`, `below_of_encW`, `encAt_of_encW`: where `encW` gives a column at the item 0, the
    test `rowsFit` passes, the position is below 2^a, and the column is `encAt`'s.
  **`locEq_at`**: at a value Z of `ProofFile.Pub` whose code has at most 2^32 positions, wherever `encW`
    gives a column at the item 0: `Desc.K14.Law.LocEq` holds between that column and the folded row
    that the shared rounds' honest side lays at the shape off Z, at the coefficients eq(gamma, r).
    One premise beside the bound on the code.
  `words_getD`: entry r of a column written as words, read as an array with the filler 0, is the
    word of the column's entry r with the filler 0.
  **`locEq_at_words`**: the same with the column as words: the form of `Desc.K14.Law.LocAt`
    (Johnson/Desc/K14/Law/LocSound.lean) for the table's column.

Limits. Z ranges over all values of the structure `ProofFile.Pub`, made of three public files or not.
Where `rowsFit` passes `encW` gives a column at the item 0 at every position below 2^a (`encW_some`,
Johnson/Bind/ForProver/Declared.lean), and in the goals' scope it passes where the maker
`ProofFile.pubPlain` returns (`rowsFit_inScope`, ShapeInScope.lean of this folder); here hc is a premise.
That the columns which a run reads are `encW Z` is not said here. NOT `LocAt` AT A STATE OF A RUN:
that a state's coefficients are eq(gamma, r) and 2^v in number, and that the words of the sent table
at the folded row's places are `uAtE`, is not said here. At the reading `Reading.gl` and at no
other. No completeness of any protocol, no index privacy; nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.LocHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (E generatorAt)
open OnBytes.Model (Reading)
open OnBytes.Slice (toF ofF)
open ProofFile.Honest (TableRand)
open Desc.K14.Law (LocEq)

section
variable (Z : ProofFile.Pub) (w : ProofFile.Honest.Weights) (rc : ℕ → TableRand) (x : ℕ) (col : List Cb.Gl.F)
  (hc : encW Z w rc 0 x = some col)
include hc

/-- Where `encW` gives a column the test passes. -/
theorem fit_of_encW : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true := by
  cases hb : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows with
  | true => rfl
  | false =>
    rw [encW_unfit Z w rc 0 x hb] at hc
    cases hc

/-- The column is `encAt`'s. -/
theorem encAt_of_encW :
    encAt (shapeOf Z) (entryAtF (linOf Z).kLo (linOf Z).matrixRows (shapeOf Z).v w.entry) (rc 0) x =
      some col := by
  rw [← encW_fit Z w rc x (fit_of_encW Z w rc x col hc)]
  exact hc

/-- The position is below 2^a. -/
theorem below_of_encW : x < 2 ^ (shapeOf Z).a := by
  refine Nat.lt_of_not_le fun h => ?_
  have h2 := encAt_of_encW Z w rc x col hc
  rw [encAt_beyond _ _ _ _ h] at h2
  cases h2

/-- **(loc_x)'s equation at `encW`'s column.** -/
theorem locEq_at (ha : (shapeOf Z).a ≤ 32) (psi : List E) :
    LocEq Reading.gl (linOf Z).fold (generatorAt (linOf Z).fold.index.code x)
      (fun r => Reading.gl.val (Desc.K14.Law.eqE (psi.drop (linOf Z).kLo) r)) (2 ^ (shapeOf Z).v)
      (fun r => Reading.gl.val (OnBytes.ofF (ofF (col.getD r 0))))
      (fun k => Reading.gl.val (Desc.K14.Honest.uAtE (linOf Z) psi
        (ProofFile.Honest.K14.rowsOf (linOf Z) w ⟨(rc 0).pad, (rc 0).tail⟩) k)) :=
  locEq_uAtE (linOf Z) ha x (below_of_encW Z w rc x col hc) w (rc 0) col
    (encAt_of_encW Z w rc x col hc) (fit_of_encW Z w rc x col hc) psi

end

/-- Entry r of a column written as words, as an array with the filler 0. -/
theorem words_getD (col : List Cb.Gl.F) (r : ℕ) :
    (col.map ofF).toArray.getD r 0 = ofF (col.getD r 0) := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
    getD_map_ofF]

/-- **The same with the column as words.** -/
theorem locEq_at_words (Z : ProofFile.Pub) (w : ProofFile.Honest.Weights) (rc : ℕ → TableRand) (x : ℕ)
    (col : List Cb.Gl.F) (hc : encW Z w rc 0 x = some col) (ha : (shapeOf Z).a ≤ 32)
    (psi : List E) :
    LocEq Reading.gl (linOf Z).fold (generatorAt (linOf Z).fold.index.code x)
      (fun r => Reading.gl.val (Desc.K14.Law.eqE (psi.drop (linOf Z).kLo) r)) (2 ^ (shapeOf Z).v)
      (fun r => Reading.gl.val (OnBytes.ofF ((col.map ofF).toArray.getD r 0)))
      (fun k => Reading.gl.val (Desc.K14.Honest.uAtE (linOf Z) psi
        (ProofFile.Honest.K14.rowsOf (linOf Z) w ⟨(rc 0).pad, (rc 0).tail⟩) k)) := by
  have h := locEq_at Z w rc x col hc ha psi
  simp only [words_getD]
  exact h

end Bind.ForProver

#print axioms Bind.ForProver.fit_of_encW
#print axioms Bind.ForProver.encAt_of_encW
#print axioms Bind.ForProver.below_of_encW
#print axioms Bind.ForProver.locEq_at
#print axioms Bind.ForProver.words_getD
#print axioms Bind.ForProver.locEq_at_words
