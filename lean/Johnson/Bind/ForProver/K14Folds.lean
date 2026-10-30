-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/K14Folds.lean: THE FOLD OF THE ROWS, THE FOLDED ROW, omega_col AND THE
SCALAR'S FUNCTION (Johnson/Desc/K14/Honest/Coded.lean), TAKEN AT THE ROWS OF
`ProofFile.Honest.K14.rowsOf`, ARE THE SAME AT `rowLaidE` (Johnson/Bind/ForProver/K14Rows.lean), WHERE THE
TEST `rowsFit` PASSES. The folded row and omega_col at `rowsOf` are the data of the two sendings
(Johnson/Desc/ProofFile/Honest/K14/Sendings.lean). By its text the scalar of the part at "SPLIT" is
that function's at `entriesOf`, not at `rowsOf`: of that term this file says nothing. Statements and
proofs.

Main names (namespace `Bind.ForProver`).
  `sumE_congr`: the programs' sum over the numbers below n reads its summands below n alone.
  **`foldRowsE_eq`**: where `rowsFit` passes: at every function ω of coefficients and every place
    the fold of the 2^v rows is the same at the two texts of the rows.
  `uAtE_eq`, `omegaAtE_eq`, `muAtE_eq`: so are the folded row, omega_col and the scalar's function.

Limits. Those of Johnson/Bind/ForProver/K14Rows.lean. Equations between terms on the programs'
elements: nothing is read into a field here. Nothing on the encoder, so not that the fold of a
column's symbols is the folded row's symbol. The pads and tails in these statements are those of the
table's rows (ρ): at their places the folded row is their fold, the same at the two texts. What the
folded row gets as a sent message of its own (the pad of its own OOD sample: "no part of these
vectors", Johnson/Desc/K14/Honest/Coded.lean's head) has no term here; the mask entry kappa is a
letter in `muAtE_eq`, the same on both sides. No completeness, no index privacy; nothing on any
program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.K14Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (E zeroE)
open OnBytes.Params (LinShape)
open ProofFile.Honest (TableRand Weights)
open Desc.K14.Honest (foldRowsE uHonE uAtE omegaAtE muAtE)

/-- The programs' sum over the numbers below n reads its summands below n alone. -/
theorem sumE_congr (n : ℕ) (f g : ℕ → E) :
    (∀ j, j < n → f j = g j) → Desc.K14.Law.sumE n f = Desc.K14.Law.sumE n g := by
  unfold Desc.K14.Law.sumE
  induction n with
  | zero =>
    intro _
    rw [List.range_zero, List.foldl_nil, List.foldl_nil]
  | succ n ih =>
    intro h
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons,
      List.foldl_nil, List.foldl_nil, ih fun j hj => h j (Nat.lt_succ_of_lt hj),
      h n (Nat.lt_succ_self n)]

section
variable (S : LinShape) (w : Weights) (ρ : TableRand)
  (hfit : rowsFit (shapeOfIndex S.fold.index) S.kLo S.matrixRows = true)
include hfit

/-- **Where `rowsFit` passes, the fold of the table's rows is the same at the two texts.** -/
theorem foldRowsE_eq (ω : ℕ → E) (k : ℕ) :
    foldRowsE S.fold.index.rows ω (ProofFile.Honest.K14.rowsOf S w ⟨ρ.pad, ρ.tail⟩) k =
      foldRowsE S.fold.index.rows ω (rowLaidE S w ρ) k := by
  unfold foldRowsE
  refine sumE_congr _ _ _ fun r hr => ?_
  rw [rowsOf_eq S w ρ hfit r k hr]

/-- So is the folded row at the shared point. -/
theorem uAtE_eq (psi : List E) :
    uAtE S psi (ProofFile.Honest.K14.rowsOf S w ⟨ρ.pad, ρ.tail⟩) = uAtE S psi (rowLaidE S w ρ) := by
  funext k
  unfold uAtE uHonE
  rw [foldRowsE_eq S w ρ hfit]

/-- So is omega_col. -/
theorem omegaAtE_eq (psi : List E) :
    omegaAtE S psi (ProofFile.Honest.K14.rowsOf S w ⟨ρ.pad, ρ.tail⟩) =
      omegaAtE S psi (rowLaidE S w ρ) := by
  unfold omegaAtE
  rw [uAtE_eq S w ρ hfit]

/-- So is the scalar's function at these rows. The scalar of the part at "SPLIT" is at
`entriesOf`. -/
theorem muAtE_eq (psi z : List E) (kappa : E) :
    muAtE S psi z (ProofFile.Honest.K14.rowsOf S w ⟨ρ.pad, ρ.tail⟩) kappa =
      muAtE S psi z (rowLaidE S w ρ) kappa := by
  unfold muAtE
  rw [omegaAtE_eq S w ρ hfit]

end

end Bind.ForProver

#print axioms Bind.ForProver.sumE_congr
#print axioms Bind.ForProver.foldRowsE_eq
#print axioms Bind.ForProver.uAtE_eq
#print axioms Bind.ForProver.omegaAtE_eq
#print axioms Bind.ForProver.muAtE_eq
