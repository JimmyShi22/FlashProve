-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/ShapeInScope.lean: at every three public files in the goals' scope, at every
value of the argument that stands for the format's second hash function, and at every public part
that the proof file's own maker of the public part (`ProofFile.pubPlain`) returns of these files: the
shape and the matrix's two numbers off that public part (Johnson/Bind/ForProver/Enc.lean) are the
full size's, and the test on room passes. Statements and proofs; no definition.

On what it rests. The library's own theorems on the planner in scope: `Lk6.AtPlan.fullShape_pub`
(Johnson/Goal/PlanValues/ProofShapeAtPlain.lean): the shape of the proof file's test on the
committed table passes `Desc.K14.Law.fullShapeB` (Johnson/Desc/Sound/PlanAsk.lean): the table's
code, its 2^11 rows, its one OOD answer a row, the matrix's 3076096 rows, 2^7 of its columns in a
row of the table; and `VerifierAndGoals.Sizes.atFull_of_pub` (Johnson/Goal/Numbers/ProofSizesAtPub.lean),
whose field on the table's shape gives the salt's length as that of a closed term, which the kernel
evaluates here.

Main names (namespace `Bind.ForProver`), each under the two premises "in scope" and "the maker
returned Z".
   `fullShape_linOf`: `fullShapeB (linOf Z)`.
   `kLo_inScope`, `matrixRows_inScope`, `salt_inScope`: 7, 3076096, 40.
   **`shapeOf_inScope`**: `shapeOf Z` is (a, l, r, v, s, sigma) =
      (32, 402653184, 44040191, 11, 1, 40): the numerals of `Bind.Column.shFull`
      (Johnson/Bind/ColumnSizes.lean); `shapeAtFull_inScope` (Johnson/Bind/ForProver/InScope.lean)
      says it by that name.
   **`rowsFit_inScope`**: the test `rowsFit` passes at Z. (No theorem of this file has it
      without the premise "in scope".)
   `a_inScope`, `room_inScope`: a ≤ 32, and l + r ≤ 2^a. `points_inScope`: so the points of two
      positions below 2^32 differ (by the library's `OnBytes.Slice.toF_point_inj`).
   `encW_inScope`: so `encW` at the item 0 is `encAt` at these numbers.
Limits. One direction: from a maker that returns. No theorem of this file shows a public part that
meets the two premises (the side library proves that the maker returns at the two stored full-size
sets: `okStart_zFull_whole`, `okStart_zGap_whole`, AtFullSide/E2E/StartAtWrittenFiles.lean, by the
field `pub` of `LaidAt`, Johnson/P5J/LaidOpens.lean). Nothing at files out of scope. Nothing here on
the verifier's whole test on the shape (`OnBytes.Params.LinShape.ok`). This file writes no honest
prover. Nothing on soundness, on completeness, on index privacy or on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.Laws
import Johnson.Goal.PlanValues.ProofShapeAtPlain
import Johnson.Goal.Numbers.ProofSizesAtPub
import OnBytes.Slice.Points

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open ProofFile.Honest (TableRand Weights)
open Desc.K14.Law (fullShapeB full_index)

/-- The salt's length in the closed term that the library's theorem names. -/
theorem salt_written :
    (OnBytes.Params.indexShapeOf OnBytes.Params.recordSet
      OnBytes.Params.recordTable).saltBytes = 40 := by
  decide +kernel

section
variable {P : VerifierAndGoals.PublicFiles} (hP : VerifierAndGoals.InScope P = true) {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub}
  (h : ProofFile.pubPlain o P.pol P.lay P.KL = .ok Z)
include hP h

/-- The library's test on the plan passes at the shape that `linOf` reads. -/
theorem fullShape_linOf : fullShapeB (linOf Z) = true := Lk6.AtPlan.fullShape_pub hP h

/-- A row of the table holds 2^7 columns of the matrix. -/
theorem kLo_inScope : (linOf Z).kLo = 7 := by
  have k := fullShape_linOf hP h
  unfold fullShapeB at k
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at k
  exact k.2

/-- The matrix has 3076096 rows. -/
theorem matrixRows_inScope : (linOf Z).matrixRows = 3076096 := by
  have k := fullShape_linOf hP h
  unfold fullShapeB at k
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at k
  exact k.1.2

/-- A leaf's salt has 40 bytes. -/
theorem salt_inScope : (linOf Z).fold.index.saltBytes = 40 := by
  have e : (linOf Z).fold.index =
      OnBytes.Params.indexShapeOf OnBytes.Params.recordSet OnBytes.Params.recordTable :=
    (VerifierAndGoals.Sizes.atFull_of_pub hP (show ProofFile.pureRoad.pub o P.pol P.lay P.KL = .ok Z from h)).index
  rw [e, salt_written]

/-- **The committer's shape off the public part is the full size's**: the six numerals of
`Bind.Column.shFull` (Johnson/Bind/ColumnSizes.lean). -/
theorem shapeOf_inScope : shapeOf Z = ⟨32, 402653184, 44040191, 11, 1, 40⟩ := by
  have hi := full_index (linOf Z) (fullShape_linOf hP h)
  have a1 : (linOf Z).fold.index.code.logN = 32 := by rw [hi]
  have a2 : (linOf Z).fold.index.code.ell = 402653184 := by rw [hi]
  have a3 : (linOf Z).fold.index.code.r = 44040191 := by rw [hi]
  have a4 : (linOf Z).fold.index.v = 11 := by rw [hi]
  have a5 : (linOf Z).fold.index.answers = 1 := by rw [hi]
  unfold shapeOf shapeOfIndex
  rw [a1, a2, a3, a4, a5, salt_inScope hP h]

/-- **The test on room passes.** -/
theorem rowsFit_inScope : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true := by
  rw [shapeOf_inScope hP h, kLo_inScope hP h, matrixRows_inScope hP h]
  decide

/-- a ≤ 32: what the library's law on the positions' points asks (`OnBytes.Slice.toF_point_inj`,
OnBytes/Slice/Points.lean). -/
theorem a_inScope : (shapeOf Z).a ≤ 32 := by
  rw [shapeOf_inScope hP h]

/-- A row's polynomial has no more coefficients than there are positions. -/
theorem room_inScope : (shapeOf Z).l + (shapeOf Z).r ≤ 2 ^ (shapeOf Z).a := by
  rw [shapeOf_inScope hP h]
  decide

/-- **The points of two positions differ.** -/
theorem points_inScope {x y : ℕ} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32)
    (e : OnBytes.Slice.toF (Fmt.M1.point (shapeOf Z).a x) =
      OnBytes.Slice.toF (Fmt.M1.point (shapeOf Z).a y)) : x = y := by
  rw [shapeOf_inScope hP h] at e
  exact OnBytes.Slice.toF_point_inj 32 (Nat.le_refl 32) hx hy e

/-- So the encoded index's column at the item 0 is `encAt` at the full size's numbers. -/
theorem encW_inScope (w : Weights) (rc : ℕ → TableRand) (x : ℕ) :
    encW Z w rc 0 x =
      encAt ⟨32, 402653184, 44040191, 11, 1, 40⟩ (entryAtF 7 3076096 11 w.entry) (rc 0) x := by
  rw [encW_fit Z w rc x (rowsFit_inScope hP h), shapeOf_inScope hP h, kLo_inScope hP h,
    matrixRows_inScope hP h]

end

end Bind.ForProver

#print axioms Bind.ForProver.salt_written
#print axioms Bind.ForProver.fullShape_linOf
#print axioms Bind.ForProver.kLo_inScope
#print axioms Bind.ForProver.matrixRows_inScope
#print axioms Bind.ForProver.salt_inScope
#print axioms Bind.ForProver.shapeOf_inScope
#print axioms Bind.ForProver.rowsFit_inScope
#print axioms Bind.ForProver.a_inScope
#print axioms Bind.ForProver.room_inScope
#print axioms Bind.ForProver.points_inScope
#print axioms Bind.ForProver.encW_inScope
