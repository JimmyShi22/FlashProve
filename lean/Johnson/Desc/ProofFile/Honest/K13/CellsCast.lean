-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/CellsCast.lean: kind K13, the members' batching: A CAST's
IDENTITY: THE CELL OF THE LIBRARY's MATRIX OF AN INDEX (`Flat.matrixOf`,
Johnson/Flat/ThreeFull.lean) AT A ROW AND A COLUMN IS THE VALUE THAT THE KIND's PARTS MAKE OF THE
INDEX's ENTRY THERE (`Reading.gl.val (eOfF (entryOf i a C))`). VALUES OF THE INDEX's OWN ENTRIES:
NOT TO STAND IN FRONT OF A LAW OVER COINS. Three statements with their proofs; two evaluations at
numbers; no definition. No thread, no Script, no prover, no hypothesis is named. NO PROPERTY IS
CLAIMED.

Main names. `val_eOfF`: the program's element made of a base-field element (`eOfF`,
Honest/ForKinds.lean) reads (`Reading.gl`, OnBytes/Model/HideLaws.lean) as that element's image in
the extension field. `val_eOfF_entryOf`: at the first reader of the index
(`OnBytes.HonestTrace.entryOf`, Johnson/HonestTrace/IndexReaders.lean): the cast of the integer
entry. `cellAtNo_matrixOf_entryOf`: **`cellAtNo (Flat.matrixOf i) a C` is that value, AT EVERY ROW
AND COLUMN: no bound is asked**: outside the reference shape both sides are 0.

How. The reading is `Slice.toE` of the triple; `eOfF` lays (ofF y, 0, 0); the library's
`Slice.toE_ofF` and `Slice.toF_ofF` (OnBytes/Slice/Field.lean). A ring map takes the cast of an
integer to its cast. Inside the shape `cellAtNo` (Johnson/Desc/K13/Law/MatOfCells.lean) is the
matrix's entry, by its text the cast; outside it is 0, and so is the entry (`entryOf_out`).

What it is for. `MatTie`'s right side (MatTieAtHead.lean of this folder) at a Script whose cells are
the matrix of the input's index, and at the reader fun i => ⟨entryOf i⟩: MatTieOfCells.lean.

Limits. AT THE REFERENCE SIZES (`hRef` rows, 2 ^ `kRef` columns) AND AT `Cm.Idx` ALONE. An equation
between two casts of one integer: it says nothing of what a prover stores, sends or commits to. The
two evaluations hold the first law at the numbers 7 and the prime less 1.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness, hiding
or binding.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.K13.Law.MatOfCells
import Johnson.HonestTrace.IndexReaders
import Johnson.Flat.ThreeFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes.Model (Reading)
open VerifiableInference.Desc.K13.Law (cellAtNo)
open Inst.Model.Layout (kRef hRef)

/-- The program's element made of a base-field element reads as its image in the extension field. -/
theorem val_eOfF (y : Cb.Gl.F) : Reading.gl.val (eOfF y) = algebraMap Cb.Gl.F Cb.Gl.E y := by
  show OnBytes.Slice.toE (OnBytes.E.ofTriple (OnBytes.Slice.ofF y, 0, 0)).triple = _
  rw [OnBytes.E.triple_ofTriple]
  have e := OnBytes.Slice.toE_ofF (OnBytes.Slice.ofF y)
  rw [OnBytes.Slice.toF_ofF] at e
  exact e

-- the first law, held at numbers: 7, and the prime less 1
#guard OnBytes.Slice.ofE (Reading.gl.val (eOfF (OnBytes.Slice.toF 7))) == (7, 0, 0)
#guard OnBytes.Slice.ofE (Reading.gl.val (eOfF (OnBytes.Slice.toF 18446744069414584320))) ==
  (18446744069414584320, 0, 0)

/-- At the first reader of the index: the cast of the integer entry. -/
theorem val_eOfF_entryOf (i : Cm.Idx) (a C : ℕ) :
    Reading.gl.val (eOfF (OnBytes.HonestTrace.entryOf i a C)) = ((i.mat a C : ℤ) : Cb.Gl.E) := by
  rw [val_eOfF]
  show algebraMap Cb.Gl.F Cb.Gl.E ((i.mat a C : ℤ) : Cb.Gl.F) = _
  exact map_intCast _ _

/-- **AT EVERY ROW AND COLUMN, NO BOUND**: outside the reference shape both sides are 0. -/
theorem cellAtNo_matrixOf_entryOf (i : Cm.Idx) (a C : ℕ) :
    cellAtNo (VerifiableInference.OnPublicFiles.Flat.matrixOf i) a C =
      Reading.gl.val (eOfF (OnBytes.HonestTrace.entryOf i a C)) := by
  by_cases hb : a < hRef ∧ C < 2 ^ kRef
  · rw [val_eOfF_entryOf]
    unfold cellAtNo
    rw [dif_pos hb]
    rfl
  · rw [OnBytes.HonestTrace.entryOf_out i hb, val_eOfF, map_zero]
    unfold cellAtNo
    rw [dif_neg hb]

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.val_eOfF
#print axioms ProofFile.Honest.K13.val_eOfF_entryOf
#print axioms ProofFile.Honest.K13.cellAtNo_matrixOf_entryOf
