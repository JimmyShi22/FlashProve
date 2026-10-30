-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/BoundsAtHead.lean: kind K13, the members' batching: UNDER THE
LIBRARY's HEAD h (`P5J.AtMgA`: a hypothesis, which has a member: `headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean; the full size, the format's second hash function): THE PLAN's MATRIX
HAS THE REFERENCE SHAPE; SO IN THE RANGE OF `MatTie`'s RIGHT SIDE (MatTieAtHead.lean of this folder)
`cellAtNo`'s DEFAULT IS NEVER READ. Two statements with their proofs; no definition. NO PROPERTY IS
CLAIMED.

Main names. `k13_bounds_at_head`: **the plan's number of rows is `hRef`, and 2 ^ kCol is 2 ^
`kRef`** (Inst/Model/Layout.lean). `k13_cellAtNo_in_range`: at every value c of the cells' type at
the full size's numbers, at a row below the plan's rows and a column below 2 ^ kCol: `cellAtNo c i
C` (Johnson/Desc/K13/Law/MatOfCells.lean) is c's own entry there: its other branch, 0, is not taken.
Its "there are" binds two proofs of bounds alone.

How. `k13_rows_full` (FromThreadAt.lean of this folder); the head's own field cols13
(Johnson/P5J/MgAtAll.lean): so the second half is a clause of the hypothesis said again; that the
full size's written numbers are `hRef` and 2 ^ `kRef` is by unfolding: Lean evaluates `P5J.colsAt`
(Johnson/P5J/TopJoint.lean) at them. The library has the two numbers as theorems too: `full_rows`,
`full_columns` (Johnson/Flat/ClaimsSizes.lean): not called here.

What it is for. `cellAtNo_matrixOf_entryOf` (CellsCast.lean of this folder) asks no bound: outside
the shape the default is the entry's own value. This file says beside it that `MatTie` never asks
there.

Limits. CONDITIONAL ON h. The first statement: numbers of a public shape: nothing of an index, a
Script, a prover or a coin is named. In the second c is a free variable: tied to no witness, index
or input. Nothing outside this file calls these statements.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness, hiding
or binding.
-/
import Johnson.Desc.ProofFile.Honest.K13.MatTieAtHead
import Johnson.Desc.ProofFile.Honest.K13.FromThreadAt
import Johnson.P5J.Cols13Paid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K13.Law (cellAtNo)
open P5J (AtMgA CellsM TS)
open Inst.Model.Layout (kRef hRef)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)

include h in
/-- **UNDER h THE PLAN's MATRIX HAS THE REFERENCE SHAPE.** -/
theorem k13_bounds_at_head :
    h.𝔇.P13.lin.matrixRows = hRef ∧ 2 ^ h.𝔇.P13.lin.kCol = 2 ^ kRef :=
  ⟨(k13_rows_full h).symm, h.cols13⟩

include h in
/-- **IN `MatTie`'s OWN RANGE `cellAtNo`'s DEFAULT IS NEVER READ**: under h. -/
theorem k13_cellAtNo_in_range (c : CellsM OnBytes.Flat.numsFull) {i C : ℕ}
    (hi : i < h.𝔇.P13.lin.matrixRows) (hC : C < 2 ^ h.𝔇.P13.lin.kCol) :
    ∃ (h1 : i < hRef) (h2 : C < 2 ^ kRef), cellAtNo c i C = c ⟨i, h1⟩ ⟨C, h2⟩ := by
  obtain ⟨e1, e2⟩ := k13_bounds_at_head h
  have h1 : i < hRef := e1 ▸ hi
  have h2 : C < 2 ^ kRef := e2 ▸ hC
  exact ⟨h1, h2, dif_pos ⟨h1, h2⟩⟩

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_bounds_at_head
#print axioms ProofFile.Honest.K13.k13_cellAtNo_in_range
