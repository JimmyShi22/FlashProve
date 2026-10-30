-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/CellsSmallAll.lean: FROM A BOUND ON A READER's CELLS AT ALL
ARGUMENTS TO THE LIBRARY's TEST cellsSmall AT ALL NUMBERS AND LISTS: the small law between a premise
on the input's reader and what tieOf_plan (Johnson/Desc/ProofFile/Honest/K1/Law/TiePlan.lean) asks.
Three statements and their proofs. No definition. A reader of cells, a list and a place's numbers as
letters: no thread, no run, no witness.

  cellsSmall_of_all   integers at most 128 in absolute value everywhere pass the test at all p
  cellsAtOf_small     where the balanced integers of a reader's cells are so bounded at all
                      arguments, cellsAtOf's are, at every list: beyond the list they are 0
  cellsSmall_cells    the two in one: cellsSmall p (cellsAtOf C mats) = true

Limits. The bound is a premise: proved here of no reader. Nothing on soundness, on completeness or
on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K8.Part
import Johnson.Desc.K8.Honest.Window

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open ProofFile.Honest (Cells)
open ProofFile.Honest.K8 (cellsAtOf signedOf)
open VerifiableInference.Desc.First.K8 (Par)
open VerifiableInference.Desc.First.K8.Honest (CellsAt cellsSmall)

/-- Integers that are at most 128 in absolute value everywhere pass the library's test at all
numbers p. -/
theorem cellsSmall_of_all (p : Par) {a : CellsAt} (h : ∀ mu i c, (a mu i c).natAbs ≤ 128) :
    cellsSmall p a = true := by
  unfold cellsSmall
  exact List.all_eq_true.2 fun mu _ => List.all_eq_true.2 fun i _ =>
    List.all_eq_true.2 fun c _ => decide_eq_true (h mu i c)

/-- Where the balanced integers of a reader's cells are at most 128 in absolute value at all
arguments, so are cellsAtOf's, at every list. -/
theorem cellsAtOf_small (C : Cells) (mats : List (ℕ × String × ℕ))
    (h : ∀ k s r c, (signedOf (C.cell k s r c)).natAbs ≤ 128) (mu i c : ℕ) :
    (cellsAtOf C mats mu i c).natAbs ≤ 128 := by
  unfold cellsAtOf
  cases mats[mu]? with
  | none => exact Nat.zero_le _
  | some m => exact h _ _ _ _

/-- **The two in one.** -/
theorem cellsSmall_cells (p : Par) (C : Cells) (mats : List (ℕ × String × ℕ))
    (h : ∀ k s r c, (signedOf (C.cell k s r c)).natAbs ≤ 128) :
    cellsSmall p (cellsAtOf C mats) = true :=
  cellsSmall_of_all p (cellsAtOf_small C mats h)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.cellsSmall_of_all
#print axioms ProofFile.Honest.K1.cellsAtOf_small
#print axioms ProofFile.Honest.K1.cellsSmall_cells
