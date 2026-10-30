-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ColWLaw.lean: the definitions of ColW.lean equal the ones that
they repeat, as functions, for all arguments and without hypothesis. Imports Mathlib (through
OnBytes/Field/MulEq.lean).

  `hornerW_eq`   `hornerW = hornerA` (FastCol.lean)
  `symW_eq`      `symW C x (rowArr C m rho) = symE C x m rho` (Fmt/M1Codes.lean)
  `colW_eq`      `colAtW s first last (colPrep s p)`, as a function of the position, is
                 `colOf s first last p` (Fmt/M1Own.lean)
  `colTreeW_eq`  `colTreeW s last p = (s.C.a, colOf s false last p)`
  `treeW_eq`     `treeW s T p = treeBy s T p` (RunRows.lean)

The rows and tails may have any lengths, also different ones; there may be none; a chosen row's
number may be out of range; the words need not be below the prime.

By what. One step of `loopW` is one step of `hornerA`, by `addF_eq` (OnBytes/Field/WordEq.lean) and
`mulF_eq` (OnBytes/Field/MulEq.lean), which hold for all words. A loop from the last index down to 0
is `List.foldr` (`loopW_foldr`). The rest follows from the equations of FastColLaw.lean.

Limits. Nothing on cost.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ColW
import Johnson.Desc.ProofFile.Honest.K12.FastColLaw
import OnBytes.Field.MulEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open Fmt.M1 (E Code Stage hornerE symE)
open Fmt.M1.Own (PSt colOf)
open OnBytes (addF mulF addF_eq mulF_eq)

/-- One step on three words is one step of `hornerA`. -/
theorem stepW_eq (z : UInt64) (c : E) (a0 a1 a2 : UInt64) :
    ((addF c.1 (mulF z a0), addF c.2.1 (mulF z a1), addF c.2.2 (mulF z a2)) : E) =
      Fld.two.addE c (Fld.two.scaleE z (a0, a1, a2)) := by
  simp only [Fld.addE, Fld.scaleE, addF_eq, mulF_eq]

theorem loopW_succ (z : UInt64) (A : Array E) (i : Nat) (a0 a1 a2 : UInt64) :
    loopW z A (i + 1) a0 a1 a2 =
      loopW z A i (addF (A.getD i Fld.zeroE).1 (mulF z a0))
        (addF (A.getD i Fld.zeroE).2.1 (mulF z a1))
        (addF (A.getD i Fld.zeroE).2.2 (mulF z a2)) := by
  conv => lhs; unfold loopW

/-- The loop over the first i entries of a list is `List.foldr` over them. -/
theorem loopW_foldr (z : UInt64) (l : List E) :
    ∀ (i : Nat) (a0 a1 a2 : UInt64), i ≤ l.length →
      loopW z l.toArray i a0 a1 a2 =
        (l.take i).foldr (fun c acc => Fld.two.addE c (Fld.two.scaleE z acc)) (a0, a1, a2)
  | 0, _, _, _, _ => rfl
  | i + 1, a0, a1, a2, h => by
    have hi : i < l.length := h
    have ec : l.toArray.getD i Fld.zeroE = l[i] := by
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hi,
        Option.getD_some]
    rw [loopW_succ, loopW_foldr z l i _ _ _ (Nat.le_of_lt hi), ec, stepW_eq, List.take_add_one,
      List.getElem?_eq_getElem hi, Option.toList_some, List.foldr_append, List.foldr_cons,
      List.foldr_nil]

theorem hornerW_eq : hornerW = hornerA := by
  funext z A
  obtain ⟨l⟩ := A
  show loopW z l.toArray l.length 0 0 0 = hornerA z l.toArray
  rw [loopW_foldr z l l.length 0 0 0 (Nat.le_refl _), List.take_length, hornerA_eq]
  rfl

theorem symW_symA : symW = symA := by
  funext C x A
  unfold symW symA
  rw [hornerW_eq]

theorem symW_eq (C : Code) (x : Nat) (m rho : List E) :
    symW C x (rowArr C m rho) = symE C x m rho := by
  rw [symW_symA]
  exact symA_eq C x m rho

theorem symsW_symsA : symsW = symsA := by
  funext C x As
  unfold symsW symsA
  rw [symW_symA]

theorem colAtW_colAt : colAtW = colAt := by
  funext s first last D x
  unfold colAtW colAt
  rw [symsW_symsA]

theorem colW_eq (s : Stage) (first last : Bool) (p : PSt) :
    (fun x => colAtW s first last (colPrep s p) x) = colOf s first last p := by
  rw [colAtW_colAt]
  exact colFast_eq s first last p

theorem colTreeW_eq (s : Stage) (last : Bool) (p : PSt) :
    colTreeW s last p = (s.C.a, colOf s false last p) :=
  congrArg (Prod.mk s.C.a) (colW_eq s false last p)

theorem treeAtW_treeAt : treeAtW = treeAt := by
  funext D x
  have e : rowSymW = rowSym := by
    funext s y d
    unfold rowSymW rowSym
    rw [symW_symA]
    rfl
  unfold treeAtW treeAt
  rw [e]

theorem treeW_eq (s : Stage) (T : Nat × List Sel) (p : PSt) : treeW s T p = treeBy s T p := by
  unfold treeW
  rw [treeAtW_treeAt]
  exact treeFast_eq s T p

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.stepW_eq
#print axioms ProofFile.Honest.K12.Light.loopW_succ
#print axioms ProofFile.Honest.K12.Light.loopW_foldr
#print axioms ProofFile.Honest.K12.Light.hornerW_eq
#print axioms ProofFile.Honest.K12.Light.symW_symA
#print axioms ProofFile.Honest.K12.Light.symW_eq
#print axioms ProofFile.Honest.K12.Light.symsW_symsA
#print axioms ProofFile.Honest.K12.Light.colAtW_colAt
#print axioms ProofFile.Honest.K12.Light.colW_eq
#print axioms ProofFile.Honest.K12.Light.colTreeW_eq
#print axioms ProofFile.Honest.K12.Light.treeAtW_treeAt
#print axioms ProofFile.Honest.K12.Light.treeW_eq
