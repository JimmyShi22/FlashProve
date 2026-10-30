-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FastColLaw.lean: the definitions of FastCol.lean equal the ones on
lists that they repeat, as functions, for all arguments and without hypothesis.

  `symA_eq`      `symA C x (rowArr C m rho) = symE C x m rho` (Fmt/M1Codes.lean)
  `colFast_eq`   `colAt s first last (colPrep s p)`, as a function of the position, is
                 `colOf s first last p` (Fmt/M1Own.lean)
  `treeFast_eq`  `treeFast s T p = treeBy s T p` (RunRows.lean)

The rows and tails may have any lengths, also different ones; there may be none; a chosen row's
number may be out of range; the words need not be below the prime.

By what. Folding an array made from a list is folding the list (`hornerA_eq`); the rest is
unfolding.

Limits. Nothing on cost.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FastCol

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open Fmt.M1 (E Code Stage hornerE symE cp)
open Fmt.M1.Own (PSt syms colOf words)

theorem hornerA_eq (z : UInt64) (l : List E) : hornerA z l.toArray = hornerE z l := by
  unfold hornerA hornerE
  simp

theorem symA_eq (C : Code) (x : Nat) (m rho : List E) :
    symA C x (rowArr C m rho) = symE C x m rho :=
  hornerA_eq _ _

theorem symsA_eq (C : Code) (x : Nat) (rows tails : List (List E)) :
    symsA C x (rowsArr C rows tails) = syms C x rows tails := by
  unfold symsA rowsArr syms
  rw [List.map_map]
  exact congrArg (fun F => (List.range rows.length).map F) (funext fun b => symA_eq C x _ _)

theorem colFast_eq (s : Stage) (first last : Bool) (p : PSt) :
    (fun x => colAt s first last (colPrep s p) x) = colOf s first last p := by
  funext x
  simp only [colAt, colPrep, colOf, symsA_eq]

theorem rowSym_mk (s : Stage) (x : Nat) (mn : Bool) (c : Prop) [Decidable c] (A : Array E)
    (b : Bool) :
    rowSym s x ⟨mn, if c then some A else none, b⟩ =
      if c then (if mn then symA s.C x A else symA s.Z (cp s.Z x) A) else Fld.zeroE := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

theorem rowSym_eq (s : Stage) (p : PSt) (x : Nat) (r : Sel) :
    rowSym s x (rowPrep s p r) = symBy s p x r := by
  unfold rowPrep symBy
  cases r.kind <;> simp only [rowSym_mk, symA_eq, if_true, Bool.false_eq_true, if_false]

theorem rowPrep_base (s : Stage) (p : PSt) (r : Sel) : (rowPrep s p r).base = r.base := by
  unfold rowPrep
  cases r.kind <;> rfl

theorem treeFast_eq (s : Stage) (T : Nat × List Sel) (p : PSt) :
    treeFast s T p = treeBy s T p := by
  unfold treeFast treeBy
  refine congrArg (Prod.mk T.1) (funext fun x => ?_)
  unfold treeAt treePrep wordsAt
  rw [List.flatMap_map]
  exact congrArg (fun F => T.2.flatMap F) (funext fun r => by rw [rowPrep_base, rowSym_eq])

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.hornerA_eq
#print axioms ProofFile.Honest.K12.Light.symA_eq
#print axioms ProofFile.Honest.K12.Light.symsA_eq
#print axioms ProofFile.Honest.K12.Light.colFast_eq
#print axioms ProofFile.Honest.K12.Light.rowSym_mk
#print axioms ProofFile.Honest.K12.Light.rowSym_eq
#print axioms ProofFile.Honest.K12.Light.rowPrep_base
#print axioms ProofFile.Honest.K12.Light.treeFast_eq
