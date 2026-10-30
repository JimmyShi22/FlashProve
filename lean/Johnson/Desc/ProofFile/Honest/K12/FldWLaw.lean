-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FldWLaw.lean: the five operations of FldW.lean equal those of
Fmt/FieldE.lean at `Fld.two`, as functions, for all words and without hypothesis. Imports Mathlib
(through OnBytes/Field/MulEq.lean).

  `addEW_eq`     `addEW = Fld.two.addE`
  `subEW_eq`     `subEW = Fld.two.subE`
  `negEW_eq`     `negEW = Fld.two.negE`
  `scaleEW_eq`   `scaleEW = Fld.two.scaleE`
  `mulEW_eq`     `mulEW = Fld.two.mulE`

By what. Both sides are unfolded, and `addF_eq`, `subF_eq`, `negF_eq` (OnBytes/Field/WordEq.lean)
and `mulF_eq` (OnBytes/Field/MulEq.lean) rewrite one into the other.

Limits. Nothing on cost.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FldW
import OnBytes.Field.MulEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open OnBytes (addF_eq subF_eq negF_eq mulF_eq)

theorem addEW_eq : addEW = Fld.two.addE := by
  funext a b
  simp only [addEW, Fld.addE, addF_eq]

theorem subEW_eq : subEW = Fld.two.subE := by
  funext a b
  simp only [subEW, Fld.subE, subF_eq]

theorem negEW_eq : negEW = Fld.two.negE := by
  funext a
  simp only [negEW, Fld.negE, negF_eq]

theorem scaleEW_eq : scaleEW = Fld.two.scaleE := by
  funext s a
  simp only [scaleEW, Fld.scaleE, mulF_eq]

theorem mulEW_eq : mulEW = Fld.two.mulE := by
  funext a b
  simp only [mulEW, Fld.mulE, addF_eq, mulF_eq]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.addEW_eq
#print axioms ProofFile.Honest.K12.Light.subEW_eq
#print axioms ProofFile.Honest.K12.Light.negEW_eq
#print axioms ProofFile.Honest.K12.Light.scaleEW_eq
#print axioms ProofFile.Honest.K12.Light.mulEW_eq
