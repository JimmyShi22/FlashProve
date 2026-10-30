-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FastLaw.lean: the three functions of Fast.lean equal their
originals in Fmt/ (`tabOf`, Fmt/M1Own.lean; `foldRows`, `csOwnG`, Fmt/M1Cs.lean), as functions, for
all arguments and without hypothesis.

  `tabFast_eq`   `tabFast = tabOf`
  `foldRowsA_eq`   `foldRowsA = foldRows`
  `csFast_eq`    `csFast = csOwnG`

The rows may have any lengths, also different ones; there may be no rows; n may be larger or smaller
than a row; the words need not be below the prime; `Fld.one` and `Fld.two` are both covered.

By what. An entry of a list converted to an array is the list's entry (`fast_getD`, `fast_row`).

Limits. Nothing on cost.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Fast
import Johnson.Desc.ProofFile.Honest.K12.HalveLaw
import Johnson.Desc.ProofFile.Honest.K12.RunBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open Fmt.M1 (E foldV foldRows csOwnG)
open Fmt.M1.Own (tabOf)

theorem fast_getD {α : Type} (l : List α) (i : Nat) (d : α) : l.toArray.getD i d = l.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem fast_row (rows : List (List E)) (r : Nat) :
    (rows.map List.toArray).toArray.getD r #[] = (rows.getD r []).toArray := by
  rw [fast_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases rows[r]? <;> rfl

theorem tabFast_eq : tabFast = tabOf := by
  funext rows n
  show Array.ofFn (n := rows.length * n) (fun i =>
      ((rows.map List.toArray).toArray.getD (i.val % rows.length) #[]).getD
        (i.val / rows.length) Fld.zeroE) =
    Array.ofFn (n := rows.length * n) fun i =>
      (rows.getD (i.val % rows.length) []).getD (i.val / rows.length) Fld.zeroE
  exact congrArg _ (funext fun i => by rw [fast_row, fast_getD])

theorem foldRowsA_eq : foldRowsA = foldRows := by
  funext f g rows n
  show (List.range n).map (fun j =>
      foldV f g ((rows.map List.toArray).map fun r => r.getD j Fld.zeroE).toArray) =
    (List.range n).map fun j => foldV f g (rows.map fun r => r.getD j Fld.zeroE).toArray
  refine congrArg (fun F => (List.range n).map F) (funext fun j => ?_)
  rw [List.map_map]
  exact congrArg (fun c : List E → E => foldV f g (rows.map c).toArray)
    (funext fun r => fast_getD r j Fld.zeroE)

theorem csFast_eq : csFast = csOwnG := by
  funext f old new g M Rh W Sg P Pi free pad
  unfold csFast csOwnG
  rw [foldRowsA_eq]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.fast_getD
#print axioms ProofFile.Honest.K12.Light.fast_row
#print axioms ProofFile.Honest.K12.Light.tabFast_eq
#print axioms ProofFile.Honest.K12.Light.foldRowsA_eq
#print axioms ProofFile.Honest.K12.Light.csFast_eq
