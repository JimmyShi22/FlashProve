-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/SingleFormsAll.lean: A TEST ON ALL OF THE SMALLNESS TEST's SINGLE FORMS, WITHOUT THE
LIST: allForms p tl funs makes the forms of SingleForms.lean one by one and asks p of each; and it is
(rowsAff tl funs).all p. A definition with code and one theorem; no Mathlib.

Why. The list rowsAff is long: a run that bound it whole to a name at the small size ran out of its room. A
public test over the forms should not build it.
Main names:
  allForms p tl funs: the loops of rowsAff's own text, with all in place of flatMap and map.
  **rowsAff_all**: (rowsAff tl funs).all p = allForms p tl funs.
Limits: what p is, is the caller's.

-/
import Johnson.Desc.First.TailClaims.SingleForms

set_option autoImplicit false

namespace VerifiableInference.Desc.First.TailClaims
open OnBytes OnBytes.Model

/-- p of every single form, the forms made one by one. -/
def allForms (p : Aff → Bool) (tl : HTailF2) (funs : Array HFun) : Bool :=
  ((List.range tl.NM).all fun mu =>
    (List.range (((tl.shp.getD mu {}).m + 2) / 3)).all fun i =>
      (List.range tl.tau).all fun u => p (tieAff tl mu i u)) &&
  (readsP tl funs).all fun x => (List.range tl.tau).all fun u => p (readAff tl x u)

/-- **It is the test on the list.** -/
theorem rowsAff_all (p : Aff → Bool) (tl : HTailF2) (funs : Array HFun) :
    (rowsAff tl funs).all p = allForms p tl funs := by
  unfold rowsAff allForms
  simp only [List.all_append, List.all_flatMap, List.all_map, Function.comp_def]

end VerifiableInference.Desc.First.TailClaims

#print axioms VerifiableInference.Desc.First.TailClaims.rowsAff_all
