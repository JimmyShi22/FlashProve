-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/SmallReader.lean: THE FIRST HOLE OF THE READERS OF A LINK
(Johnson/Desc/First/Batch/ReadersOfLink.lean:
`LinkHoles.small`),
FILLED: the reader of the smallness test's single equations. A definition with code, and two lemmas.
No Mathlib.
  `smallReader s`: the family of single equations as forms over the arrays' OWN rows
    (Johnson/Desc/First/TailClaims/SingleForms.lean: `rowsAff`), off what the record holds of the
    smallness test (`S.tl?`) and of the caller's list of tables (`S.funs?`); no late slot: these
    forms
    name no slot. Nothing where the record holds one of the two not.
  `withSmall H`: the letters H with the first hole so filled.
  `forms_small`: at the name "K8.equations" the readers of a link give just that.
  `formsIn_small`: THE PUBLIC TEST THERE, WITHOUT THE LIST: it is `allForms`
    (Johnson/Desc/First/TailClaims/SingleFormsAll.lean) of "the form names only what is there": the
    list is long (at a small proof some ten million forms): a run must not build it.
Limits: (1) NOT the sums over powers of the draw that the program adds at the batching: that these
add
up to the single equations is the batching's law's premise on that run. (2) THAT IT GIVES ONE LIST
AT
EVERY BORDER AT WHICH THE ITEM IS OPEN is not shown: it reads the smallness test's whole record,
which
later blocks of the segment turn in other fields. (3) It has not run. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.ReadersOfLink
import Johnson.Desc.First.TailClaims.SingleFormsAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims (rowsAff allForms rowsAff_all)

/-- **The reader of the smallness test's single equations.** -/
def smallReader (s : S) : Option Read :=
  match s.tl?, s.funs? with
  | some tl, some funs => some { forms := rowsAff tl funs, late := [] }
  | _, _ => none

/-- The letters with the first hole filled. -/
def withSmall (H : LinkHoles) : LinkHoles := { H with small := smallReader }

theorem forms_small (H : LinkHoles) (l : Link S Claim) (b : Nat) (s : S) :
    (readersOfLink (withSmall H) l).forms b "K8.equations" s = smallReader s := by
  unfold readersOfLink withSmall
  simp

/-- **The public test at the single equations, without the list.** -/
theorem formsIn_small (H : LinkHoles) (l : Link S Claim) (own : List (Nat × Nat)) (b : Nat) (s : S)
    (a : Part) (tl : HTailF2) (funs : Array HFun) (ha : segAt? s = some a) (ht : s.tl? = some tl)
    (hf : s.funs? = some funs) :
    formsIn (readersOfLink (withSmall H) l) own b "K8.equations" s =
      allForms (affIn own (mergeOf s) [] a) tl funs := by
  unfold formsIn
  rw [forms_small, ha]
  unfold smallReader
  rw [ht, hf]
  show (lateOk [] a && (rowsAff tl funs).all fun f => affIn own (mergeOf s) [] a f) = _
  rw [rowsAff_all]
  rfl

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.forms_small
#print axioms VerifiableInference.Desc.K9.formsIn_small
