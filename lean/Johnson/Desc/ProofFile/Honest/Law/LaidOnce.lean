-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/LaidOnce.lean: EVERY ELEMENT OF A MESSAGE's ARRAYS IS LAID AT A
PLACE AND IS READ BACK FROM IT: of a list of arrays that the plan's own test passes (Own.laidFits,
Johnson/Desc/Own/Req.lean), and under the filling's own public test (msgFits,
Johnson/Desc/ProofFile/Honest/LaidData.lean). Theorems on public data alone; no definition.

ONE LEMMA OF THE LIBRARY's FOLDER Johnson/Goal/ IS CALLED: Meaning.laidAt_of_matrixOk
(Johnson/Goal/Meaning/LaidCovered.lean): under the programs' test on one matrix the array answers at
every element. NOTHING ELSE OF THAT FOLDER IS CALLED HERE; what that file imports beneath it is not
read here.

Main names (namespace ProofFile.Honest).
  place_some   an element inside its array's rows and columns has a place.
  once_and_back   it has a place, and the list's way back hands that array and that element at it.
  once_and_back_msg   the same at laidBack, under msgFits.

By calls: Meaning.laidAt_of_matrixOk; laidMatrixFits_eq (Johnson/Desc/Own/ReqAgree.lean);
fits_matrix, laidBack_iff (Law/LaidLists.lean); back_of_some, fits_of_msgFits (Law/LaidApart.lean).

Limits. With elements_apart (Law/LaidApart.lean): each element at one place, no two at one. That
such a place is none of the pad's: Law/LaidLaw.lean, at a seat: not assembled here. That an array of
values is as large as the layout's array is the caller's test. Tests: one #guard line at the foot.
Nothing on any property.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Law.LaidApart
import Johnson.Goal.Meaning.LaidCovered
import Johnson.Desc.Own.ReqAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes.Params (ReqArray ReqLayout ReqShape)
open VerifiableInference.Desc (laidAt)
open VerifiableInference.Desc.Own (laidFits laidMatrixFits_eq)

/-- An element inside its array's rows and columns has a place. -/
theorem place_some {as : List ReqArray} {R P : Nat} (hf : laidFits as R P = true) {a : ReqArray}
    (ha : a ∈ as) {i c : Nat} (hi : i < a.sizeI) (hc : c < a.sizeC) :
    (laidAt a i c).isSome = true :=
  Meaning.laidAt_of_matrixOk ((laidMatrixFits_eq a R P).symm.trans (fits_matrix hf ha)) hi hc

/-- **LAID, AND READ BACK.** -/
theorem once_and_back {as : List ReqArray} {R P : Nat} (hf : laidFits as R P = true)
    {a : ReqArray} (ha : a ∈ as) {i c : Nat} (hi : i < a.sizeI) (hc : c < a.sizeC) :
    ∃ r j, laidAt a i c = some (r, j) ∧
      (as.findSome? fun a => (arrayBack a r j).map fun p => (a, p.1, p.2)) = some (a, i, c) := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (place_some hf ha hi hc)
  exact ⟨p.1, p.2, hp, back_of_some hf ha hp⟩

/-- **LAID, AND READ BACK BY laidBack**, under the filling's own public test. -/
theorem once_and_back_msg {codes : OnBytes.Codes} {s : ReqShape} {lay : ReqLayout} {l m : Nat}
    (h : msgFits codes s lay l m = true) {a : ReqArray}
    (ha : a ∈ (lay.link.getD l []).filter fun a => a.message == m) {i c : Nat}
    (hi : i < a.sizeI) (hc : c < a.sizeC) :
    ∃ r j, laidAt a i c = some (r, j) ∧ laidBack lay l m r j = some (a, i, c) := by
  obtain ⟨R, P, hf⟩ := fits_of_msgFits h ha
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (place_some hf ha hi hc)
  exact ⟨p.1, p.2, hp, (laidBack_iff lay l m R P hf a i c p.1 p.2).2 ⟨ha, hp⟩⟩

-- at the toy's array every element has a place; one row or one column beyond it has none
#guard ((List.range 2).all fun i => (List.range 4).all fun c =>
    (laidAt LaidListsToy.good i c).isSome) &&
  (laidAt LaidListsToy.good 2 0).isNone && (laidAt LaidListsToy.good 0 4).isNone

end ProofFile.Honest

#print axioms ProofFile.Honest.place_some
#print axioms ProofFile.Honest.once_and_back
#print axioms ProofFile.Honest.once_and_back_msg
