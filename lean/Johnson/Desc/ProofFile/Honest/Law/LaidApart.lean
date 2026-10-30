-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/LaidApart.lean: NO TWO ELEMENTS OF A MESSAGE's ARRAYS LIE AT ONE
PLACE: of a list of arrays that the plan's own test passes (Own.laidFits,
Johnson/Desc/Own/Req.lean). Over Law/LaidLists.lean. Theorems on public data alone; no definition.

Main names (namespace ProofFile.Honest).
  back_of_some   where the rule lays an element, the list's way back hands that array and that
      element.
  elements_apart   laidAt a i c and laidAt a' i' c' at one place: then a = a', i = i', c = c'.
  fits_of_msgFits   msgFits (Johnson/Desc/ProofFile/Honest/LaidData.lean) at a message that holds an
      array gives Own.laidFits at the arrays of that message.
  elements_apart_msg   elements_apart under msgFits.

By calls: listBack_iff (Law/LaidLists.lean).

Limits. That every element HAS a place is not proved here (the library: laidAt_of_matrixOk,
Johnson/Goal/Meaning/LaidCovered.lean, whose head says that it does not claim "that two elements
have two seats": what elements_apart shows). Nothing of what stands in the arrays. Tests: one #guard
line at the foot. Nothing on any property.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Law.LaidLists

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes.Params (ReqArray ReqLayout ReqShape)
open VerifiableInference.Desc (laidAt)
open VerifiableInference.Desc.Own (laidFits reqMessageLaid)

/-- Where the rule lays an element, the list's way back hands that array and that element. -/
theorem back_of_some {as : List ReqArray} {R P : Nat} (hf : laidFits as R P = true) {a : ReqArray}
    (ha : a ∈ as) {i c r j : Nat} (h : laidAt a i c = some (r, j)) :
    (as.findSome? fun a => (arrayBack a r j).map fun p => (a, p.1, p.2)) = some (a, i, c) :=
  (listBack_iff hf a i c r j).2 ⟨ha, h⟩

/-- **NO TWO ELEMENTS AT ONE PLACE.** -/
theorem elements_apart {as : List ReqArray} {R P : Nat} (hf : laidFits as R P = true)
    {a a' : ReqArray} (ha : a ∈ as) (ha' : a' ∈ as) {i c i' c' : Nat} {p : Nat × Nat}
    (h : laidAt a i c = some p) (h' : laidAt a' i' c' = some p) : a = a' ∧ i = i' ∧ c = c' := by
  obtain ⟨r, j⟩ := p
  have e := (back_of_some hf ha h).symm.trans (back_of_some hf ha' h')
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  exact e

/-- The filling's own public test, at a message that holds an array, gives the plan's test on that
message's arrays. -/
theorem fits_of_msgFits {codes : OnBytes.Codes} {s : ReqShape} {lay : ReqLayout} {l m : Nat}
    (h : msgFits codes s lay l m = true) {a : ReqArray}
    (ha : a ∈ (lay.link.getD l []).filter fun a => a.message == m) :
    ∃ R P, laidFits ((lay.link.getD l []).filter fun a => a.message == m) R P = true := by
  unfold msgFits at h
  obtain ⟨M, -, hM⟩ := (Option.any_eq_true _ _).1 h
  have hne : ((lay.link.getD l []).filter fun a => a.message == m).isEmpty = false := by
    cases hq : (lay.link.getD l []).filter fun a => a.message == m with
    | nil => rw [hq] at ha; cases ha
    | cons _ _ => rfl
  rw [hne, Bool.false_or, Bool.and_eq_true] at hM
  have h2 := hM.2
  unfold reqMessageLaid at h2
  rw [hne, Bool.false_or, Bool.and_eq_true] at h2
  have h3 := h2.2
  split at h3
  · rename_i c pad _ _
    rw [Bool.and_eq_true] at h3
    exact ⟨_, _, h3.1⟩
  · cases h3

/-- **NO TWO ELEMENTS OF ONE MESSAGE's ARRAYS AT ONE PLACE**, under the filling's own public
test. -/
theorem elements_apart_msg {codes : OnBytes.Codes} {s : ReqShape} {lay : ReqLayout} {l m : Nat}
    (h : msgFits codes s lay l m = true) {a a' : ReqArray}
    (ha : a ∈ (lay.link.getD l []).filter fun a => a.message == m)
    (ha' : a' ∈ (lay.link.getD l []).filter fun a => a.message == m) {i c i' c' : Nat}
    {p : Nat × Nat} (h1 : laidAt a i c = some p) (h2 : laidAt a' i' c' = some p) :
    a = a' ∧ i = i' ∧ c = c' := by
  obtain ⟨R, P, hf⟩ := fits_of_msgFits h ha
  exact elements_apart hf ha ha' h1 h2

-- the eight elements of the toy's array have eight places
#guard (((List.range 2).flatMap fun i => (List.range 4).filterMap fun c =>
  laidAt LaidListsToy.good i c).eraseDups).length = 8

end ProofFile.Honest

#print axioms ProofFile.Honest.back_of_some
#print axioms ProofFile.Honest.elements_apart
#print axioms ProofFile.Honest.fits_of_msgFits
#print axioms ProofFile.Honest.elements_apart_msg
