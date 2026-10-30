-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/AddMulL.lean: THE FORM a + k b (`Aff.addMul`, OnBytes/Model/Hide.lean) ONCE
MORE, ITS TWO LISTS LAID BY ONE APPEND EACH: `addMulL`; AND THE TWO ARE EQUAL AT ALL FORMS AND EVERY
FACTOR: `addMul_eq`. No premise. One definition, four theorems. It imports
Johnson/Desc/First/Shape/Parts.lean alone.

Purpose. Aff.addMul lays b's entries onto a's array by one `push` an entry, and b's slots likewise.
Lean's kernel pays for a push by the array's length: a form of some thousand entries that is laid so
costs it minutes and gigabytes as soon as the form's lists are read (seen in a run; not shown here).
addMulL appends b's list to a's once. Whoever has to evaluate a text that makes forms may rewrite by
these laws first. Sum, difference and multiple of forms are Aff.addMul by definition: a law for
each, so that a rewriting finds them.

Main names.
* `addMulL a b k`: entries: a's list, then b's with each coefficient times k; slots likewise; the
  constant as in Aff.addMul.
* **`addMul_eq`**: Aff.addMul a b k = addMulL a b k. By `foldl_push_map` (Parts.lean).
* `add_eq`: a + b = addMulL a b oneE. `sub_eq`: a - b = addMulL a b (subE zeroE oneE). `scale_eq`:
  Aff.scale a k = addMulL {} a k.

Limits. An equality of two functions. Nothing is said on what either costs; nothing is evaluated
here. WHERE ENTRIES ARE LAID ONE BY ONE ONTO A LONG FORM addMulL APPENDS A LIST OF ONE MEMBER AT THE
END EACH TIME: that walks the long list as a push does. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.First.Shape.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.AddMulL
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Shape (foldl_push_map)

/-- The form a + k b, its two lists laid by ONE APPEND each. -/
def addMulL (a b : Aff) (k : E) : Aff where
  ents := (a.ents.toList ++
    b.ents.toList.map fun (x : Ent) => { x with coef := mulE x.coef k }).toArray
  slots := (a.slots.toList ++ b.slots.toList.map fun x => (x.1, mulE x.2 k)).toArray
  const := addE a.const (mulE b.const k)

/-- **THE LAW: Aff.addMul IS addMulL**, at all forms and every factor. -/
theorem addMul_eq (a b : Aff) (k : E) : Aff.addMul a b k = addMulL a b k := by
  have e1 : b.ents.foldl (fun l x => l.push { x with coef := mulE x.coef k }) a.ents =
      (a.ents.toList ++
        b.ents.toList.map fun (x : Ent) => { x with coef := mulE x.coef k }).toArray := by
    apply Array.toList_inj.1
    rw [← Array.foldl_toList, foldl_push_map]
  have e2 : b.slots.foldl (fun l x => l.push (x.1, mulE x.2 k)) a.slots =
      (a.slots.toList ++ b.slots.toList.map fun x => (x.1, mulE x.2 k)).toArray := by
    apply Array.toList_inj.1
    rw [← Array.foldl_toList, foldl_push_map]
  unfold Aff.addMul addMulL
  rw [e1, e2]

/-- The sum of two forms. -/
theorem add_eq (a b : Aff) : a + b = addMulL a b oneE := addMul_eq a b oneE

/-- The difference of two forms. -/
theorem sub_eq (a b : Aff) : a - b = addMulL a b (subE zeroE oneE) :=
  addMul_eq a b (subE zeroE oneE)

/-- The form k a. -/
theorem scale_eq (a : Aff) (k : E) : Aff.scale a k = addMulL {} a k := addMul_eq {} a k

end Johnson.AtFull.Shape.AddMulL

#print axioms Johnson.AtFull.Shape.AddMulL.addMul_eq
#print axioms Johnson.AtFull.Shape.AddMulL.add_eq
#print axioms Johnson.AtFull.Shape.AddMulL.sub_eq
#print axioms Johnson.AtFull.Shape.AddMulL.scale_eq
#print axioms Johnson.AtFull.Shape.AddMulL.addMulL
