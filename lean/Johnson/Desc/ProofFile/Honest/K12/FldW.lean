-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FldW.lean: the five operations of Fmt/FieldE.lean on elements
(triples of 64-bit words) at `Fld.two`, computed on words alone. Definitions only. Imports
OnBytes/Field/Word.lean alone, and no Mathlib.

Why. `Fld.add`, `Fld.sub`, `Fld.neg` and `Fld.mul` (Fmt/FieldE.lean) convert their words to natural
numbers, compute there, reduce modulo the prime and convert back; a product has 128 bits and does
not fit a machine word. `addF`, `subF`, `negF` and `mulF` (OnBytes/Field/Word.lean) return the same
words with operations on 64-bit words only.

Each definition repeats one of Fmt/FieldE.lean, with these four functions in the place of the four
of `Fld.two`: `addEW` repeats `Fld.addE`, `subEW` repeats `Fld.subE`, `negEW` repeats `Fld.negE`,
`scaleEW` repeats `Fld.scaleE`, `mulEW` repeats `Fld.mulE`. FldWLaw.lean proves each equal to its
original at `Fld.two`, as functions, for all words, also for words that are not below the prime
(`addEW_eq`, `subEW_eq`, `negEW_eq`, `scaleEW_eq`, `mulEW_eq`).

Limits. A second text, for speed. HalveW.lean calls four of the five, and `Seams.fast` (FastW.lean)
calls HalveW.lean's `halvedW`. Theorems on a run are stated at the originals and are carried over by
the equations. At `Fld.two` only. The constant `Fld.two.cW` in `mulEW` is still that of
Fmt/FieldE.lean. Nothing is measured here. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import OnBytes.Field.Word

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld Ext3)
open OnBytes (addF subF negF mulF)

/-- The sum of two elements. -/
def addEW (a b : Ext3) : Ext3 := (addF a.1 b.1, addF a.2.1 b.2.1, addF a.2.2 b.2.2)

/-- The difference of two elements. -/
def subEW (a b : Ext3) : Ext3 := (subF a.1 b.1, subF a.2.1 b.2.1, subF a.2.2 b.2.2)

/-- The negative of an element. -/
def negEW (a : Ext3) : Ext3 := (negF a.1, negF a.2.1, negF a.2.2)

/-- An element times an element s of the base field. -/
def scaleEW (s : UInt64) (a : Ext3) : Ext3 := (mulF s a.1, mulF s a.2.1, mulF s a.2.2)

/-- The product of two elements. -/
def mulEW (a b : Ext3) : Ext3 :=
  (addF (mulF a.1 b.1) (mulF Fld.two.cW (addF (mulF a.2.1 b.2.2) (mulF a.2.2 b.2.1))),
   addF (addF (mulF a.1 b.2.1) (mulF a.2.1 b.1)) (mulF Fld.two.cW (mulF a.2.2 b.2.2)),
   addF (addF (mulF a.1 b.2.2) (mulF a.2.1 b.2.1)) (mulF a.2.2 b.1))

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.addEW
#print axioms ProofFile.Honest.K12.Light.subEW
#print axioms ProofFile.Honest.K12.Light.negEW
#print axioms ProofFile.Honest.K12.Light.scaleEW
#print axioms ProofFile.Honest.K12.Light.mulEW
