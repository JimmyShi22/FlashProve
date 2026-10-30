-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Field/Ext.lean: the cubic extension field on machine words.

The extension field is E = F[X] / (X^3 - 2), with F the base field of OnBytes/Field/Word.lean. An
element e_0 + e_1 X + e_2 X^2 has the three coordinates e_0, e_1, e_2. E is a field because 2 is not
a cube in F, so that X^3 - 2 is irreducible; blocks/field/gl64.h gives the argument. Neither this
file nor OnBytes/Field/ExtEq.lean proves it. Fmt/FieldE.lean has two base fields, each with a cubic
extension; F and E are its second pair (`Fmt.Fld.two`). The functions here that Fmt/FieldE.lean also
has give the same results as there, through the word operations of OnBytes/Field/Word.lean. The C++
counterpart is blocks/field/field.h, built with BLK_FIELD = 2.

Every function is total. A word that is not below p counts as its residue modulo p, except in two
tests: `okE` asks whether the words are below p, and `isZeroE` compares the words themselves with 0,
so that a coordinate p, which represents 0, makes it answer false.

Main definitions: `zeroE`, `oneE`, `ofF`, `thetaE`, `addE`, `subE`, `negE`, `scaleE`, `mulE`,
`invE`, `powE`, `maddE`, `maddS`, `foldPairE`, `isZeroE`, `okE`.

This file holds no theorem. Fmt/ spells an element as a triple of words. OnBytes/Field/ExtEq.lean
proves the equalities with Fmt/FieldE.lean on such triples; its head lists them. For `powE`, which
Fmt/FieldE.lean does not have, it only unfolds the loop, and it has nothing on `thetaE` or
`isZeroE`. What `powE` and `isZeroE` mean in the field: `readE_pow` and `isZeroE_iff` in
OnBytes/Slice/ProgField.lean. Known answers: OnBytes/Field/TestField.lean.
-/
import OnBytes.Field.Word

namespace OnBytes

/-- The element 0 of E. -/
@[inline] def zeroE : E := E.mk3 0 0 0

/-- The element 1 of E. -/
@[inline] def oneE : E := E.mk3 1 0 0

/-- An element of the base field as an element of E. -/
@[inline] def ofF (a : F) : E := E.mk3 a 0 0

/-- The basis of E over F: 1 at t = 0, X at t = 1, X^2 at t = 2, and 0 at any other t. -/
def thetaE (t : Nat) : E :=
  E.mk3 (if t = 0 then 1 else 0) (if t = 1 then 1 else 0) (if t = 2 then 1 else 0)

/-- True if all three words are below p. -/
@[inline] def okE (a : E) : Bool := okF a.c0 && okF a.c1 && okF a.c2

/-- True if all three words are 0. On words below p this says that the element is 0. -/
@[inline] def isZeroE (a : E) : Bool := a.c0 == 0 && a.c1 == 0 && a.c2 == 0

/-- The sum in E. -/
@[inline] def addE (a b : E) : E :=
  E.mk3 (addF a.c0 b.c0) (addF a.c1 b.c1) (addF a.c2 b.c2)

/-- The difference in E. -/
@[inline] def subE (a b : E) : E :=
  E.mk3 (subF a.c0 b.c0) (subF a.c1 b.c1) (subF a.c2 b.c2)

/-- The negative in E. -/
@[inline] def negE (a : E) : E := E.mk3 (negF a.c0) (negF a.c1) (negF a.c2)

/-- The product of an element s of the base field and an element of E. -/
@[inline] def scaleE (s : F) (a : E) : E :=
  E.mk3 (mulF s a.c0) (mulF s a.c1) (mulF s a.c2)

/-- Twice an element of the base field: the factor 2 that X^3 = 2 brings into a product in E. -/
@[inline] def twiceF (a : F) : F := addF a a

/-- The coordinate at 1 of the product of a0 + a1 X + a2 X^2 and b0 + b1 X + b2 X^2. -/
@[inline] def mulW0 (a0 a1 a2 b0 b1 b2 : F) : F :=
  addF (mulF a0 b0) (twiceF (addF (mulF a1 b2) (mulF a2 b1)))

/-- The coordinate at X of the product of a0 + a1 X + a2 X^2 and b0 + b1 X + b2 X^2. -/
@[inline] def mulW1 (a0 a1 a2 b0 b1 b2 : F) : F :=
  addF (addF (mulF a0 b1) (mulF a1 b0)) (twiceF (mulF a2 b2))

/-- The coordinate at X^2 of the product of a0 + a1 X + a2 X^2 and b0 + b1 X + b2 X^2. -/
@[inline] def mulW2 (a0 a1 a2 b0 b1 b2 : F) : F :=
  addF (addF (mulF a0 b2) (mulF a1 b1)) (mulF a2 b0)

/-- The coordinate at 1 of a product in E. -/
@[inline] def mulE0 (a b : E) : F := mulW0 a.c0 a.c1 a.c2 b.c0 b.c1 b.c2

/-- The coordinate at X of a product in E. -/
@[inline] def mulE1 (a b : E) : F := mulW1 a.c0 a.c1 a.c2 b.c0 b.c1 b.c2

/-- The coordinate at X^2 of a product in E. -/
@[inline] def mulE2 (a b : E) : F := mulW2 a.c0 a.c1 a.c2 b.c0 b.c1 b.c2

/-- The product in E. -/
def mulE (a b : E) : E := E.mk3 (mulE0 a b) (mulE1 a b) (mulE2 a b)

/-- The three cofactors of an element a: the element whose product with a is the norm of a. -/
def adjE (a : E) : E :=
  E.mk3 (subF (mulF a.c0 a.c0) (twiceF (mulF a.c1 a.c2)))
    (subF (twiceF (mulF a.c2 a.c2)) (mulF a.c0 a.c1))
    (subF (mulF a.c1 a.c1) (mulF a.c0 a.c2))

/-- The norm of an element of E, an element of the base field. -/
def normE (a : E) : F :=
  let c := adjE a
  addF (mulF a.c0 c.c0) (twiceF (addF (mulF a.c2 c.c1) (mulF a.c1 c.c2)))

/-- The inverse in E: the cofactors divided by the norm. In a field the norm is 0 only at the
element 0. At 0 the result is 0, with no sign of an error: a caller for whom 0 can occur has to
test for it first. -/
def invE (a : E) : E := scaleE (invF (normE a)) (adjE a)

/-- a + s x, with all three in E. Each coordinate of the product is added at once: no value of E is
built for the product. -/
def maddE (a s x : E) : E :=
  E.mk3 (addF a.c0 (mulE0 s x)) (addF a.c1 (mulE1 s x)) (addF a.c2 (mulE2 s x))

/-- a + s x, with s in the base field and a, x in E. -/
def maddS (a : E) (s : F) (x : E) : E :=
  E.mk3 (addF a.c0 (mulF s x.c0)) (addF a.c1 (mulF s x.c1)) (addF a.c2 (mulF s x.c2))

/-- a + g (b - a), with all three in E. No value of E is built for the difference or for the
product. C++: fold_pair in blocks/field/mle.h. -/
def foldPairE (a b g : E) : E :=
  let d0 := subF b.c0 a.c0
  let d1 := subF b.c1 a.c1
  let d2 := subF b.c2 a.c2
  E.mk3 (addF a.c0 (mulW0 g.c0 g.c1 g.c2 d0 d1 d2)) (addF a.c1 (mulW1 g.c0 g.c1 g.c2 d0 d1 d2))
    (addF a.c2 (mulW2 g.c0 g.c1 g.c2 d0 d1 d2))

/-- The loop of `powE`: r x^e by squaring. The first argument bounds the number of steps; any
number that is at least e is enough. -/
def powLoopE : Nat → E → Nat → E → E
  | 0, _, _, r => r
  | k + 1, x, e, r =>
    if e = 0 then r else powLoopE k (mulE x x) (e / 2) (if e % 2 = 1 then mulE r x else r)

/-- The power a^e in E. a^0 is 1, also at a = 0. -/
def powE (a : E) (e : Nat) : E := powLoopE e a e oneE

end OnBytes
