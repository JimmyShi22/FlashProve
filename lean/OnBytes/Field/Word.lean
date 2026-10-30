-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Field/Word.lean: the base field on machine words.

The base field is the integers modulo p = 2^64 - 2^32 + 1. An element is kept as its least residue,
in one word. Fmt/FieldE.lean computes in this field (its second field, `Fmt.Fld.two`) through
natural numbers. The functions here give the same results with operations on 64-bit words, so that
the compiled program needs no arbitrary-precision arithmetic on elements. Only the exponent of
`powF` and the bound on the steps of its loop are natural numbers. The C++ counterparts are the
struct GL64 of blocks/field/gl64.h, whose field operations expect words below p, and pow and inv of
blocks/field/field.h.

Every function is total. In the field operations (`normF`, `addF`, `subF`, `negF`, `mulF`, `powF`,
`invF`) a word that is not below p counts as its residue modulo p, and the result is below p. This
is also how Fmt/FieldE.lean treats such words. The helpers `mulHi`, `subMend` and `addMend` return
plain words, which need not be below p, and `powLoopF` at the exponent 0 returns its last argument
as it is.

How a product is reduced. Write e = 2^32 - 1. Then 2^64 = e and 2^96 = -1 modulo p. So a number of
128 bits with the 32-bit digits w0, w1, w2, w3 is congruent to (w0 + 2^32 w1) - w3 + e w2. A borrow
out of a word is corrected by subtracting e, a carry by adding e. These are the steps of the
function reduce128 of the plonky2 library (Polygon Zero, field/src/goldilocks_field.rs,
https://github.com/0xPolygonZero/plonky2, under the MIT or the Apache-2.0 licence), with a last step
that makes the result the least residue.

Main definitions: `okF`, `normF`, `addF`, `subF`, `negF`, `mulF`, `powF`, `invF`.

The names end in F so that none of them is the name of an operation of `UInt64`. On a word, `a + b`
and `a * b` are the operations modulo 2^64, not those of the field.

This file holds no theorem. That the functions equal those of Fmt/FieldE.lean is proved in three
files: `okF`, `addF`, `subF` and `negF` in OnBytes/Field/WordEq.lean, `mulF` in
OnBytes/Field/MulEq.lean, `powF` and `invF` in OnBytes/Field/PowEq.lean. For `normF`, WordEq.lean
proves that the result, as a number, is the word modulo p (`toNat_normF`). Known answers:
OnBytes/Field/TestField.lean.
-/
import OnBytes.Base

namespace OnBytes

/-- The prime p = 2^64 - 2^32 + 1 as a word. -/
@[inline] def pW : UInt64 := 0xFFFFFFFF00000001

/-- The word e = 2^32 - 1. It is 2^64 modulo p, and it is the mask of a word's low half. -/
@[inline] def epsW : UInt64 := 0xFFFFFFFF

/-- True if the word is below p, that is, if it is an element's least residue. -/
@[inline] def okF (a : UInt64) : Bool := decide (a < pW)

/-- The element that a word stands for: its residue modulo p. -/
@[inline] def normF (a : UInt64) : F := if a < pW then a else a - pW

/-- The sum in the base field. -/
@[inline] def addF (a b : F) : F :=
  let x := normF a
  let y := normF b
  let z := pW - y
  if x < z then x + y else x - z

/-- The difference in the base field. -/
@[inline] def subF (a b : F) : F :=
  let x := normF a
  let y := normF b
  if x < y then x + (pW - y) else x - y

/-- The negative in the base field. -/
@[inline] def negF (a : F) : F :=
  let x := normF a
  if x = 0 then 0 else pW - x

/-- The high word of the product of two words, from four products of 32-bit halves. -/
@[inline] def mulHi (a b : UInt64) : UInt64 :=
  let a0 := a &&& epsW
  let a1 := a >>> 32
  let b0 := b &&& epsW
  let b1 := b >>> 32
  let m1 := a0 * b1 + ((a0 * b0) >>> 32)
  let m2 := a1 * b0 + (m1 &&& epsW)
  a1 * b1 + (m1 >>> 32) + (m2 >>> 32)

/-- A word that is congruent to a - b modulo p, for b below 2^32. After a borrow the word is 2^64
too large, and e = 2^32 - 1 (`epsW`), which is 2^64 modulo p, is subtracted. The bound on b keeps
this second subtraction from wrapping: after a borrow the word is at least 2^64 - e. -/
@[inline] def subMend (a b : UInt64) : UInt64 := if a < b then a - b - epsW else a - b

/-- A word that is congruent to a + b modulo p, for b at most e^2, with e = 2^32 - 1 (`epsW`). After
a carry the word is 2^64 too small, and e, which is 2^64 modulo p, is added. The bound on b keeps
this second addition from wrapping: after a carry the word is below b, so below e^2, and e^2 + e
is below 2^64. -/
@[inline] def addMend (a b : UInt64) : UInt64 := if a + b < b then a + b + epsW else a + b

/-- The number hi 2^64 + lo modulo p, for any two words. -/
@[inline] def reduceWide (hi lo : UInt64) : F :=
  normF (addMend (subMend lo (hi >>> 32)) (((hi &&& epsW) <<< 32) - (hi &&& epsW)))

/-- The product in the base field. -/
@[inline] def mulF (a b : F) : F := reduceWide (mulHi a b) (a * b)

/-- The loop of `powF`: r x^e by squaring. The first argument bounds the number of steps; any
number that is at least e is enough. -/
def powLoopF : Nat → F → Nat → F → F
  | 0, _, _, r => r
  | k + 1, x, e, r =>
    if e = 0 then r else powLoopF k (mulF x x) (e / 2) (if e % 2 = 1 then mulF r x else r)

/-- The power a^e in the base field. a^0 is 1, also at a = 0. -/
def powF (a : F) (e : Nat) : F := powLoopF e a e 1

/-- The inverse in the base field, as the power a^(p - 2). At 0 it is 0, with no sign of an error:
a caller for whom 0 can occur has to test for it first. -/
def invF (a : F) : F := powF a 18446744069414584319

end OnBytes
