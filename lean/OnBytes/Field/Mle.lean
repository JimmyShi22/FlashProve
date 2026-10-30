-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Field/Mle.lean: multilinear polynomials and product forms, for OnBytes/Iop/.

A vector v of at most 2^k entries is read as the multilinear polynomial in k variables that takes
the value v[j] at the corner whose coordinate t is bit t of j (the lowest bit first); entries that
are missing count as 0. Its value at a point z is the sum of eq(j, z) v[j] over j, where eq(j, z)
is the product over t of z[t] if bit t of j is 1, and of 1 - z[t] if it is 0.

A product form with the factors f[0] to f[k - 1] is the vector of 2^k entries whose entry j is
the product of the f[t] over the bits t of j that are 1. The generator rows of
OnBytes/Iop/Ground.lean are of this kind: with the factors x, x^2, x^4 and so on (`squaresOf`) entry
j is x^j.

These are the routines of the C++ header blocks/field/mle.h, on lists. Two differences to know: that
header has no routine for `squaresOf`; and where mle_eval, product_table and product_dot there stop
the program on a length above 2^k, the functions here test nothing: their docstrings say what they
do.

Main definitions: `eqWeight`, `eqIndex`, `eqEval`, `eqTable`, `polyEval`, `foldPairF`,
`mleEvalF`, `mleEvalE`, `squaresOf`, `productIndex`, `productTable`, `productMle`, `productDotF`,
`productDotE`.

No recursion here is deeper than the number of variables: the loops over a vector are tail calls
that collect their results in an array. This file holds no theorem; OnBytes/Slice/ProgMle.lean and
ProgCodes.lean have some. Known answers: OnBytes/Field/TestMle.lean.
-/
import OnBytes.Field.Ext

namespace OnBytes

/-- `eqWeight z j r` is r times eq(j, z): the product, over the coordinates x of the point z, of x
if the matching bit of j is 1 and of 1 - x if it is 0. The first coordinate goes with the lowest
bit. Bits of j beyond the length of z are ignored. -/
def eqWeight : List E → Nat → E → E
  | [], _, r => r
  | x :: xs, j, r => eqWeight xs (j / 2) (mulE r (if j % 2 == 1 then x else subE oneE x))

/-- eq(j, z), the weight of the corner j at the point z: `eqWeight` with r = 1. C++: eq_index. -/
def eqIndex (z : List E) (j : Nat) : E := eqWeight z j oneE

/-- r times the equality polynomial of two points, as far as the shorter point goes. -/
def eqEvalFrom : List E → List E → E → E
  | a :: as, b :: bs, r =>
    let ab := mulE a b
    eqEvalFrom as bs (mulE r (subE (subE (addE (addE ab ab) oneE) a) b))
  | _, _, r => r

/-- The equality polynomial of two points: the product of 2 a b + 1 - a - b over the coordinates, as
far as the shorter point goes. -/
def eqEval (a b : List E) : E := eqEvalFrom a b oneE

/-- The weights of all corners: entry j is `eqIndex z j`, for j below 2^k with k the length of z. -/
def eqTable (z : List E) : Array E :=
  z.foldl (fun (out : Array E) x =>
    let hi := out.map fun w => mulE w x
    (Array.zipWith subE out hi) ++ hi) #[oneE]

/-- The value at x of the polynomial with the coefficients c, the constant one first. -/
def polyEval (c : List E) (x : E) : E := c.reverse.foldl (fun r a => maddE a r x) zeroE

/-- a + g (b - a), for a and b in the base field. -/
@[inline] def foldPairF (a b : F) (g : E) : E := addE (scaleE (subF b a) g) (ofF a)

/-- The loop of `foldStepF`. acc holds the results so far. -/
def foldLoopF (g : E) : List F → Array E → Array E
  | a :: b :: t, acc => foldLoopF g t (acc.push (foldPairF a b g))
  | [a], acc => acc.push (scaleE a (subE oneE g))
  | [], acc => acc

/-- Fixes the lowest variable of a vector over the base field at g. A last entry without a partner
has the partner 0. -/
def foldStepF (g : E) (v : List F) : List E := (foldLoopF g v #[]).toList

/-- The loop of `foldStepE`. acc holds the results so far. -/
def foldLoopE (g : E) : List E → Array E → Array E
  | a :: b :: t, acc => foldLoopE g t (acc.push (foldPairE a b g))
  | [a], acc => acc.push (mulE (subE oneE g) a)
  | [], acc => acc

/-- Fixes the lowest variable of a vector over E at g. A last entry without a partner has the
partner 0. -/
def foldStepE (g : E) (v : List E) : List E := (foldLoopE g v #[]).toList

/-- The value at the point z of the multilinear polynomial of a vector over E. The vector is meant
to have at most 2^k entries, with k the length of z. This is not tested: entries from 2^k on are
ignored, where the C++ mle_eval stops the program. The empty vector has the value 0. -/
def mleEvalE : List E → List E → E
  | v, [] => v.headD zeroE
  | v, g :: z => mleEvalE (foldStepE g v) z

/-- As `mleEvalE`, for a vector over the base field. -/
def mleEvalF : List F → List E → E
  | v, [] => ofF (v.headD 0)
  | v, g :: z => mleEvalE (foldStepF g v) z

/-- `squaresOf n z` is the list of the n elements z, z^2, z^4, and so on: each is the square of the
one before it. -/
def squaresOf : Nat → F → List F
  | 0, _ => []
  | n + 1, z => z :: squaresOf n (mulF z z)

/-- The product of f[i] over the bits i that are set in j. -/
def productIndex : List F → Nat → F
  | [], _ => 1
  | x :: f, j => if j % 2 == 1 then mulF x (productIndex f (j / 2)) else productIndex f (j / 2)

/-- The first n entries of the product form of the factors f: entry j is `productIndex f j`. If n is
above 2^k, with k the length of f, the result has only 2^k entries, where the C++ product_table
stops the program. -/
def productTable (f : List F) (n : Nat) : Array F :=
  (f.foldl (fun (a : Array F) x => if a.size < n then a ++ a.map (mulF · x) else a) #[1]).extract
    0 n

/-- r times the value at z of the multilinear polynomial of the products of the factors f: the
product of z[t] (f[t] - 1) + 1, as far as the shorter list goes. -/
def productMleFrom : List F → List E → E → E
  | x :: f, g :: z, r => productMleFrom f z (mulE r (addE (scaleE (subF x 1) g) oneE))
  | _, _, r => r

/-- The value at z of the multilinear polynomial whose value at the corner j is
`productIndex f j`. -/
def productMle (f : List F) (z : List E) : E := productMleFrom f z oneE

/-- The loop of `dotStepF`. acc holds the results so far. -/
def dotLoopF (x : F) : List F → Array F → Array F
  | a :: b :: t, acc => dotLoopF x t (acc.push (addF a (mulF b x)))
  | [a], acc => acc.push a
  | [], acc => acc

/-- One step of `productDotF`: each pair a, b becomes a + x b. -/
def dotStepF (x : F) (v : List F) : List F := (dotLoopF x v #[]).toList

/-- The loop of `dotStepE`. acc holds the results so far. -/
def dotLoopE (x : F) : List E → Array E → Array E
  | a :: b :: t, acc => dotLoopE x t (acc.push (maddS a x b))
  | [a], acc => acc.push a
  | [], acc => acc

/-- One step of `productDotE`: each pair a, b becomes a + x b. -/
def dotStepE (x : F) (v : List E) : List E := (dotLoopE x v #[]).toList

/-- The sum of v[j] `productIndex f j` over a vector v over the base field. The vector is meant to
have at most 2^k entries, with k the length of f. This is not tested: entries from 2^k on are
ignored, where the C++ product_dot stops the program. The empty vector has the sum 0. -/
def productDotF : List F → List F → F
  | v, [] => v.headD 0
  | v, x :: f => productDotF (dotStepF x v) f

/-- As `productDotF`, for a vector over E. -/
def productDotE : List E → List F → E
  | v, [] => v.headD zeroE
  | v, x :: f => productDotE (dotStepE x v) f

end OnBytes
