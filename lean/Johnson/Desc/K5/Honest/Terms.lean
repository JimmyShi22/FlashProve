-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Terms.lean: the form of the summands of an attention segment's masked
sumchecks, for the honest prover's side, and what a sumcheck's prover computes of such a summand.
Definitions with code; no theorem. Tests: Johnson/Desc/K5/Honest/TermsToy.lean [not in this library;
so here read: not tested in this library].

The form. Each of the segment's sumchecks sums, over a cube of zeros and ones, a polynomial
  S(x) = the sum over t of  c_t(x) times the product over j of (a_tj(x) e_n(x) + b_tj(x)), n = n_tj,
where the e_n are hidden maps, whose values at the last point are the sumcheck's end values, and c,
a and b are public. A sum of weighted products of two maps is the case of two factors with a = 1 and
b = 0. AN END VALUE IS WHAT `endAt` YIELDS. Where the protocol counts a constant into an end value
(a map "A - 1", or "gamma + v"), the constant stands inside `endAt`, under that end value's own
number, and b is 0. With the constant in b the sum and every round polynomial are the same, but the
end value that is sent is another, or the polynomial in Y is: no test on this file's functions tells
which of the two is the protocol's; only the claim that the verifier's text leaves does. A number
that stands in two factors has one mask entry in Y.

  `addP`, `scaleP`, `mulP`, `lineP`   polynomials in one variable as lists of coefficients, the
                                      lowest first
  `cube`                              all points of zeros and ones
  `Factor`, `Term`, `Summand`         the form
  `Summand.at`, `Summand.total`       the summand at a point; its sum over the whole cube
  `Summand.round`                     the round polynomial in the next variable, all coefficients
  `Summand.inY`                       at the last point, each end value with Y times a mask entry
                                      added: the polynomial in Y
  `Summand.endsAt`                    the end values
  `Summand.fits`, `Summand.cutIsZero`  tests for a caller: the counts are a call's; what lies beyond
                                      a round's number of coefficients is 0

How a round polynomial is made. With the first variables at the challenges and the later ones at
zeros and ones, c and every factor are taken at 0 and at 1 in the round's variable; the lines
through these two values are multiplied. No division is needed.

The caller's duty, which no line here tests: that c and each factor's value are of degree at most 1
in each variable, and that the number of terms, the numbers of their factors and the numbers n do
not depend on the point. Where the two lists of terms differ in length the shorter one counts.
Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Field.Ext

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)

/-! ## Polynomials as lists -/

/-- The sum of two polynomials. -/
def addP : List E → List E → List E
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => addE x y :: addP a b

/-- k times a polynomial. -/
def scaleP (k : E) (a : List E) : List E := a.map (mulE k)

/-- The product of two polynomials. -/
def mulP : List E → List E → List E
  | [], _ => []
  | x :: a, b => addP (scaleP x b) (zeroE :: mulP a b)

/-- The polynomial of degree at most 1 with the value v0 at 0 and v1 at 1. -/
def lineP (v0 v1 : E) : List E := [v0, subE v1 v0]

/-- The sum of a list of polynomials. -/
def sumP (l : List (List E)) : List E := l.foldl addP []

/-- The sum of a list of elements. -/
def sumE (l : List E) : E := l.foldl addE zeroE

/-- All points of n zeros and ones; the first coordinate turns slowest. -/
def cube : Nat → List (List E)
  | 0 => [[]]
  | n + 1 => (cube n).map (zeroE :: ·) ++ (cube n).map (oneE :: ·)

/-! ## The form -/

/-- A factor: a times the hidden map number n, plus b. -/
structure Factor where
  a : E
  n : Nat
  b : E

/-- A term: a public coefficient and its factors. -/
structure Term where
  c : E
  fs : List Factor

/-- **A summand**: hidden maps, and at each point the public coefficients that join them. -/
structure Summand where
  /-- the number of variables -/
  vars : Nat
  /-- the number of hidden maps, which is the number of end values -/
  ends : Nat
  /-- the hidden map number n at a point of `vars` coordinates -/
  endAt : List E → Nat → E
  /-- the terms at that point: their public coefficients, and which maps they multiply -/
  terms : List E → List Term

/-- A factor's value at a point. -/
def Summand.factorAt (S : Summand) (x : List E) (f : Factor) : E :=
  addE (mulE f.a (S.endAt x f.n)) f.b

/-- The summand at a point. -/
def Summand.at (S : Summand) (x : List E) : E :=
  sumE ((S.terms x).map fun t => t.fs.foldl (fun p f => mulE p (S.factorAt x f)) t.c)

/-- The sum over the whole cube. -/
def Summand.total (S : Summand) : E := sumE ((cube S.vars).map S.at)

/-- A term as a polynomial in one variable, of its letters and maps at the two points that differ in
that variable alone. -/
def Summand.termLine (S : Summand) (x0 x1 : List E) (t0 t1 : Term) : List E :=
  (t0.fs.zip t1.fs).foldl (fun p f => mulP p (lineP (S.factorAt x0 f.1) (S.factorAt x1 f.2)))
    (lineP t0.c t1.c)

/-- **The round polynomial** in the variable number rs.length, from 0: the variables in front at rs,
the later ones summed over zeros and ones. All its coefficients, the lowest first. -/
def Summand.round (S : Summand) (rs : List E) : List E :=
  sumP ((cube (S.vars - rs.length - 1)).map fun y =>
    let x0 := rs ++ zeroE :: y
    let x1 := rs ++ oneE :: y
    sumP (((S.terms x0).zip (S.terms x1)).map fun t => S.termLine x0 x1 t.1 t.2))

/-- **The polynomial in the further variable Y** at the point rs: each end value number n with Y
times m[n] added. -/
def Summand.inY (S : Summand) (rs m : List E) : List E :=
  sumP ((S.terms rs).map fun t =>
    t.fs.foldl (fun p f => mulP p [S.factorAt rs f, mulE f.a (m.getD f.n zeroE)]) [t.c])

/-- **The end values** at the point rs. -/
def Summand.endsAt (S : Summand) (rs : List E) : List E := (List.range S.ends).map (S.endAt rs)

/-- The summand has as many variables and end values as a sumcheck with these two numbers. -/
def Summand.fits (S : Summand) (vars ends : Nat) : Bool := S.vars == vars && S.ends == ends

/-- What lies beyond the first d coefficients of the round polynomial is 0: a sender that keeps d
coefficients drops nothing. -/
def Summand.cutIsZero (S : Summand) (rs : List E) (d : Nat) : Bool :=
  ((S.round rs).drop d).all (· == zeroE)

end H2K5.Honest
