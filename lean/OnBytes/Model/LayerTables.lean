-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/LayerTables.lean: three public tables of the layer sub-proofs, in whole numbers.

Three tables rest on real functions: SILU, the sigmoid (a part of table FS) and the rotary table of
cosines and sines. The C++ verifier computes them in 64-bit floating-point numbers
(verifier/src/cp_verify.cpp: gateTableEntry, sigmoidTableEntry, sigmoidClampTableEntry, ropeC) and
compares their digests with the parameter file.

This file computes the same tables without floating-point numbers. It follows the C++ expressions
step by step. Each real function (exp, a power, cosine, sine) is computed in fixed-point arithmetic
with 320 binary places, and the result of each step is rounded as the floating-point format rounds:
to 53 significant bits, to the nearest, ties to the even neighbour (roundD). The rounding of the
steps matters. For large arguments 64 SILU(z) can lie below some n + 1/2, n a whole number, by less
than the format can represent. The C++ value is then n + 1/2 itself, which is rounded up to n + 1.

How the functions are computed.
 - exp at the multiples of a step 2^-eg: the series for exp(2^-eg), then repeated products.
 - theta0^(-2 i / dh), where dh is a power of two: repeated square roots of 1 / theta0, then
   repeated products.
 - cosine and sine of the angle t p, p a rounded power: their series at p, then a rotation by p for
   each further token. The C++ angle is the rounded product of t and p. The difference between it
   and t p is exact in fixed-point, and a second, small rotation accounts for it.

Main definitions: roundD, expPowers, siluWord, sigmoidAt, clampHalf, fsWord, gateTables, ropeTable.

What is not claimed: nothing is proved here. In particular it is not shown that 320 places are
always enough: a rounding here is that of the real value unless that value is nearer to the midpoint
of two neighbouring results than the error of the fixed-point computation. A library's exp, pow, cos
or sin need not round correctly in the last bit, so the tables could differ from those of a given
C++ build. Each program compares its own table with the digest in the parameter file and refuses if
they differ. So if the two tables differed at some parameters, a file with the digest of this file's
table would pass here and be refused by the C++ verifier: this program would accept more, and its
lookups would use another table. For a file without the digest lines nothing is compared: each
program then uses its own table, and a difference would go unseen and could change a decision either
way. What the tests of the library show is said in OnBytes/Model/TestLayerTables.lean: equality at
the numbers of two configurations.
Numbers too large or too small for the floating-point format do not occur at the admitted parameters
and are not handled.
-/
import OnBytes.Iop.Ground

namespace OnBytes.Model.Layer

/-! ## Fixed-point numbers and rounding -/

/-- The number 1 in fixed-point arithmetic: 320 binary places. -/
def fxOne : Nat := 2 ^ 320

/-- The number of binary digits of n. -/
def bitLen (n : Nat) : Nat := if n == 0 then 0 else Nat.log2 n + 1

/-- The fraction N / D, D not 0, rounded to 53 significant bits, to the nearest, ties to the even
neighbour. The result is a pair (m 2^a, 2^b), numerator and denominator, with m at most 2^53 and a
or b equal to 0. -/
def roundD (N D : Nat) : Nat × Nat :=
  if N == 0 then (0, 1)
  else
    let up := bitLen D + 54
    let bn := bitLen N
    -- The quotient q of N 2^(up - bn) by D has 54 or 55 bits.
    let num := N * 2 ^ (up - bn)
    let den := D * 2 ^ (bn - up)
    let q := num / den
    let drop := bitLen q - 53
    let low := q % 2 ^ drop
    let half := 2 ^ (drop - 1)
    let m := q / 2 ^ drop
    let m := if low > half || (low == half && (num % den != 0 || m % 2 == 1)) then m + 1 else m
    (m * 2 ^ (drop + bn - up), 2 ^ (up - (drop + bn)))

/-- k times the fraction x, rounded to a whole number, halves upwards. -/
def roundHalfUp (k : Nat) (x : Nat × Nat) : Nat := (2 * k * x.1 + x.2) / (2 * x.2)

/-- The product of two fixed-point numbers of either sign, rounded towards 0. -/
def mulFx (a b : Int) : Int := (a * b).tdiv fxOne

/-! ## The exponential function -/

/-- The rest of the series for exp(1 / step): adds term / (step k), then that quotient over
step (k + 1), and so on, until a term is 0. The argument after step bounds the number of terms. -/
def expSeries (step : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, sum => sum
  | fuel + 1, k, term, sum =>
    let next := term / (step * k)
    if next == 0 then sum else expSeries step fuel (k + 1) next (sum + next)

/-- Appends x, x u, x u^2 and so on to a, n numbers in all. -/
def fxPowersLoop (u : Nat) : Nat → Nat → Array Nat → Array Nat
  | 0, _, a => a
  | n + 1, x, a => fxPowersLoop u n (x * u / fxOne) (a.push x)

/-- exp(c / 2^eg) for c = 0 .. n, in fixed-point. -/
def expPowers (eg n : Nat) : Array Nat :=
  fxPowersLoop (expSeries (2 ^ eg) 400 1 fxOne fxOne) (n + 1) fxOne
    (Array.emptyWithCapacity (n + 1))

/-- 1 + exp(-z), by the two rounded steps of the C++ expression, for z = a / 2^eg, or its negative
if neg. X: expPowers eg n with a at most n. -/
def onePlusExp (X : Array Nat) (a : Nat) (neg : Bool) : Nat × Nat :=
  let x := X.getD a fxOne
  let e := if neg then roundD x fxOne else roundD fxOne x
  roundD (e.2 + e.1) e.2

/-- Entry t of table SILU, plus 4096: 64 z / (1 + exp(-z)), rounded, halves away from 0, and clamped
to -smax .. smax. Here z = c / 2^eg, and c is t - 2^15 clamped so that -64 <= z < 64. smax is at
most 4095 (the reader of the parameter file tests it), so 4096 - v is never cut off at 0.
C++: gateTableEntry. -/
def siluWord (eg smax : Nat) (X : Array Nat) (t : Nat) : Nat :=
  let top := 64 * 2 ^ eg
  let neg := decide (t < 32768)
  let a := if neg then min (32768 - t) top else min (t - 32768) (top - 1)
  let s := onePlusExp X a neg
  let v := min (roundHalfUp 64 (roundD (a * s.2) (2 ^ eg * s.1))) smax
  if neg then 4096 - v else 4096 + v

/-- 16 times the rounded value of 4096 / (1 + exp(-z)) at z = (t - 2^15) / 256. X: expPowers 8 n
with n at least 2^15. C++: sigmoidTableEntry. -/
def sigmoidAt (X : Array Nat) (t : Nat) : Nat :=
  let neg := decide (t < 32768)
  let s := onePlusExp X (if neg then 32768 - t else t - 32768) neg
  16 * roundHalfUp 1 (roundD (4096 * s.2) s.1)

/-- Entry t of the upper half of table FS with the gate's clamp: t - 49152 clamped to -127 .. 127,
plus 128. -/
def clampHalf (t : Nat) : Nat := (if t + 127 < 49152 then 0 else min (t + 127 - 49152) 254) + 1

/-- Entry t of table FS: the sigmoid; with the gate's clamp, the middle half of the sigmoid's
entries and then the clamp. C++: sigmoidClampTableEntry. -/
def fsWord (gcl : Bool) (X : Array Nat) (t : Nat) : Nat :=
  if !gcl then sigmoidAt X t else if t < 32768 then sigmoidAt X (t + 16384) else clampHalf t

/-! ## The rotary table -/

/-- Newton's steps for the whole part of a square root, from a start that is not below it. The
argument after n bounds the number of steps. -/
def isqrtLoop (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x =>
    let y := (x + n / x) / 2
    if y ≥ x then x else isqrtLoop n fuel y

/-- The whole part of the square root of n. -/
def isqrt (n : Nat) : Nat := if n < 2 then n else isqrtLoop n 2000 (2 ^ ((bitLen n + 1) / 2))

/-- The square root of a fixed-point number, k times over. -/
def rootLoop : Nat → Nat → Nat
  | 0, q => q
  | k + 1, q => rootLoop k (isqrt (q * fxOne))

/-- The rest of the series of cosine and sine. x2: the square of the argument; k: the number of the
next pair of terms; tc, ts: the last terms; c, s: the sums so far. The argument after x2 bounds the
number of terms. -/
def cosSinLoop (x2 : Int) : Nat → Nat → Int → Int → Int → Int → Int × Int
  | 0, _, _, _, c, s => (c, s)
  | fuel + 1, k, tc, ts, c, s =>
    let tc' := (-(mulFx tc x2)).tdiv ((2 * k - 1) * (2 * k) : Nat)
    let ts' := (-(mulFx ts x2)).tdiv ((2 * k) * (2 * k + 1) : Nat)
    if tc' == 0 && ts' == 0 then (c, s) else cosSinLoop x2 fuel (k + 1) tc' ts' (c + tc') (s + ts')

/-- Cosine and sine of a fixed-point number between -1 and 1. -/
def cosSin (x : Int) : Int × Int := cosSinLoop (mulFx x x) 200 1 fxOne x fxOne x

/-- The pair (c, s) rotated by the angle whose cosine and sine are r. -/
def turn (c s : Int) (r : Int × Int) : Int × Int :=
  (mulFx c r.1 - mulFx s r.2, mulFx s r.1 + mulFx c r.2)

/-- 2^cs times a cosine or sine, by the rounded steps of the C++ expression, plus 4096. cs is 12
(the layout tests it), so 4096 - v is never cut off at 0. -/
def ropeWord (cs : Nat) (val : Int) : Nat :=
  let v := roundHalfUp (2 ^ cs) (roundD val.natAbs fxOne)
  if val < 0 then 4096 - v else 4096 + v

/-- Fills in the entries of pair i for the tokens t, t + 1 and so on, n of them. p: the rounded
power, as a fraction; pf: the same in fixed-point; r: cosine and sine of p; (c, s): cosine and sine
of t p. T: the number of tokens; half: the number of pairs. -/
def ropeTokens (cs T half i : Nat) (p : Nat × Nat) (pf : Nat) (r : Int × Int) :
    Nat → Nat → Int → Int → Array Nat → Array Nat
  | 0, _, _, _, a => a
  | n + 1, t, c, s, a =>
    let ang := roundD (t * p.1) p.2
    let delta : Int := (ang.1 * fxOne / ang.2 : Nat) - (t * pf : Nat)
    let x := turn c s (cosSin delta)
    let a := (a.setIfInBounds (t * half + i) (ropeWord cs x.1)).setIfInBounds
      ((T + t) * half + i) (ropeWord cs x.2)
    let next := turn c s r
    ropeTokens cs T half i p pf r n (t + 1) next.1 next.2 a

/-- Fills in the entries of the pairs i, i + 1 and so on, n of them. u: theta0^(-2 / dh); x: its
power i, both in fixed-point. -/
def ropePairs (cs T half u : Nat) : Nat → Nat → Nat → Array Nat → Array Nat
  | 0, _, _, a => a
  | n + 1, i, x, a =>
    let p := roundD x fxOne
    let pf := p.1 * fxOne / p.2
    ropePairs cs T half u n (i + 1) (x * u / fxOne)
      (ropeTokens cs T half i p pf (cosSin pf) T 0 fxOne 0 a)

/-- The rotary table of a layer with rotary embeddings: for each token t and pair i the rounded
values of 2^cs cos and 2^cs sin of t theta0^(-2 i / dh), each plus 4096; first all cosines, then all
sines. dh must be a power of two and theta0 not 0. C++: ropeC in runStage. -/
def ropeTable (cs theta0 dh lt : Nat) : Array Nat :=
  let half := dh / 2
  let T := 2 ^ lt
  -- The C++ expression converts theta0 to a floating-point number first.
  let th := roundD theta0 1
  ropePairs cs T half (rootLoop (ceilLog2 half) (fxOne * th.2 / th.1)) half 0 fxOne
    (Array.replicate (2 * T * half) 0)

/-! ## The two tables of the gate -/

/-- Table SILU and table FS as words, in the order in which their digests take them: entry t of the
first is 4096 plus the value at t, entry t of the second the value at t. The step between the keys
of SILU is 2^-eg, and its values are clamped to -smax .. smax. Without routed experts (p3 false)
there is no table FS. gcl: the gate's clamp. -/
def gateTables (eg smax : Nat) (p3 gcl : Bool) : Array Nat × Array Nat :=
  let X8 := expPowers 8 32768
  let X := if eg == 8 then X8 else expPowers eg (64 * 2 ^ eg)
  ((Array.range 65536).map (siluWord eg smax X),
   if p3 then (Array.range 65536).map (fsWord gcl X8) else #[])

end OnBytes.Model.Layer
