-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Pairs.lean: what an honest prover computes of its summand in a masked
sumcheck whose summand is a sum of weighted products of pairs of multilinear maps and whose
variables are each summed at a point. Definitions with code, and tests; no theorem.

The verifier's side is Johnson/Desc/Part/MaskedSum4.lean, as the output head's sub-protocol calls it
(Johnson/Desc/Kinds/HeadParts.lean, `heardBy`): every variable is `.point z 3`, that is, a round's
polynomial g has three coefficients and is summed as (1 - z) g(0) + z g(1); behind the variables
comes one further variable Y, of degree 2, read at 0. All four sumchecks of the output head's own
rounds have a summand of this one form, so the arithmetic is written once, here, free of any frame
for provers: this file knows neither rounds nor messages nor masks of the hiding polynomial.

  `PairSum`          the sum: the points z, the maps, the weighted pairs
  `PairSum.on`       the summand on one value for each map
  `PairSum.onLines`  the summand on one line for each map: a polynomial of three coefficients
  `atFirst`          a map with its first variables at challenges
  `PairSum.total`    the sum
  `PairSum.round`    the summand's round polynomial in the next variable
  `PairSum.ends`     the end values: each map at all the challenges
  `PairSum.inY`      the summand in Y, each end value being its true value plus Y times a mask entry

The order of the bits. A map is a function of an index below 2^n, n the number of points. The first
variable, whose point is the first of z and whose challenge is the first drawn, is the HIGHEST bit
of the index: as with `eq`, whose point has the coordinate of the highest bit first.

What the round polynomial is. With the challenges rs of the variables in front, in the next variable
X: the sum, over the bits b of the later variables, of (the equality weight of b at the later
points) times (the summand on the maps at (rs, X, b)). IT BEARS NO EQUALITY FACTOR OF THE VARIABLE
AT HAND OR OF THOSE IN FRONT: the verifier's way of summing, (1 - z) g(0) + z g(1), brings the
factor of the variable at hand by itself. So (1 - z) g(0) + z g(1) of a round is the round before at
its challenge, and of the first round the sum.

The tests, at the end of the file. Each of the four functions is held (1) against a plain sum over
all corners, in which a map's value at a point is the sum over ALL indices under `eq` and no
variable is ever laid by folding; (2) against written numbers, which were computed apart from Lean
by a short program in another language: values by the same plain sums, a polynomial's coefficients
by interpolation from its values at 0, 1 and -1; (3) together, against the verifier's own walk
(`complete`, `after`): from the sum, through what is sent of each round, it arrives at the summand
on the end values as shown. Each test is shown to be able to fail: with one entry of one map, one
sent scalar, one mask entry or one weight turned by 1 it says no.

Limits. The arithmetic is the program's, on words. `round` has a meaning only with fewer challenges
than variables; `ends` and `inY` read the first n challenges and want n of them; where challenges
lack, the variables left count as 0. A pair that names a map which is not in the list counts that
map as 0; a mask entry that lacks counts as 0. As written, each call names every entry of every map
once (laying a variable names each of its two halves once); no test counts the readings. The tests
are evaluations at a few fixed small sums.
Nothing on any property of the protocol.

-/
import Johnson.Desc.Kinds.HeadParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Honest
open OnBytes (E)

/-- A sum over the 2^n indices (n := z.length; the highest bit first), under the equality weights of
z, of weighted products of pairs of maps. -/
structure PairSum where
  /-- the points at which the variables are summed, that of the highest bit first -/
  z : List E
  /-- the maps: each a function of the index -/
  maps : List (Nat → E)
  /-- the summand's terms: a weight, and the numbers of two maps in the list -/
  pairs : List (E × Nat × Nat)

/-- Polynomials of three coefficients, added. -/
def add3 (g h : List E) : List E := List.zipWith (· + ·) g h

/-- **The summand on values**, one for each map: the sum over the pairs of weight times value times
value. -/
def PairSum.on (s : PairSum) (v : List E) : E :=
  s.pairs.foldl (fun t p => t + p.1 * (v.getD p.2.1 0 * v.getD p.2.2 0)) 0

/-- **The summand on lines**, one for each map: the line (a, a') is a + a' X. Three coefficients,
the lowest first. -/
def PairSum.onLines (s : PairSum) (l : List (E × E)) : List E :=
  s.pairs.foldl (fun g p =>
    let a := l.getD p.2.1 (0, 0)
    let b := l.getD p.2.2 (0, 0)
    add3 g [p.1 * (a.1 * b.1), p.1 * (a.1 * b.2 + a.2 * b.1), p.1 * (a.2 * b.2)]) [0, 0, 0]

/-- A multilinear map on n bits with its first variables at the challenges rs: a map on the bits
that are left. Each step lays the highest bit: f(r, j) = f(0, j) + r (f(1, j) - f(0, j)). -/
def atFirst : Nat → (Nat → E) → List E → Nat → E
  | _, f, [], j => f j
  | n, f, r :: rs, j =>
    atFirst (n - 1) (fun i => let a := f i; a + r * (f (2 ^ (n - 1) + i) - a)) rs j

/-- **The sum.** -/
def PairSum.total (s : PairSum) : E :=
  let w := eqAll s.z.toArray
  ∑ i < 2 ^ s.z.length, w.getD i 0 * s.on (s.maps.map (· i))

/-- **The summand's round polynomial** in the next variable, of the challenges rs of the variables
in front: three coefficients, the lowest first. The later variables are summed under their points'
equality weights. -/
def PairSum.round (s : PairSum) (rs : List E) : List E :=
  let m := s.z.length - rs.length - 1
  let w := eqAll (s.z.drop (rs.length + 1)).toArray
  let t := s.maps.map fun f => atFirst s.z.length f rs
  (List.range (2 ^ m)).foldl (fun g b =>
    add3 g ((s.onLines (t.map fun f => let a := f b; (a, f (2 ^ m + b) - a))).map
      (w.getD b 0 * ·))) [0, 0, 0]

/-- **The end values**: each map at all the variables' challenges. -/
def PairSum.ends (s : PairSum) (rs : List E) : List E :=
  s.maps.map fun f => atFirst s.z.length f (rs.take s.z.length) 0

/-- **The summand in the further variable Y**: on the lines (end value) + Y (its mask entry). Three
coefficients, the lowest first. -/
def PairSum.inY (s : PairSum) (rs masks : List E) : List E :=
  s.onLines ((s.ends rs).zipIdx.map fun x => (x.1, masks.getD x.2 0))

/-! ## Tests -/

namespace PairsTest
open Part.MaskedSum (Var Call after valueAt)

/-! ### The plain sums over all corners -/

/-- A map's value at a point: the sum over all indices under the equality weights. -/
def atAll (f : Nat → E) (pt : List E) : E := ∑ i < 2 ^ pt.length, eq pt.toArray i * f i

/-- The m bits of b as elements, the highest first. -/
def bitsE (m b : Nat) : List E :=
  (List.range m).map fun j => if b.testBit (m - 1 - j) then (1 : E) else 0

/-- The sum, by `eq`. -/
def totalAll (s : PairSum) : E :=
  ∑ i < 2 ^ s.z.length, eq s.z.toArray i * s.on (s.maps.map (· i))

/-- The round polynomial's VALUE at x: each map's value at (rs, x, b) is a sum over all corners. -/
def roundAll (s : PairSum) (rs : List E) (x : E) : E :=
  let m := s.z.length - rs.length - 1
  ∑ b < 2 ^ m, eq (s.z.drop (rs.length + 1)).toArray b *
    s.on (s.maps.map fun f => atAll f (rs ++ x :: bitsE m b))

/-- The summand's value at Y = y. -/
def inYAll (s : PairSum) (rs masks : List E) (y : E) : E :=
  s.on (s.maps.zipIdx.map fun x => atAll x.1 rs + y * masks.getD x.2 0)

/-- `round` is held against `roundAll` at four elements: one more than three coefficients can be
bent to meet. -/
def roundFits (s : PairSum) (rs xs : List E) : Bool :=
  (s.round rs).length == 3 && xs.all fun x => valueAt (s.round rs) x == roundAll s rs x

def inYFits (s : PairSum) (rs masks xs : List E) : Bool :=
  (s.inY rs masks).length == 3 && xs.all fun y => valueAt (s.inY rs masks) y == inYAll s rs masks y

/-! ### The verifier's own walk -/

/-- What is sent of the summand's polynomials where the hiding polynomial is 0 and eps is 1: of each
all coefficients but the constant. The last is Y's. -/
def sent (s : PairSum) (rs masks : List E) : List (List E) :=
  ((List.range s.z.length).map fun i => (s.round (rs.take i)).drop 1) ++ [(s.inY rs masks).drop 1]

/-- The call as the output head's sub-protocol lays it (`heardBy`); the lead plays no part here. -/
def call (s : PairSum) : Call :=
  { lead := 0, vs := s.z.map fun x => Var.point x 3, ends := some ⟨2, s.maps.length⟩ }

/-- The verifier's running claim behind all rounds, from the claimed sum c: over the call's own list
of variables, Y last. -/
def walk (s : PairSum) (c : E) (sent : List (List E)) (rs : List E) (beta : E) : E :=
  after (call s).all (sent.zip (rs ++ [beta])) c

/-- The end values as shown. -/
def shown (s : PairSum) (rs masks : List E) (beta : E) : List E :=
  (s.ends rs).zipIdx.map fun x => x.1 + beta * masks.getD x.2 0

/-- Entry j of list number i, plus 1. -/
def turn2 (l : List (List E)) (i j : Nat) : List (List E) :=
  l.zipIdx.map fun x =>
    if x.2 == i then (x.1.zipIdx.map fun y => if y.2 == j then y.1 + 1 else y.1) else x.1

/-- Entry j plus 1. -/
def turn1 (l : List E) (j : Nat) : List E := l.zipIdx.map fun y => if y.2 == j then y.1 + 1 else y.1

/-! ### A sum in three variables: four maps, four pairs, every element with three coordinates -/

/-- Entries without a simple pattern in the index: a power of a fixed number plus a multiple of the
exponent, modulo the prime 2^31 - 1. -/
def word (a t : Nat) : UInt64 := ((a ^ (t + 1) + 12345 * t) % 2147483647).toUInt64
def entry (k i : Nat) : E :=
  ⟨word 1103515245 (8 * k + i + 1), word 22695477 (8 * k + i + 1), word 134775813 (8 * k + i + 1)⟩

def s3 : PairSum :=
  { z := [⟨5, 1, 2⟩, ⟨9, 0, 4⟩, ⟨2, 7, 1⟩]
    maps := (List.range 4).map entry
    pairs := [(⟨2, 1, 0⟩, 0, 1), (⟨3, 0, 5⟩, 2, 3), (⟨1, 4, 1⟩, 0, 0), (⟨7, 0, 0⟩, 1, 2)] }
def r3 : List E := [⟨11, 3, 8⟩, ⟨6, 13, 2⟩, ⟨4, 1, 17⟩]
def m3 : List E := [⟨31, 2, 1⟩, ⟨8, 19, 3⟩, ⟨5, 6, 23⟩, ⟨14, 1, 9⟩]
def beta3 : E := ⟨21, 2, 5⟩
def xs : List E := [0, 1, 2, ⟨77, 5, 1234567⟩]

/-- The sum with entry i of map k turned by 1. -/
def bent (s : PairSum) (k i : Nat) : PairSum :=
  { s with maps := s.maps.zipIdx.map fun x =>
      if x.2 == k then (fun j => if j == i then x.1 j + 1 else x.1 j) else x.1 }

/-- All (map, index). -/
def cells : List (Nat × Nat) := (List.range 4).flatMap fun k => (List.range 8).map fun i => (k, i)

#guard entry 0 0 == ⟨1685022083, 2133602336, 1424386403⟩
#guard entry 3 7 == ⟨2004522381, 1545331478, 975691368⟩

-- (1) against the plain sums
#guard s3.total == totalAll s3
#guard (List.range 3).all fun i => roundFits s3 (r3.take i) xs
#guard s3.ends r3 == s3.maps.map (atAll · r3)
#guard inYFits s3 r3 m3 xs

-- (2) against written numbers
#guard s3.total == ⟨2715941785338517749, 13224059035561488135, 16989360775212769834⟩
#guard s3.round [] ==
   [⟨15082613736231599136, 12942379268251623608, 16966144422946357481⟩,
    ⟨8729633517888495111, 6286242453902106604, 6191063614422829281⟩,
    ⟨9839030878541088890, 9605314101240331017, 1654546655844716386⟩]
#guard s3.round (r3.take 1) ==
   [⟨8835888036485151114, 9292476038114496968, 1587118815400500651⟩,
    ⟨3363641527844634652, 17565274958940653233, 5980265045340535588⟩,
    ⟨3800313588453411743, 16375210591905269358, 14382569380424285978⟩]
#guard s3.round (r3.take 2) ==
   [⟨213447299399210658, 1093568067793333882, 14883395503982048106⟩,
    ⟨4899272966119609640, 459477577929104893, 1967175255863361506⟩,
    ⟨13429166751682852528, 9067272667966398717, 5951224512667672862⟩]
#guard s3.ends r3 ==
   [⟨18446696281013120664, 18446711186365918406, 18446720449372095924⟩,
    ⟨18446691976257185523, 18446687549299662040, 18446711279917702258⟩,
    ⟨2264964342662, 18446742458085798568, 18446742412924767877⟩,
    ⟨25845148273584, 14006379092280, 12745529793201⟩]
#guard s3.inY r3 m3 ==
   [⟨1360390353058824770, 6316168239087872362, 11987192848217512989⟩,
    ⟨18401561510472836229, 18413176357166774786, 18419634207237675983⟩,
    ⟨14975, 12860, 6858⟩]

-- (3) the verifier's walk arrives at the summand on the end values as shown
#guard (sent s3 r3 m3).map (·.length) == [2, 2, 2, 2]
#guard walk s3 s3.total (sent s3 r3 m3) r3 beta3 == s3.on (shown s3 r3 m3 beta3)
-- and, round by round, a round's sum is the round before at its challenge
#guard (1 - s3.z.getD 0 0) * valueAt (s3.round []) 0 + s3.z.getD 0 0 * valueAt (s3.round []) 1
  == s3.total
#guard (List.range 2).all fun i =>
  let g := s3.round (r3.take (i + 1))
  (1 - s3.z.getD (i + 1) 0) * valueAt g 0 + s3.z.getD (i + 1) 0 * valueAt g 1
    == valueAt (s3.round (r3.take i)) (r3.getD i 0)
#guard valueAt (s3.inY r3 m3) 0 == valueAt (s3.round (r3.take 2)) (r3.getD 2 0)
#guard valueAt (s3.inY r3 m3) 0 == s3.on (s3.ends r3)

-- THE TESTS CAN FAIL. One entry of one map turned by 1, whichever: the sum, every round, that map's
-- end value and the polynomial in Y all move, and each of the four unbent functions no longer meets
-- the bent plain sum.
#guard cells.all fun c =>
  let t := bent s3 c.1 c.2
  t.total != s3.total && totalAll t != s3.total
#guard cells.all fun c => (List.range 3).all fun i =>
  let t := bent s3 c.1 c.2
  t.round (r3.take i) != s3.round (r3.take i) &&
    !(xs.all fun x => valueAt (s3.round (r3.take i)) x == roundAll t (r3.take i) x)
#guard cells.all fun c =>
  let t := bent s3 c.1 c.2
  (t.ends r3).getD c.1 0 != (s3.ends r3).getD c.1 0 &&
    ((List.range 4).all fun k => k == c.1 || (t.ends r3).getD k 0 == (s3.ends r3).getD k 0) &&
    s3.ends r3 != t.maps.map (atAll · r3)
#guard cells.all fun c =>
  let t := bent s3 c.1 c.2
  t.inY r3 m3 != s3.inY r3 m3 &&
    !(xs.all fun y => valueAt (s3.inY r3 m3) y == inYAll t r3 m3 y)
-- and the bent sum passes the tests in its own right
#guard cells.all fun c => (bent s3 c.1 c.2).total == totalAll (bent s3 c.1 c.2) &&
  walk (bent s3 c.1 c.2) (bent s3 c.1 c.2).total (sent (bent s3 c.1 c.2) r3 m3) r3 beta3
    == (bent s3 c.1 c.2).on (shown (bent s3 c.1 c.2) r3 m3 beta3)
-- One sent scalar turned by 1, whichever; the claimed sum; one shown end value; one mask entry on
-- one side alone; one weight: the walk misses.
#guard (List.range 4).all fun i => (List.range 2).all fun j =>
  walk s3 s3.total (turn2 (sent s3 r3 m3) i j) r3 beta3 != s3.on (shown s3 r3 m3 beta3)
#guard walk s3 (s3.total + 1) (sent s3 r3 m3) r3 beta3 != s3.on (shown s3 r3 m3 beta3)
#guard (List.range 4).all fun j =>
  walk s3 s3.total (sent s3 r3 m3) r3 beta3 != s3.on (turn1 (shown s3 r3 m3 beta3) j)
#guard (List.range 4).all fun j =>
  walk s3 s3.total (sent s3 r3 (turn1 m3 j)) r3 beta3 != s3.on (shown s3 r3 m3 beta3)
#guard (List.range 4).all fun j =>
  let t : PairSum := { s3 with pairs := s3.pairs.zipIdx.map fun x =>
    if x.2 == j then (x.1.1 + 1, x.1.2) else x.1 }
  t.total != s3.total && t.round [] != s3.round [] && t.inY r3 m3 != s3.inY r3 m3 &&
    t.ends r3 == s3.ends r3
-- The order of the bits is held: with the lowest bit first the end values are others.
#guard s3.ends r3 != s3.maps.map (atAll · r3.reverse)
-- An equality factor of the variable at hand does not belong in the round: with it the walk's first
-- step misses.
#guard (1 - s3.z.getD 0 0) * ((1 - s3.z.getD 0 0) * valueAt (s3.round []) 0)
  + s3.z.getD 0 0 * (s3.z.getD 0 0 * valueAt (s3.round []) 1) != s3.total

/-! ### One variable, by hand

z = 3; a = (2, 5), b = (7, 11); the summand a b. The sum: (1 - 3) 14 + 3 * 55 = 137. The round:
(2 + 3 X) (7 + 4 X) = 14 + 29 X + 12 X^2. At r = 10: a = 32, b = 47. With the mask entries 1 and 2:
(32 + Y) (47 + 2 Y) = 1504 + 111 Y + 2 Y^2. -/

def s1 : PairSum :=
  { z := [3], maps := [fun i => if i == 0 then 2 else 5, fun i => if i == 0 then 7 else 11]
    pairs := [(1, 0, 1)] }

#guard s1.total == 137
#guard s1.round [] == [14, 29, 12]
#guard s1.ends [10] == [32, 47]
#guard s1.inY [10] [1, 2] == [1504, 111, 2]

/-! ### Points 1/2, and no variable -/

/-- Under n points 1/2 the sum is 2^-n times the plain sum. -/
def sHalf : PairSum := { s3 with z := (halves 3).toList }
#guard (8 : E) * sHalf.total == ∑ i < 8, s3.on (s3.maps.map (· i))
#guard (List.range 3).all fun i => roundFits sHalf (r3.take i) xs
#guard walk sHalf sHalf.total (sent sHalf r3 m3) r3 beta3 == sHalf.on (shown sHalf r3 m3 beta3)
#guard sHalf.total != s3.total

/-- Without a variable the sum is the summand at index 0. -/
def s0 : PairSum := { s3 with z := [] }
#guard s0.total == s3.on (s3.maps.map (· 0)) && s0.ends [] == s3.maps.map (· 0)
#guard walk s0 s0.total (sent s0 [] m3) [] beta3 == s0.on (shown s0 [] m3 beta3)

/-! ### The limits, as the head of the file states them -/

-- A pair that names a map which is not in the list counts that map as 0.
#guard ({ s3 with pairs := [(1, 0, 4)] } : PairSum).total == 0 &&
  ({ s3 with pairs := [(1, 0, 4)] } : PairSum).round [] == [0, 0, 0] &&
  ({ s3 with pairs := [(1, 0, 3)] } : PairSum).total != 0
-- A mask entry that lacks counts as 0.
#guard s3.inY r3 (m3.take 2) == s3.inY r3 (m3.take 2 ++ [0, 0]) &&
  s3.inY r3 (m3.take 2) != s3.inY r3 m3
-- Where challenges lack, the variables left count as 0.
#guard s3.ends (r3.take 2) == s3.maps.map (atAll · (r3.take 2 ++ [0])) &&
  s3.ends (r3.take 2) != s3.ends r3
-- Challenges beyond the number of variables are not read.
#guard s3.ends (r3 ++ [beta3]) == s3.ends r3 && s3.inY (r3 ++ [beta3]) m3 == s3.inY r3 m3

end PairsTest

end VerifiableInference.Desc.Kinds.Head.Honest
