-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Cube.lean: a sum, over the corners of a cube, of weighted products of pairs
of tables, as the honest prover of a sumcheck reckons it: the sum, each round's polynomial, each
table's value at the challenges; and what one masked sumcheck of the feed-forward layers' rounds
needs beside that. Definitions with code, and tests. No theorem.

NOT SHOWN HERE. No theorem says that `Cube.round` is the summand's partial sum, that `Cube.valuesAt`
is the multilinear extension, or that `polyInY` interpolates: the tests at the foot hold these at
one small cube, summed in both ways, at fixed numbers. Nothing here ties a cube or a job to a
verifier's text, to a committed table or to a model. Nothing holds a job's `ends` and `atEnds`
against its cube. The file depends on no prover framework: whoever plays a sumcheck calls these
functions.

What is summed. A table (`Tab`) holds the values of a multilinear map in n variables at the 2 ^ n
corners: bit v of a corner's number, bit 0 the lowest, is variable v. The summand S is the sum over
the listed pairs (k, a, b) of k times map a times map b. A variable is summed in one of two ways
(docs/format/11-1-machinery.md, "The sumcheck with a hiding sum"): plainly, g(0) + g(1); or at a
coordinate z, (1 - z) g(0) + z g(1). In a cube all variables are summed the same way; at a point rho
variable v has the coordinate rho[n - 1 - v], so that coordinate 0 belongs to the highest bit, as in
`OnBytes.Model.eqTab`. THE EQUALITY WEIGHTS LIE IN THE WAY OF SUMMING AND ARE NO FACTOR OF S: a
round's polynomial holds the weights of the variables that are still to come, none for the variables
that are bound and none for its own; after the last round the running claim is S itself at the
challenges.

The order. Round j runs in variable order[j]. Lists of challenges (rs) are in the order of the
rounds.

  `Tab`, `Way`, `Cube`, `Cube.fits`          the data; the tests on its sizes
  `sidesOf`, `weightsOf`   a variable's two weights; the weights of some variables' corners
  `placeOf`, `lowAt`, `bindAt`, `Cube.bound`   a table with one variable, or the first rounds'
     variables, at challenges
  `termsAt`, `lineAt`   the summand at an entry of some tables; on the line between two entries
  `Cube.total`, `Cube.points`, `Cube.round`, `Cube.valuesAt`, `Cube.pointOf`, `Cube.summandAt`
  `mle`   a table's multilinear extension at a point, by the equality table
  `addP`, `mulP`, `valueP`, `diffs`, `polyInY`   polynomials as lists, lowest coefficient first; a
     function of the end values as a polynomial in the further variable Y
  `Job`   one masked sumcheck's data, free of any prover framework

Limits. Where `Cube.fits` is false the functions still return: an entry beyond a table counts as 0,
a missing map as the empty table, a missing coordinate as 0. At the round of a variable that is
bound already, or of a number from n on, `Cube.bound` halves the tables all the same and strikes
nothing off its list; to a number from n on `Cube.points` and `Cube.pointOf` give the place 0, the
highest variable's, because n - 1 - v stops at 0. `Cube.valuesAt` and `Cube.summandAt` with fewer
challenges than variables return entry 0 of half-bound tables, without a word. `mle` sums as far as
the shorter of the two tables goes, without a word. Each call of `round` binds the tables anew from
the first round on: its cost is linear in the tables' size, for each call. A `Job`'s fields are laid
when the `Job` is made: a lead that holds `Cube.total` costs a whole sum each time. `polyInY` takes
the inverses of 1, .., dY + 1 (the last one is not used), which are units of the field for every
dY + 1 below its characteristic. `valueP`, `addP` and `mulP` are typed here again so that the
file imports no prover framework: the library has the first as `OnBytes.Psc.polyAt`; no lemma ties
them.
Nothing on any property.
No property is claimed.
-/
import OnBytes.Model.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest
open OnBytes (E addE subE mulE negE invE ofF zeroE oneE)

/-! ## 1 The data -/

/-- A multilinear map in n variables by its values at the 2 ^ n corners: bit v of a corner's number,
bit 0 the lowest, is variable v. -/
abbrev Tab : Type := Array E

/-- How the variables of a cube are summed. -/
inductive Way where
  /-- g(0) + g(1) -/
  | plain
  /-- (1 - z) g(0) + z g(1), for variable v of n at z = rho[n - 1 - v] -/
  | point (rho : Array E)

/-- **A sum over a cube.** -/
structure Cube where
  /-- the number of variables -/
  n : Nat
  /-- round j runs in variable order[j] -/
  order : List Nat
  way : Way
  maps : Array Tab
  /-- the summand: the sum of weight times map times map; the maps by their numbers -/
  pairs : List (E × Nat × Nat)

/-- The sizes fit: the order lists each variable once; every map has 2 ^ n entries; the pairs name
maps that are there; a point has n coordinates. -/
def Cube.fits (c : Cube) : Bool :=
  c.order.length == c.n && (List.range c.n).all (fun v => c.order.contains v) &&
    c.maps.all (fun t => t.size == 2 ^ c.n) &&
    c.pairs.all (fun x => decide (x.2.1 < c.maps.size) && decide (x.2.2 < c.maps.size)) &&
    (match c.way with
     | .plain => true
     | .point rho => rho.size == c.n)

/-! ## 2 Weights and binding -/

/-- The weights of a variable's two corners, 0 and 1. -/
def sidesOf (c : Cube) (v : Nat) : E × E :=
  match c.way with
  | .plain => (oneE, oneE)
  | .point rho => (subE oneE (rho.getD (c.n - 1 - v) zeroE), rho.getD (c.n - 1 - v) zeroE)

/-- The weights of all corners of some variables: the product of each variable's weight. The first
member of the list belongs to the highest bit of a corner's number. -/
def weightsOf (ws : List (E × E)) : Array E :=
  ws.foldl
    (fun t w =>
      t.foldl (fun u a => (u.push (mulE a w.1)).push (mulE a w.2))
        (Array.emptyWithCapacity (2 * t.size)))
    #[oneE]

/-- Which bit of a corner's number variable v is, in a table on the variables in the list. -/
def placeOf (left : List Nat) (v : Nat) : Nat := (left.filter (· < v)).length

/-- The number i with a bit 0 laid in at the place whose value is s = 2 ^ place. -/
def lowAt (s i : Nat) : Nat := (i / s) * (2 * s) + i % s

/-- A table with the variable at a place set to r: half as many entries. -/
def bindAt (place : Nat) (r : E) (t : Tab) : Tab :=
  let s := 2 ^ place
  Array.ofFn (n := t.size / 2) fun i =>
    let a := t.getD (lowAt s i.val) zeroE
    addE a (mulE r (subE (t.getD (lowAt s i.val + s) zeroE) a))

/-- The variables that are left, the highest first, and all maps, behind the first rounds. rs: these
rounds' challenges. -/
def Cube.bound (c : Cube) (rs : List E) : List Nat × Array Tab :=
  (c.order.zip rs).foldl
    (fun s x => (s.1.erase x.1, s.2.map (bindAt (placeOf s.1 x.1) x.2)))
    ((List.range c.n).reverse, c.maps)

/-! ## 3 The sum, the rounds, the values -/

/-- The summand at entry j of some tables. -/
def termsAt (pairs : List (E × Nat × Nat)) (ms : Array Tab) (j : Nat) : E :=
  pairs.foldl
    (fun q x =>
      addE q (mulE x.1
        (mulE ((ms.getD x.2.1 #[]).getD j zeroE) ((ms.getD x.2.2 #[]).getD j zeroE))))
    zeroE

/-- **The sum**: each variable summed in the cube's way. -/
def Cube.total (c : Cube) : E :=
  let w := weightsOf ((List.range c.n).reverse.map (sidesOf c))
  (List.range (2 ^ c.n)).foldl
    (fun t i => addE t (mulE (w.getD i zeroE) (termsAt c.pairs c.maps i))) zeroE

/-- The coordinates at which the rounds' variables are summed, in the order of the rounds; none
where the sum is plain. -/
def Cube.points (c : Cube) : List E :=
  match c.way with
  | .plain => []
  | .point rho => c.order.map fun v => rho.getD (c.n - 1 - v) zeroE

/-- The summand on the line from entry j to entry j + s, as a polynomial: three coefficients. -/
def lineAt (pairs : List (E × Nat × Nat)) (ms : Array Tab) (j s : Nat) : E × E × E :=
  pairs.foldl
    (fun q x =>
      let ta := ms.getD x.2.1 #[]
      let tb := ms.getD x.2.2 #[]
      let a := ta.getD j zeroE
      let b := tb.getD j zeroE
      let da := subE (ta.getD (j + s) zeroE) a
      let db := subE (tb.getD (j + s) zeroE) b
      (addE q.1 (mulE x.1 (mulE a b)),
        addE q.2.1 (mulE x.1 (addE (mulE a db) (mulE da b))),
        addE q.2.2 (mulE x.1 (mulE da db))))
    (zeroE, zeroE, zeroE)

/-- **A round's polynomial**, three coefficients, the lowest first: the summand with the variables
of the rounds in front at rs, as a polynomial in this round's variable, the variables of the later
rounds summed in the cube's way. [] if rs has a challenge for every round. -/
def Cube.round (c : Cube) (rs : List E) : List E :=
  match c.order.drop rs.length with
  | [] => []
  | v :: _ =>
    let y := c.bound rs
    let s := 2 ^ placeOf y.1 v
    let rest := y.1.erase v
    let w := weightsOf (rest.map (sidesOf c))
    let q := (List.range (2 ^ rest.length)).foldl
      (fun q i =>
        let g := lineAt c.pairs y.2 (lowAt s i) s
        let k := w.getD i zeroE
        (addE q.1 (mulE k g.1), addE q.2.1 (mulE k g.2.1), addE q.2.2 (mulE k g.2.2)))
      (zeroE, zeroE, zeroE)
    [q.1, q.2.1, q.2.2]

/-- **Each map at all challenges.** -/
def Cube.valuesAt (c : Cube) (rs : List E) : Array E := (c.bound rs).2.map (·.getD 0 zeroE)

/-- The challenges as a point: variable v's at the place n - 1 - v. -/
def Cube.pointOf (c : Cube) (rs : List E) : Array E :=
  (c.order.zip rs).foldl (fun a x => a.set! (c.n - 1 - x.1) x.2) (Array.replicate c.n zeroE)

/-- The summand at all challenges. -/
def Cube.summandAt (c : Cube) (rs : List E) : E :=
  termsAt c.pairs ((c.valuesAt rs).map fun x => #[x]) 0

/-- A table's multilinear extension at a point, coordinate 0 at the highest bit: the sum of the
equality table's entries times the table's. -/
def mle (t : Tab) (z : Array E) : E :=
  ((OnBytes.Model.eqTab z).zip t).foldl (fun s y => addE s (mulE y.1 y.2)) zeroE

/-! ## 4 The further variable -/

/-- The sum of two polynomials. -/
def addP : List E → List E → List E
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => addE x y :: addP a b

/-- The product of two polynomials. -/
def mulP : List E → List E → List E
  | [], _ => []
  | x :: a, b => addP (b.map (mulE x)) (zeroE :: mulP a b)

/-- A polynomial at x. -/
def valueP (g : List E) (x : E) : E := g.foldr (fun c r => addE (mulE r x) c) zeroE

/-- The first members of a list's k successive lists of differences: l[0]; l[1] - l[0]; and so on.
-/
def diffs : Nat → List E → List E
  | 0, _ => []
  | k + 1, l => l.headD zeroE :: diffs k (((l.drop 1).zip l).map fun y => subE y.1 y.2)

/-- **A function of the end values as a polynomial in Y**: the dY + 1 coefficients, the lowest
first, of Y ↦ f (ends + Y masks), for an f of degree at most dY in its arguments together: from its
values at Y = 0, .., dY, by Newton's forward differences. THE EMPTY LIST WHERE THERE ARE NOT AS MANY
MASK ENTRIES AS END VALUES: no entry that lacks is taken for 0. -/
def polyInY (dY : Nat) (f : List E → E) (ends masks : List E) : List E :=
  if ends.length != masks.length then []
  else
    let vals := (List.range (dY + 1)).map fun k =>
      f ((ends.zip masks).map fun x => addE x.1 (mulE (ofF k.toUInt64) x.2))
    ((diffs (dY + 1) vals).zipIdx.foldl
      (fun (s : List E × List E) d =>
        (addP s.1 (s.2.map (mulE d.1)),
          (mulP s.2 [negE (ofF d.2.toUInt64), oneE]).map (mulE (invE (ofF (d.2 + 1).toUInt64)))))
      ([], [oneE])).1

/-- **One masked sumcheck's data.** -/
structure Job where
  /-- the hidden values that are sent in front of the hiding polynomial's sum: none, or the claimed
  sum -/
  lead : List E
  cube : Cube
  /-- the degree in the further variable -/
  dY : Nat
  /-- of the challenges: the true end values, in the order in which they are sent -/
  ends : List E → List E
  /-- of the challenges and of end values: the summand at the challenges on THESE end values -/
  atEnds : List E → List E → E

/-! ## 5 Tests -/

namespace CubeTest

def e (n : UInt64) : E := ⟨n, 0, 0⟩

/-- A way's sum of a polynomial: z: the coordinate, or none. -/
def sumBy (z : Option E) (g : List E) : E :=
  match z with
  | none => addE (valueP g zeroE) (valueP g oneE)
  | some z => addE (mulE (subE oneE z) (valueP g zeroE)) (mulE z (valueP g oneE))

def tA : Tab :=
  Array.ofFn (n := 8) fun i => e (3 + 2 * i.val.toUInt64 + i.val.toUInt64 * i.val.toUInt64)
def tB : Tab := Array.ofFn (n := 8) fun i => e (1 + 5 * i.val.toUInt64)
def tC : Tab := Array.ofFn (n := 8) fun i => ⟨7 + i.val.toUInt64, i.val.toUInt64, 2⟩

/-- Three variables, bound in the order 1, 2, 0; two pairs. -/
def cube (w : Way) (ta : Tab := tA) : Cube :=
  { n := 3, order := [1, 2, 0], way := w, maps := #[ta, tB, tC]
    pairs := [(e 2, 0, 1), (⟨3, 1, 0⟩, 2, 0)] }

def rho : Array E := #[e 11, ⟨13, 2, 5⟩, e 17]
def rs : List E := [e 5, ⟨8, 1, 1⟩, e 9]

/-- The coordinate of round j. -/
def zAt (c : Cube) (j : Nat) : Option E := c.points[j]?

/-- THE CHAIN OF A SUMCHECK: the first round's polynomial sums to the total; each later round's sums
to the round in front at its challenge; the last round's at its challenge is the summand there. -/
def chain (c : Cube) : Bool :=
  sumBy (zAt c 0) (c.round []) == c.total &&
    sumBy (zAt c 1) (c.round (rs.take 1)) == valueP (c.round []) (rs.getD 0 zeroE) &&
    sumBy (zAt c 2) (c.round (rs.take 2)) == valueP (c.round (rs.take 1)) (rs.getD 1 zeroE) &&
    c.summandAt rs == valueP (c.round (rs.take 2)) (rs.getD 2 zeroE)

#guard (cube .plain).fits && (cube (.point rho)).fits
-- a point with a coordinate too few; an order that lists a variable twice; a pair without its map
#guard !(cube (.point (rho.pop))).fits && !({ cube .plain with order := [1, 2, 2] } : Cube).fits
#guard !({ cube .plain with pairs := [(e 1, 0, 3)] } : Cube).fits
#guard chain (cube .plain) && chain (cube (.point rho))
-- THE TOTAL BY ITS DEFINITION, apart from weightsOf: plainly the bare sum over the corners; at a
-- point under the library's equality table
#guard (cube .plain).total ==
  (List.range 8).foldl (fun s i => addE s (termsAt (cube .plain).pairs (cube .plain).maps i)) zeroE
#guard (cube (.point rho)).total ==
  (List.range 8).foldl (fun s i => addE s (mulE ((OnBytes.Model.eqTab rho).getD i zeroE)
    (termsAt (cube .plain).pairs (cube .plain).maps i))) zeroE
-- the points come in the order of the rounds: variable 1 has the coordinate rho[1], 2 rho[0], 0
-- rho[2]
#guard (cube (.point rho)).points == [rho.getD 1 zeroE, rho.getD 0 zeroE, rho.getD 2 zeroE]
#guard (cube .plain).points == []
-- the challenges as a point; EACH MAP's VALUE IS ITS MULTILINEAR EXTENSION THERE, by the equality
-- table
#guard (cube .plain).pointOf rs == #[rs.getD 1 zeroE, rs.getD 0 zeroE, rs.getD 2 zeroE]
#guard (cube .plain).valuesAt rs ==
  #[tA, tB, tC].map fun t => mle t ((cube .plain).pointOf rs)
-- at a corner the value is the table's entry: the challenges 1, 1, 0 for the variables 1, 2, 0:
-- entry 6
#guard (cube .plain).valuesAt [oneE, oneE, zeroE] == #[tA, tB, tC].map (·.getD 6 zeroE)
-- in another order of the rounds the first round's polynomial is another. That the total is the
-- same holds of itself: `total` does not read the order: the first of these two lines cannot fail
#guard ({ cube (.point rho) with order := [2, 1, 0] } : Cube).total == (cube (.point rho)).total
#guard ({ cube (.point rho) with order := [2, 1, 0] } : Cube).round [] !=
  (cube (.point rho)).round []
-- IT CAN FAIL: one entry of a table raised by one: another total, and against the old total the
-- chain's first link breaks
#guard (cube .plain (tA.set! 5 (e 39))).total != (cube .plain).total
#guard sumBy none ((cube .plain (tA.set! 5 (e 39))).round []) != (cube .plain).total
-- behind the last round there is none
#guard (cube .plain).round rs == []

/-- A bilinear function of four end values. -/
def f₂ (l : List E) : E :=
  addE (mulE (l.getD 0 zeroE) (l.getD 1 zeroE))
    (mulE (e 3) (mulE (l.getD 2 zeroE) (l.getD 3 zeroE)))

def ends₄ : List E := [e 2, e 3, ⟨5, 1, 0⟩, e 7]
def masks₄ : List E := [e 11, ⟨13, 0, 4⟩, e 17, e 19]

-- THE POLYNOMIAL IN Y, WRITTEN OUT BY HAND: a b + 3 c d with each end value plus Y times its mask
-- entry
#guard polyInY 2 f₂ ends₄ masks₄ ==
  [f₂ ends₄,
    addE (addE (mulE (e 2) ⟨13, 0, 4⟩) (mulE (e 11) (e 3)))
      (mulE (e 3) (addE (mulE ⟨5, 1, 0⟩ (e 19)) (mulE (e 17) (e 7)))),
    f₂ masks₄]
-- at a fourth value of Y, which the interpolation did not use
#guard valueP (polyInY 2 f₂ ends₄ masks₄) (e 10) ==
  f₂ ((ends₄.zip masks₄).map fun y => addE y.1 (mulE (e 10) y.2))
-- of degree 1: two coefficients
#guard polyInY 1 (fun l => addE (mulE (e 4) (l.getD 0 zeroE)) (e 9)) [e 2] [e 5] == [e 17, e 20]
-- too low a degree stated: it does not fit at a further value
#guard valueP (polyInY 1 f₂ ends₄ masks₄) (e 10) !=
  f₂ ((ends₄.zip masks₄).map fun y => addE y.1 (mulE (e 10) y.2))
-- a mask entry too few, or one too many: the empty list
#guard polyInY 2 f₂ ends₄ (masks₄.take 3) == [] && polyInY 2 f₂ ends₄ (e 1 :: masks₄) == []

end CubeTest

end OnBytes.Desc.First.K4.Honest
