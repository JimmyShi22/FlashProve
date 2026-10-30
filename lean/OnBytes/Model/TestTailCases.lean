-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestTailCases.lean: the smallness test in cases that the small configuration of
OnBytes/Model/TestTailSmall.lean does not have.

That configuration has tau = 128, so one block, and one tree for each call of the digits' lookup.
Every kind of sub-proof has U3 alone of U1 to U3. And only by chance is a challenge 0 or 1, or one
whose powers repeat early. This file runs the functions of OnBytes/Model/Tail.lean in such cases:
several blocks, several trees a call, a vector U1, weights of the reads that differ from those of
the ties, several matrices and tables, and the small example of OnBytes/Model/TestTailRun.lean with
a challenge fixed to 0 or 1. No proof is read, and nothing is said about a prover. Forest.pad does
not run here: what the lookup would have received and drawn is written by hand. The calls' points
are not compared with what Forest.pad makes, since Forest.pad has no function of its own for them.
The expected numbers were worked out by hand from piecesF, placeZ, Forest.shape and Forest.pubRun,
and in the last section from the rule in the C++ comment on the reads' weights
(verifier/src/vf_smallness_test_members.inc, tileSelfTestF).

The terms are explained in OnBytes/Model/Tail.lean (the docstring of HTailF2 says where). The file
is not imported by the program.
-/
import OnBytes.Model.TestTailHeld

namespace OnBytes.Model.TestTailCases

open OnBytes OnBytes.Model OnBytes.Model.TestTailRun OnBytes.Model.TestTailHeld

/-! ## Blocks -/

-- One block for each bit of the number that is 1.
#guard (t2BL 1).toOption == some #[(0, 1)]
#guard (t2BL 2).toOption == some #[(0, 2)]
#guard (t2BL 3).toOption == some #[(0, 2), (2, 1)]
#guard (t2BL 6).toOption == some #[(0, 4), (4, 2)]
#guard (t2BL 7).toOption == some #[(0, 4), (4, 2), (6, 1)]
#guard (t2BL 15).toOption == some #[(0, 8), (8, 4), (12, 2), (14, 1)]

/-! ## Padding keys with several trees a call -/

/-- The numbers of padding keys of the trees, for one matrix of m rows of cells and one column. -/
def padding (tau lidb m : Nat) : Option (Array Nat) :=
  ((({ tau := tau, lidb := lidb } : HTailF2).shape #[{ name := "x", m := m, k := 1 }] #[none] #[]
    #[false, false, true, false] tau).toOption).map fun tl => tl.f9.pub

-- CP = 512, one piece of 2^11 places, two trees a call: 212 padding places in each of four rows,
-- two rows a tree.
#guard padding 4 10 300 == some #[424, 424, 424, 424]
-- Pieces of 2^11 and 2^10 places, four trees a call, of which the last is all padding.
#guard padding 6 10 300 == some #[424, 424, 424, 1024, 424, 424, 424, 1024]
-- tau = 160 and lidb = 22, the defaults of HTailF2: CP = 32768, n = 23, two trees a call.
#guard padding 160 22 30720 == some #[262144, 3211264, 262144, 3211264]

/-! ## The sums over the drawn matrix where the two vectors of weights differ -/

/-- A made-up state: powersF, the only writer of vt and vp, makes them equal. -/
def twoWeights : HTailF2 where
  tau := 2
  NM := 1
  mats := #[{ name := "x", m := 1, k := 1 }]
  cfFirst := #[0, 1]
  cfF := #[1, 1]
  vt := #[oneE, oneE]
  vp := #[oneE, zeroE]
  gamX := #[#[]]
  gamV := #[#[]]

#guard (twoWeights.foldSums 0).any fun tl => tl.gamX == #[#[ofNat 1]] && tl.gamV == #[#[ofNat 2]]

/-! ## The powers of the second computation at the edges of its tables -/

#guard HTailF2.powersAgain (ofNat 2) 3 1 == #[ofNat 1]
#guard (HTailF2.powersAgain (ofNat 3) 2 129).getD 128 zeroE == powE (ofNat 3) 256
#guard (HTailF2.powersAgain (ofNat 3) 2 130).getD 129 zeroE == powE (ofNat 3) 258

/-! ## The second computation's own helpers -/

-- The least power of two that is not below x, at and beside powers of two, and at its limit.
#guard [0, 1, 2, 3, 4, 5, 127, 128, 129, 160].map HTailF2.pow2Again ==
  [1, 1, 2, 4, 4, 8, 128, 128, 256, 256]
#guard HTailF2.pow2Again (2 ^ 64 - 1) == 2 ^ 64 && HTailF2.pow2Again (2 ^ 64) == 2 ^ 64 &&
  HTailF2.pow2Again (2 ^ 64 + 1) == 2 ^ 64
-- The second column of a matrix of two columns of three entries, (1, 0, -1), under the weights
-- 2, 3, 5: 2 - 5. Then from the second entry on, added to 10: 10 - 5.
#guard HTailF2.sumAgain #[1, 1, 1, 1, 0, -1] 3 #[ofNat 2, ofNat 3, ofNat 5] 3 0 zeroE ==
  subE (ofNat 2) (ofNat 5)
#guard HTailF2.sumAgain #[1, 1, 1, 1, 0, -1] 3 #[ofNat 2, ofNat 3, ofNat 5] 2 1 (ofNat 10) ==
  ofNat 5
-- It agrees with foldColumn on entries -1, 0, 1. At another entry foldColumn goes by the sign.
#guard HTailF2.foldColumn #[1, 1, 1, 1, 0, -1] 3 3 #[ofNat 2, ofNat 3, ofNat 5] ==
  subE (ofNat 2) (ofNat 5)
#guard HTailF2.sumAgain #[2] 0 #[ofNat 7] 1 0 zeroE == zeroE &&
  HTailF2.foldColumn #[2] 0 1 #[ofNat 7] == ofNat 7
-- An entry after the end of the matrix adds nothing.
#guard HTailF2.sumAgain #[1] 0 #[ofNat 2, ofNat 3] 2 0 zeroE == ofNat 2

/-! ## A sub-proof with U1 -/

/-- The example's list of arrays, with a vector U1 of one entry before U3. No kind of sub-proof asks
for that. -/
def plannedU1 : Except String (HTailF2 × Fork) := do
  let tl ← ({} : HTailF2).shape #[{ name := "x", m := 6, k := 2 }] #[none] #[]
    #[true, false, true, false] 160
  let (tl, F, _) ← tl.addTrees {} {} #[1, 0, 4] #[] 100 128
  pure (tl, F)

-- coefficientsF gives the one row of U1, and of U3, the weight 1.
#guard plannedU1.toOption.any fun (tl, F) =>
  (((afterMessages tl).coefficientsF (afterDraw tl F)).outcome (noRounds false)).any fun x =>
    let G : Fork := x.1.2
    [0, 1].all fun t =>
      let row := (G.trees.getD t {}).rows.getD 0 {}
      row.coef == #[oneE] && row.rowForm && row.rowOnes

/-! ## Two trees a call, through all claims and all tests on the weights -/

/-- The example's list of arrays, with trees of 2^10 places: each call of 2^11 keys has two. -/
def planned10 : Except String (HTailF2 × Fork) := do
  let tl ← ({ lidb := 10 } : HTailF2).shape #[{ name := "x", m := 6, k := 2 }] #[none] #[]
    #[false, false, true, false] 160
  let (tl, F, _) ← tl.addTrees {} {} #[0, 0, 4] #[] 100 128
  pure (tl, F)

/-- What the lookup would have received and drawn: two coordinates for the tree's index, ten for the
place in a tree. The point of each call is (zy_1 | zx). -/
def heard10 (tl : HTailF2) : Forest.Heard :=
  let zy := els false 100 2
  let zx := els false 200 10
  { heard false tl with
    zx := zx, zy := zy, e := #[subE oneE (zy.getD 0 zeroE), zy.getD 0 zeroE],
    zk := #[zy.extract 1 2 ++ zx, zy.extract 1 2 ++ zx] }

/-- Adds the claims. -/
def claimsAdded10 : Option (HTailF2 × Fork) :=
  match planned10 with
  | .error _ => none
  | .ok (tl0, F) =>
    let course : SubM HTailF2 := do
      let tl ← ({ afterMessages tl0 with heard := some (heard10 tl0) } : HTailF2).objectsF
        (funs false)
      SubM.must ((← SubM.claims) == tl0.lins 2 && tl.foldAllTakenF)
      pure tl
    ((course (afterDraw tl0 F)).outcome (noRounds false)).map (·.1)

#guard planned10.toOption.any fun (tl, _) =>
  tl.f9.dT == 10 && tl.f9.iota == #[1, 1] && tl.f9.first == #[0, 2] && tl.f9.NT == 4 &&
    tl.f9.rK == 2 && tl.f9.pub == #[256, 832, 256, 832]
-- The calls' weights that heard10 writes by hand are those that the lookup's own function gives:
-- call 0, with the trees 0 and 1, has 1 - zy_0; call 1, with the trees 2 and 3, has zy_0.
#guard planned10.toOption.any fun (tl, _) =>
  (heard10 tl).e == (Array.range 2).map (Forest.callWeight tl.f9 (heard10 tl).zy)
-- The claims are added, and all tests on the weights pass.
#guard claimsAdded10.any fun (tl, F) => testsPass false tl F

/-! ## Challenges that are 0 or 1 -/

/-- The example start (planned or planned3) after all claims are added and the weights on the rows
are set, with what the lookup has drawn changed by onHeard and with the batching element theta. The
changes are made before any weight is computed, so both computations of the weights agree, and only
a condition "is not 0" or "differ" can fail. -/
def readyWith (start : Except String (HTailF2 × Fork)) (onHeard : Forest.Heard → Forest.Heard)
    (theta : E) : Option Both :=
  match start with
  | .error _ => none
  | .ok (tl0, F) =>
    let tl1 := afterMessages tl0
    let course : SubM HTailF2 := do
      let tl ← ({ tl1 with heard := tl1.heard.map onHeard } : HTailF2).objectsF (funs false)
      tl.coefficientsF
      pure tl
    ((course { afterDraw tl0 F with theta := theta }).outcome (noRounds false)).map
      fun x => { tl := x.1.1, F := x.1.2 }

/-- Sets coordinate i of both calls' point to v. -/
def zxSet (i : Nat) (v : E) (g : Forest.Heard) : Forest.Heard :=
  let zx := g.zx.set! i v
  { g with zx := zx, zk := #[zx, zx] }

-- Unchanged, both parts hold.
#guard (readyWith planned id (el false 9)).any fun s => piecesWeighed s && tieWeighed s
-- Coordinate 5 belongs to the rows of all four pieces. Set to 0, it gives every row whose bit is 1
-- the weight 0. The second computation expects that weight too; the test must fail all the same.
#guard (readyWith planned (zxSet 5 zeroE) (el false 9)).any fun s => !piecesWeighed s
-- Coordinate 10 is the lowest bit of the column. At 0 every odd column has the weight 0.
#guard (readyWith planned (zxSet 10 zeroE) (el false 9)).any fun s => !piecesWeighed s
-- Under the batching element 1 the two rows of symbols have one weight. The sums of the two fixed
-- columns of the drawn matrix are 2 and -2, so no read's weight is 0.
#guard (readyWith planned id oneE).any fun s => !tieWeighed s
-- The test of the reads' weights has no condition "is not 0" or "differ": it holds under the
-- example's batching element, under 1 and under 0.
#guard [el false 9, oneE, zeroE].all fun theta => (readyWith planned id theta).any readWeighed

/-- The column weights of ZZ's four rows of digits. -/
def digitWeights (s : Both) : List (Array E) :=
  [0, 1, 2, 3].map fun r => HTailF2.weightsOf s.F s.tl.ix.ZZ r

-- A made-up state: each call's point has one coordinate too many. The claim on the key vectors
-- takes a piece's coordinates by their places, so the weights on ZZ's rows of digits stay.
#guard (readyWith planned id (el false 9)).any fun s =>
  (readyWith planned (fun g => { g with zk := g.zk.map (·.push (el false 77)) }) (el false 9)).any
    fun t => digitWeights t == digitWeights s && (digitWeights s).all fun L => L.size == 12

/-- An example with one row of symbols: three rows of cells, two columns, one table of one segment.
Each call has 2^10 keys. -/
def planned3 : Except String (HTailF2 × Fork) := do
  let tl ← ({} : HTailF2).shape #[{ name := "x", m := 3, k := 2 }] #[none] #[]
    #[false, false, true, false] 160
  let (tl, F, _) ← tl.addTrees {} {} #[0, 0, 2] #[] 100 128
  pure (tl, F)

/-- Gives both calls a point of ten coordinates. -/
def ten (g : Forest.Heard) : Forest.Heard :=
  let zx := els false 200 10
  { g with zx := zx, zk := #[zx, zx] }

-- The tie's weights hold under the example's batching element.
#guard (readyWith planned3 ten (el false 9)).any tieWeighed
-- Under the batching element 0 the one row weight is 1, and every expected weight of a digit is 0,
-- as is the weight that the claims have set.
#guard (readyWith planned3 ten zeroE).any fun s => !tieWeighed s
-- One read, of a table with one segment.
#guard (readyWith planned3 ten (el false 9)).any readWeighed

/- ## The reads' weights with two matrices and four tables -/

/-- A made-up state for readWeightsAgain alone: tau = 2; two matrices, of two and of three rows of
cells; on each a table in U1 and one in U3, listed in another order than the reads'. -/
def fourTables : HTailF2 :=
  { tau := 2, NM := 2, mz := 5, nX4Laid := 7,
    mats := #[{ name := "x", m := 2, k := 1 }, { name := "y", m := 3, k := 1 }],
    funs := #[{ mat := 1, len := 3, phi := els false 10 3, tree := 2 },
      { mat := 0, len := 1, phi := els false 20 1, tree := 2 },
      { mat := 0, len := 2, phi := els false 30 2, tree := 0 },
      { mat := 1, len := 1, phi := els false 40 1, tree := 0 }] }

-- Worked out by hand. Np = 2. Each matrix has one row of symbols, so the ties' equations take the
-- indices 0 to 3, and with five claims in the plan the first read stands under theta^9. The reads'
-- order: matrix 0, U1 (one read, q = 0), U3 (q = 1, 2); matrix 1, U1 (q = 3, 4, 5), U3 (q = 6).
#guard
  let theta := el false 9
  let w := fourTables.readWeightsAgain { theta := theta, planClaimsF := 5 }
  let p (n k : Nat) : E := mulE (powE theta n) (el false k)
  let low := #[addE (p 9 30) (p 11 20), addE (p 9 31) (p 13 20),
    addE (p 15 40) (p 21 10), addE (p 17 40) (p 21 11), addE (p 19 40) (p 21 12)]
  w == low ++ low.map (scaleNat · 1024) && fourTables.readShapeHeld w

/-- A made-up state for readWeightsAgain alone: tau = 2; one matrix of seven rows of cells; one
table of one segment. -/
def sevenRows : HTailF2 :=
  { tau := 2, NM := 1, mz := 7, nX4Laid := 1, mats := #[{ name := "x", m := 7, k := 1 }],
    funs := #[{ mat := 0, len := 7, phi := els false 50 7, tree := 2 }] }

-- Seven rows of cells are three rows of symbols, which take the room of four: with Np = 2 the tie's
-- equations have the indices 0 to 7, and without a claim in the plan the read stands under theta^8.
#guard
  let theta := el false 9
  let w := sevenRows.readWeightsAgain { theta := theta, planClaimsF := 0 }
  sevenRows.readShapeHeld w && (List.range 7).all fun j =>
    w.getD j zeroE == mulE (powE theta 8) (el false (50 + j))

end OnBytes.Model.TestTailCases
