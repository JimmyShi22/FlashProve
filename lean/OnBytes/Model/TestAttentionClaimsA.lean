-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionClaimsA.lean: tests of OnBytes/Model/AttentionClaimsA.lean.

The tests run when this file is compiled. The program does not import this file.

Some tests use the small configuration that OnBytes/Model/TestAttentionTables.lean spells out
(exampleShape: 64 tokens in four tiles of 16, two heads of keys and values, 128 features a head). No
file of the repository is read; the examples under prover/examples may have other numbers.

The expected values of the key forms, of the padding's term and of the order of coordinates are
worked out by hand from the C++ source (verifier/src/vf_attention_check.h, AttentionSubProof::run,
claims 3 and 4 and the forms before them; verifier/src/vf_common.h, eqTab). The tables' first
entries and lengths are those that OnBytes/Model/TestAttentionTables.lean pins at the small
configuration. None of these values comes from a run of the C++ verifier.

What is tested: the key forms of the calls of kinds KR and KFD, with the padding's term; how a table
is read; whose key point a call takes; the order of a point's coordinates; which entries plane and
xl read. The sections below begin with their own accounts.

What is not tested: shV and the functions that call shV or xl. No claim is added here. callKFD is
run only on a record without a unit of scores, where it adds none. linPlanes, endValues, unitKFD,
callKR, claim3 and claim4 are not run. So neither the claims nor their order are seen.
OnBytes/Model/TestAttentionHonest.lean runs them, on the record of one honest proof. Of the four
keys of kind KFD that are computed here only the first is compared with a row of a table.
-/
import OnBytes.Model.AttentionClaimsA
import OnBytes.Model.TestAttentionTables

namespace OnBytes.Attention.TestClaimsA

open OnBytes.Model

/-- The value of a form that names no entry of a table, if slot first + i holds the number v[i]. -/
def valueAt (f : Aff) (first : Nat) (v : List Int) : E :=
  f.slots.foldl (fun s x => addE s (mulE x.2 (ofInt (v.getD (x.1 - first) 0)))) f.const

/-- One piece of weight 1. -/
def onePiece : Array PW := #[{ lam := 0, a := 0, wp := oneE }]

/-- Two pieces, of weights 2 and 3. -/
def twoPieces : Array PW :=
  #[{ lam := 0, a := 0, wp := ofNat 2 }, { lam := 0, a := 1, wp := ofNat 3 }]

#guard minusOne == ofInt (-1)
#guard limbWeights 4 == #[ofNat 1, ofNat 256, ofNat 65536, ofNat 16777216]

/-! ## Kind KR

This account is for this section and the next.
Tested: the key forms of the calls of kinds KR and KFD. A unit with one piece of weight 1 is
given whole numbers for the values that the prover sends. The key form must then be the key that the
lookup is meant to find in its table. For kind KR that is the row of the remainder r in the table
(rowKR). For kind KFD it is D - r + 2^32 fl + 2^33 e, with fl the flag, e the softmax weight, and D
the row maximum minus the score. On the empty tile slot below the diagonal D is C. Above the
diagonal Om is added to D. The values sent stand for cells of the matrix `as`: a remainder r has the
cells (r mod 256) - 128 and floor(r / 256) - 128, and a weight e has the cells (e mod 256) - 128 and
floor(e / 256). The first of the four keys of kind KFD is also compared with a row of a table
(rowKFD); the other three are not. For a unit with two pieces, of weights 2 and 3, the constant of
each key form is compared too: it holds the sum of the weights.
-/

/-- A unit of a call of kind KR whose values have the slots from 10 on. -/
def planeUnit : PlaneClaim :=
  { call := 0, seg := .rm, z := #[], isD := false, pw := onePiece, s0 := 10, np := 3 }

-- r = 135 * 256 + 133 is at least 2^4, so the flag is 1: the key is row r of the table
#guard valueAt (keyKR planeUnit) 10 [133 - 128, 135 - 128, 1] == ofNat (rowKR 4 (135 * 256 + 133))
-- r = 9 is below 2^4, so the flag is 0
#guard valueAt (keyKR planeUnit) 10 [9 - 128, 0 - 128, 0] == ofNat (rowKR 4 9)
-- two pieces: the constant holds the sum 5 of their weights
#guard (keyKR { planeUnit with pw := twoPieces }).const == ofNat (128 * 5 + 2 ^ 20 * 128 * 5)

/-! ## Kind KFD -/

/-- The numbers C = 4096 and Om = 70000 of a shift. -/
def someShift : ShD := { C := 4096, Om := 70000 }

/-- A unit of a call of kind KFD whose values have the slots from 20 on. -/
def scoreUnit (seg : Seg) (zs zi zj : Array E) : Score :=
  { call := 0, claim := 0, seg := seg, pw := onePiece, zg := #[], zs := zs, zi := zi, zj := zj,
    wI := #[], s0 := 20, sc := {} }

/-- The cells of r = 300, fl = 0 and e = 1000, then the maximum 5000 and the score 3100. -/
def someCells : List Int := [44 - 128, 1 - 128, 0, 232 - 128, 3, 5000, 3100]

-- below the diagonal, a tile slot that is not the empty one: m - s - r + 2^32 fl + 2^33 e
#guard valueAt (keyKFD someShift (scoreUnit .fm #[zeroE, oneE] #[] #[])) 20 someCells ==
  ofNat (5000 - 3100 - 300 + 2 ^ 33 * 1000)
-- that key is row 25 of the table for the shift 6, if entry 25 of the exponentials is 1000
#guard rowKFD (Array.replicate 26 1000) someShift 6 25 == 5000 - 3100 - 300 + 2 ^ 33 * 1000
-- below the diagonal, the empty tile slot; maximum, score and e are given as 0: C - r + 2^32 fl
#guard valueAt (keyKFD someShift (scoreUnit .fm #[oneE, oneE] #[] #[])) 20
    [44 - 128, 1 - 128, 1, 0 - 128, 0, 0, 0] == ofNat (4096 - 300 + 2 ^ 32)
-- on the diagonal, column 1 at most row 2: no term Om
#guard valueAt (keyKFD someShift (scoreUnit .fd #[] #[oneE, zeroE] #[zeroE, oneE])) 20 someCells ==
  ofNat (5000 - 3100 - 300 + 2 ^ 33 * 1000)
-- on the diagonal, column 2 above row 1: the term Om
#guard valueAt (keyKFD someShift (scoreUnit .fd #[] #[zeroE, oneE] #[oneE, zeroE])) 20 someCells ==
  ofNat (5000 - 3100 + 70000 - 300 + 2 ^ 33 * 1000)

-- two pieces, the empty tile slot: C LW - 128 LW - 256 * 128 LW + 2^33 * 128 LW with LW = 5
#guard (keyKFD someShift { scoreUnit .fm #[oneE, oneE] #[] #[] with pw := twoPieces }).const ==
  ofNat (4096 * 5 + 2 ^ 33 * 128 * 5 - 128 * 5 - 256 * 128 * 5)

/-! ## The padding's term

For a call of four keys, one of them padding: the sum of the pieces' weights (wall) and the
constant of the padding's term (padTerm), at corners of the cube.
-/

/-- A call with four keys: a piece of two keys, a piece of one key, and one padding key. Row 1 of
its table has the value 77. -/
def someCall : ACall :=
  { call := { n := 2, t0 := 1, tau := some #[5, 77] },
    pcs := #[{ b := 1, off := 0 }, { b := 0, off := 2 }] }

-- at the points of the cube the pieces' weights add up to 1 on a piece and to 0 on the padding
#guard wall someCall #[zeroE, oneE] == oneE
#guard wall someCall #[oneE, zeroE] == oneE
#guard wall someCall #[oneE, oneE] == zeroE
#guard (padTerm someCall #[oneE, oneE]).const == ofNat 77
#guard (padTerm someCall #[zeroE, zeroE]).const == zeroE

/-! ## Reading a table

u3at gives the entry of the array of tables that it is asked for, with the coefficient
1. It refuses, under the name internal-a-table-index, the index at a table's end and a first entry
at which no table begins. Two tables are tried, the first and the last of the small configuration.
-/

/-- The small configuration's records with all its tables, which take 34,152 entries. -/
def exampleHeard : Option Heard :=
  (TestTables.exampleTables 34152).map fun t =>
    { S := TestTables.exampleShape, g := TestTables.exampleLook, planes := #[], scores := #[],
      d := TestTables.exampleDivide, x := TestTables.exampleAttain, t := t, iU3 := 0 }

/-- The entries of the array of tables that a form reads with a coefficient other than 0. -/
def entriesOf (f : Aff) : List (Nat × E) :=
  (f.ents.toList.filter fun e => !isZeroE e.coef).map fun e => (e.idx, e.coef)

/-- What u3at does for entry i of the table that begins at t: the name under which it refuses, or no
name and the entries that its form reads. The array of the tables is array number 0 and has one row
of 34,152 columns. -/
def reads (t i : Nat) : Option (Option String × List (Nat × E)) :=
  exampleHeard.map fun h =>
    match ((u3at h t i).run' { trees := #[{ R := 1, K := 34152 }] }).runNamed
        { entries := [], st := {} } false [] [] with
    | .ok x => (none, entriesOf x.1)
    | .error e => (some e.name, [])

-- the first table begins at entry 0 and has 120 entries
#guard reads 0 0 == some (none, [(0, oneE)])
#guard reads 0 119 == some (none, [(119, oneE)])
#guard reads 0 120 == some (some "internal-a-table-index", [])
-- no table begins at entry 1
#guard reads 1 0 == some (some "internal-a-table-index", [])
-- the last table begins at entry 33,128 and has 1,024 entries
#guard reads 33128 1023 == some (none, [(34151, oneE)])
#guard reads 33128 1024 == some (some "internal-a-table-index", [])

/-! ## Whose key point

callKFD takes the padding's term at the key point of its own call. With the calls of
smallCfg in OnBytes/Model/TestAttentionPlan.lean, which have 2^20 keys each with their padding, all
calls have the same key point. So two different points are given here.
-/

/-- The records of exampleHeard with the key point (0, 0) for call 0 and (1, 1) for call 1. There is
no unit of scores, so the key form that callKFD returns is the padding's term. -/
def twoPoints : Option Heard :=
  exampleHeard.map fun h => { h with g := { h.g with zk := #[#[zeroE, zeroE], #[oneE, oneE]] } }

/-- The constant of the key form that callKFD returns for someCall as call number q. -/
def padOf (q : Nat) : Option E := do
  let h ← twoPoints
  (Blk.runFrom ((callKFD h q someCall).run' {}) { entries := [], st := {} } false [] []).map
    (·.1.const)

-- as above: the term is 0 at (0, 0), a key of a piece, and 77 at (1, 1), the padding key
#guard padOf 0 == some zeroE
#guard padOf 1 == some (ofNat 77)

/-! ## The order of a point's coordinates

This account is for this section and the next.
Tested: which coordinate of a point belongs to which bit of an index, in overG and in plane. At
the small configuration each of the two reads at most one coordinate, so a shape is taken at which
each reads two. At that shape the entries that plane and xl read are compared for one plane and one
tensor, with a layer, a head and a pair other than the first, below the diagonal and on it; and xl
refuses, under the name plan-tensor-layout, a point that is too short and a head that is not there.
-/

/-- The records of exampleHeard at another shape: four heads of keys and values, two layers, two
query heads for each head of keys and values, heads of 128 features, and for a plane of one pair
2^13 places below the diagonal and 2^12 on it. An entry of a table on `as` stands for 2^11 places,
so such a plane has four entries below the diagonal and two on it. -/
def wideHeard : Option Heard :=
  exampleHeard.map fun h =>
    { h with S := { h.S with G := 4, Lam := 2, HA := 2, dh := 128, nM := 13, nD := 12,
                             cf := { h.S.cf with lgk := 2 } } }

/-- The form that x makes at the shape of wideHeard; none if x refuses. -/
def formOf (x : Heard → SubM Aff) : Option Aff := do
  let h ← wideHeard
  (Blk.runFrom ((x h).run' { trees := #[{ R := 1, K := 34152 }] })
    { entries := [], st := {} } false [] []).map (·.1)

/-- The sum over the heads g of keys and values of eq(zg, g) (g + 1). -/
def headAt (zg : Array E) : Option E :=
  (formOf fun h => overG h zg fun g => pure (Aff.ofConst (ofNat (g + 1)))).map (·.const)

/-- The entries that plane 0 of the pair (0, 0) reads at a point that begins with z. -/
def planeAt (z : Array E) : Option (List (Nat × E)) :=
  (formOf fun h => plane h 0 0 0 0 (z ++ Array.replicate 11 zeroE) false).map entriesOf

-- The first coordinate belongs to the top bit: the point (1, 0) is the index 2, and (0, 1) is 1.
#guard headAt #[oneE, zeroE] == some (ofNat 3)
#guard headAt #[zeroE, oneE] == some (ofNat 2)
#guard planeAt #[oneE, zeroE] == some [(2, oneE)]
#guard planeAt #[zeroE, oneE] == some [(1, oneE)]

/-! ## Which entries plane and xl read -/

/-- What x does at the shape of wideHeard: the name under which it refuses, or no name and the
entries that its form reads. -/
def doneAt (x : Heard → SubM Aff) : Option (Option String × List (Nat × E)) :=
  wideHeard.map fun h =>
    match ((x h).run' { trees := #[{ R := 1, K := 34152 }] }).runNamed
        { entries := [], st := {} } false [] [] with
    | .ok y => (none, entriesOf y.1)
    | .error e => (some e.name, [])

-- Plane 1 of the pair (1, 1) is number (1 * 2 + 1) * 2 + 1 = 7 among the planes of all pairs. Below
-- the diagonal it begins at entry 7 * 4 = 28, and the point (1, 0) is its entry 2.
#guard doneAt (fun h => plane h 0 1 1 1 (#[oneE, zeroE] ++ Array.replicate 11 zeroE) false) ==
  some (none, [(30, oneE)])
-- The five planes of the four pairs take 5 * 4 * 4 = 80 entries below the diagonal. On the diagonal
-- the plane begins at entry 80 + 7 * 2 = 94, and the point (1) is its entry 1.
#guard doneAt (fun h => plane h 0 1 1 1 (#[oneE] ++ Array.replicate 11 zeroE) true) ==
  some (none, [(95, oneE)])

/-- A tensor of two limbs, two layers and two heads of 128 features, from feature 0 on. -/
def twoHeads : TenAt := ⟨0, 2, 2, 256⟩

-- The table that begins at entry 3,432 has one entry for each block of four features. For layer 1
-- and head 1, limb 0 begins at feature 384, in block 96, and limb 1 at feature 896, in block 224.
-- The point's first five coordinates, (1, 0, 0, 0, 0), are block 16 of the head's 32.
#guard doneAt (fun h => xl h 3432 twoHeads 1 1 (#[oneE] ++ Array.replicate 6 zeroE)) ==
  some (none, [(3432 + 96 + 16, oneE), (3432 + 224 + 16, ofNat 256)])
-- a point of one coordinate, of which two should be cut off; a head that the tensor does not have
#guard doneAt (fun h => xl h 3432 twoHeads 1 1 #[oneE]) == some (some "plan-tensor-layout", [])
#guard doneAt (fun h => xl h 3432 twoHeads 1 2 (Array.replicate 7 zeroE)) ==
  some (some "plan-tensor-layout", [])

end OnBytes.Attention.TestClaimsA
