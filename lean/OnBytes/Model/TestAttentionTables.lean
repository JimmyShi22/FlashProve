-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionTables.lean: tests of OnBytes/Model/AttentionTables.lean.

The tests run when this file is compiled. The program does not import this file.

What is tested.
 - At small shapes, against values computed by hand: when a table's length fits its matrix; where
   tables are placed and which lengths are stored; the order of the entries of token weights; the
   sums of the tile slots' weights by tile row and by tile column (tileSums of
   OnBytes/Model/AttentionHeard.lean, which the tables call).
 - At a small configuration, spelled out here (exampleShape: 64 tokens in 4 tiles of 16, 2 heads of
   keys and values, 128 features a head), with 0 for every value: each table's first entry, that
   the tables fill the array of 34,152 entries, that each weight vector has the length of its block,
   and that the dry run places the same tables with zeros as weights.
 - With altered points and token weights: that the two tests of agreement and the test in lng
   refuse, and under which name each test of the file refuses.
A run on a view is the ordinary run, on values read from a proof. The dry run takes zeros for all
values (OnBytes/Iop/Ground.lean).

Where the numbers come from. The small configuration's sizes and matrices are written out by hand.
Guards compare them, and 34,152, with what shapeHid and matrices give for smallCfg
(OnBytes/Model/TestAttentionPlan.lean), which is itself written out by hand with the same numbers. A
guard compares each table's matrix, block length, first entry and number of weights with what the
C++ verifier printed at this configuration (OnBytes/Model/TestAttentionHonestData.lean, whose head
says how the print was made). No file of the repository is read; the examples under prover/examples
may have other numbers.
-/
import OnBytes.Model.AttentionTables
import OnBytes.Model.TestAttentionPlan
import OnBytes.Model.TestAttentionHonestData

namespace OnBytes.Attention.TestTables

/-- Small numbers as elements of the extension field. -/
def small (l : List UInt64) : Array E := (l.map ofF).toArray

/-- Runs an action that places tables, from no table, outside any chain. Returns its value, the
first free entry and the lengths stored; none if it refuses, under whatever name. -/
def ran {α : Type} (a : PlaceM α) : Option (α × Nat × List (Nat × Nat)) :=
  (Blk.runFrom (a {}) { entries := [], st := {} } false [] []).map fun r =>
    (r.1.1, r.1.2.next, r.1.2.tabLen)

/-! ## The length of a table -/

/-- One matrix of 8 rows and 3 columns. -/
def one : Array Model.TMat := #[{ m := 8, k := 3 }]

-- blocks of 4 rows: 2 blocks in each of 3 columns
#guard fits one 0 4 6
#guard !fits one 0 4 5
#guard !fits one 0 4 7
-- a block is a whole column
#guard fits one 0 8 3
-- 3 does not divide 8; 0 is no block length; there is no matrix number 1
#guard !fits one 0 3 6
#guard !fits one 0 0 0
#guard !fits one 1 4 6
-- blocks of one row fit; 0 is no block length for a matrix of no rows either
#guard fits one 0 1 24
#guard !fits #[{ m := 0, k := 3 }] 0 0 0

/-! ## Where tables are placed -/

#guard ran (add one 0 4 #[] 6) == some (0, 6, [(0, 6)])
#guard ran (add one 0 4 #[] 5) == none
#guard ran (do let _ ← add one 0 4 #[] 6; add one 0 8 #[] 3) == some (6, 9, [(6, 3), (0, 6)])

/-- The matrix `as` in two parts of 4 rows and 3 columns each. -/
def twoParts : Shape := { cf := { NAs := 2, lmS := 2 }, kAs := 6 }

/-- The two parts. -/
def parts : Array Model.TMat := #[{ m := 4, k := 3 }, { m := 4, k := 3 }]

-- Each part's table is stored under its first entry. The newest pair for the first part's first
-- entry holds the length of both.
#guard ran (addAs twoParts parts fun _ => #[]) == some (0, 6, [(0, 6), (3, 3), (0, 3)])
#guard ran (do let _ ← addAs twoParts parts fun _ => #[]; addAs twoParts parts fun _ => #[]) ==
  some (6, 12, [(6, 6), (9, 3), (6, 3), (0, 6), (3, 3), (0, 3)])

/-! ## Weights -/

#guard lastCoords (small [1, 2, 3, 4]) 2 == small [3, 4]
#guard lastCoords (small [1, 2, 3, 4]) 0 == #[]

-- Two tiles of two tokens. At the point 1 the equality weights are 0 and 1.
#guard tok { T := 4, B := 2 } (small [5, 7]) (small [1]) == small [0, 5, 0, 7]
-- At the point 2 they are -1 and 2.
#guard tok { T := 4, B := 2 } (small [5, 7]) (small [2]) ==
  #[negE (ofF 5), ofF 10, negE (ofF 7), ofF 14]

/-- A shape of which only the numbers of tiles are set: four along a side. The six tiles below the
diagonal are in two slot rows. Slot row 0 holds the tiles (3, 0), (3, 1), (3, 2), and slot row 1
the tiles (1, 0), (2, 0), (2, 1), each written (tile row, tile column). -/
def four : Shape := { nT := 4, hP := 2 }

-- The tile slots' weights are 1, 2, 3 in slot row 0 and 10, 20, 30 in slot row 1. The last tile
-- slot's weight, 100, is not read.
#guard tileSums four (small [1, 10]) (small [1, 2, 3, 100]) ==
  (small [0, 10, 50, 6], small [31, 32, 3, 0])

/-! ## All tables at the small configuration -/

/-- n zeros. -/
def zeros (n : Nat) : Array E := Array.replicate n zeroE

/-- The small configuration's sizes: 64 tokens in 4 tiles of 16, 2 heads of keys and values, 128
features a head. Only what the tables read is set. -/
def exampleShape : Shape :=
  { cf := { lt := 6, lB := 4, lgk := 1, ldh := 7, lmS := 11, la := 8, lmb := 13, NAs := 1 },
    T := 64, B := 16, nT := 4, hP := 2, lnT := 2, ls := 2,
    kAs := 120, kbA := 1024, fillH := 256, fillO := 4096, fillQ := 12288 }

/-- The small configuration's matrices: `as` in one part, then ah, ao, bA and qa. Their sizes follow
from exampleShape by the rule of the function matrices of OnBytes/Model/AttentionPlan.lean. -/
def exampleMats : Array Model.TMat :=
  #[{ m := 2048, k := 120 }, { m := 4096, k := 4 }, { m := 8192, k := 32 },
    { m := 8192, k := 1024 }, { m := 8192, k := 96 }]

/-- The numbers of a shape that the tables read. -/
def readOf (S : Shape) : List Nat :=
  [S.cf.lt, S.cf.lB, S.cf.lgk, S.cf.ldh, S.cf.lmS, S.cf.la, S.cf.lmb, S.cf.NAs, S.T, S.B, S.nT,
   S.hP, S.lnT, S.ls, S.kAs, S.kbA, S.fillH, S.fillO, S.fillQ]

-- The sizes and matrices written out above are those that shapeHid and matrices give for smallCfg.
#guard ((shapeHid 24 smallCfg).toOption.map fun x => (readOf x.1, x.1.tableElems)) ==
  some (readOf exampleShape, 34152)
#guard ((shapeHid 24 smallCfg).toOption.map fun x => (matrices x.1 {}).map fun M => (M.m, M.k)) ==
  some (exampleMats.map fun M => (M.m, M.k))

/-- What the lookup stores, as far as the tables read it: points of the small configuration's
lengths. -/
def exampleLook : Model.Forest.Heard :=
  { shape := { dT := 20, kT := 16, cK := 2, NC := 4 }, leaves := default,
    zx := zeros 20, zb0 := zeros 23, zb1 := zeros 23 }

#guard ((shapeHid 24 smallCfg).toOption.map fun x => (x.2.dT, x.2.kT, x.2.cK, x.2.NC)) ==
  some (exampleLook.shape.dT, exampleLook.shape.kT, exampleLook.shape.cK, exampleLook.shape.NC)

/-- A plane claim at a point of n coordinates. -/
def examplePlane (s : Seg) (n : Nat) : PlaneClaim :=
  { call := 0, seg := s, z := zeros n, isD := false, pw := #[], s0 := 0, np := 0 }

/-- A unit of kind KFD whose sumcheck has n variables. -/
def exampleScore (s : Seg) (n : Nat) : Score :=
  { call := 0, claim := 0, seg := s, pw := #[], zg := zeros 1, zi := zeros 4, zj := zeros 4,
    wI := zeros 4, s0 := 0, sc := { r := zeros n } }

/-- The division and the value product, with points of the small configuration's lengths. -/
def exampleDivide : Divide :=
  { pwW := #[], pwX := #[], pwH := #[], qWH := 0, zsl := zeroE,
    zgW := zeros 1, ziW := zeros 6, zcW := zeros 7, zgX := zeros 1, ziX := zeros 6,
    zgH := zeros 1, ziH := zeros 6, zcH := zeros 7, s5 := 0, sIB := 0, s5h := 0,
    scE := { r := zeros 7 }, gam := zeroE, sCl := 0, vpm := { r := zeros 8 }, wJv := zeros 4,
    vpd := { r := zeros 7 } }

/-- The maximum and the index's bits, with points of the small configuration's lengths. -/
def exampleAttain : Attain :=
  { tg := zeros 1, ti := zeros 6, sM6 := 0, scF := { r := zeros 14 }, scd := { r := zeros 13 },
    scH := { r := zeros 11 } }

/-- All tables of the small configuration for an array of nW entries, on a view or in the dry run;
none if tables refuses. -/
def exampleTables (nW : Nat) (dry : Bool := false) : Option Tables :=
  (Blk.runFrom
    (tables exampleShape exampleMats nW exampleLook
      #[examplePlane .rm 12, examplePlane .rd 11, examplePlane .fm 12, examplePlane .fd 11]
      #[exampleScore .fm 11, exampleScore .fd 10] exampleDivide exampleAttain)
    { entries := [], st := {} } dry [] []).map (·.1)

/-- The tables' first entries, in the tables' order. -/
def starts (t : Tables) : List Nat :=
  [t.tA, t.tVM, t.tVD] ++ t.score.toList.map (·.tM) ++ [t.hW, t.hX, t.hE, t.hT, t.hPi, t.hR2, t.tO]
    ++ t.score.toList.flatMap (fun s => [s.tQ, s.tK])
    ++ [t.qO, t.qVM, t.qVD, t.qF, t.qKx, t.tBit0, t.tBit1, t.tPin]

-- 3 tables of 120 entries, 8 of 256, 1 of 1024, 9 of 3072, 3 of 1024
#guard (exampleTables 34152).map starts == some
  [0, 120, 240, 360, 616, 872, 1128, 1384, 1640, 1896, 2152, 2408,
   3432, 6504, 9576, 12648, 15720, 18792, 21864, 24936, 28008, 31080, 32104, 33128]
#guard (exampleTables 34152).map (fun t => t.funs.toList.map (·.start)) ==
  (exampleTables 34152).map starts
#guard (exampleTables 34152).map (fun t => t.funs.all fun f => f.phi.size == f.len) == some true
-- matrix, block length, vector, first entry and number of weights of each table are those that the
-- C++ verifier printed at this configuration's first attention sub-proof
#guard (exampleTables 34152).map (fun t => t.funs.toList.map fun f =>
    (f.mat, f.len, f.tree, f.start, f.phi.size)) ==
  some (TestHonest.seenTables.map fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1))
#guard (exampleTables 34152).map (fun t => (t.ptM.size, t.ptD.size)) == some (12, 11)
-- on a view the last table has the weights 2^(row mod 32); the dry run has zeros of the same length
#guard (exampleTables 34152).map (fun t => ((t.funs.back?.map (·.phi)).getD #[]).extract 30 34) ==
  some (small [2 ^ 30, 2 ^ 31, 1, 2])
#guard (exampleTables 34152 true).map starts == (exampleTables 34152).map starts
#guard (exampleTables 34152 true).map (fun t => t.funs.all fun f =>
    f.phi.size == f.len && f.phi.all isZeroE) == some true
-- another planned length is refused
#guard (exampleTables 34151).isNone
#guard (exampleTables 34153).isNone

/-! ## The tests on points and on token weights -/

/-- The small configuration's tables with another first plane claim and another division. -/
def alteredTables (pc : PlaneClaim) (d : Divide) (dry : Bool := false) : Option Tables :=
  (Blk.runFrom
    (tables exampleShape exampleMats 34152 exampleLook
      #[pc, examplePlane .rd 11, examplePlane .fm 12, examplePlane .fd 11]
      #[exampleScore .fm 11, exampleScore .fd 10] d exampleAttain)
    { entries := [], st := {} } dry [] []).map (·.1)

/-- The small configuration's first plane claim at the point z. -/
def planeAt (z : Array E) : PlaneClaim := { examplePlane .rm 12 with z := z }

#guard (alteredTables (planeAt (zeros 12)) exampleDivide).isSome
-- The last 11 coordinates of a plane claim's point must be the last 11 of the lookup's point,
-- which are 0 here. The first of the 12 is free.
#guard (alteredTables (planeAt (zeros 11 ++ #[oneE])) exampleDivide).isNone
#guard (alteredTables (planeAt (#[zeroE, oneE] ++ zeros 10)) exampleDivide).isNone
#guard (alteredTables (planeAt (#[oneE] ++ zeros 11)) exampleDivide).isSome
-- Token and feature of segment wh must be those of segment wl.
#guard (alteredTables (planeAt (zeros 12)) { exampleDivide with ziH := zeros 5 ++ #[oneE] }).isNone
#guard (alteredTables (planeAt (zeros 12)) { exampleDivide with zcH := #[oneE] ++ zeros 6 }).isNone
-- Both must be the last coordinates of the lookup's point.
#guard (alteredTables (planeAt (zeros 12))
  { exampleDivide with ziW := #[oneE] ++ zeros 5, ziH := #[oneE] ++ zeros 5 }).isNone
-- These are tests on drawn values: the dry run skips them.
#guard (alteredTables (planeAt (zeros 11 ++ #[oneE])) exampleDivide true).isSome
#guard (alteredTables (planeAt (zeros 12)) { exampleDivide with ziH := zeros 5 ++ #[oneE] }
  true).isSome

/-! ## The names of the refusals -/

/-- The name under which a run outside any chain, on a view, is refused; none if it goes through.
This is not the function refusal of OnBytes/Model/TestAttentionPlan.lean. -/
def refusal {α : Type} (b : Blk α) : Option String :=
  match b.runNamed { entries := [], st := {} } false [] [] with
  | .error e => some e.name
  | .ok _ => none

/-- The small configuration's tables for an array of nW entries, at another shape. -/
def tablesAt (S : Shape) (nW : Nat) : Blk Tables :=
  tables S exampleMats nW exampleLook
    #[examplePlane .rm 12, examplePlane .rd 11, examplePlane .fm 12, examplePlane .fd 11]
    #[exampleScore .fm 11, exampleScore .fd 10] exampleDivide exampleAttain

#guard refusal (tablesAt exampleShape 34152) == none
#guard refusal (add one 0 4 #[] 5 {}) == some "internal-a-table-length"
#guard refusal (tablesAt exampleShape 34151) == some "internal-af-W-length"
#guard refusal (lng exampleShape (zeros 7) (fun _ => zeros 63) {}) == some "plan-tensor-layout"
#guard refusal (lng exampleShape (zeros 1) (fun _ => zeros 64) {}) == some "plan-tensor-layout"
#guard refusal (tables exampleShape exampleMats 34152 exampleLook
    #[planeAt (zeros 11 ++ #[oneE]), examplePlane .rd 11, examplePlane .fm 12, examplePlane .fd 11]
    #[exampleScore .fm 11, exampleScore .fd 10] exampleDivide exampleAttain) ==
  some "internal-a-merged-point"
#guard refusal (tables exampleShape exampleMats 34152 exampleLook
    #[examplePlane .rm 12, examplePlane .rd 11, examplePlane .fm 12, examplePlane .fd 11]
    #[exampleScore .fm 11, exampleScore .fd 10]
    { exampleDivide with ziH := zeros 5 ++ #[oneE] } exampleAttain) ==
  some "internal-a-merged-point"
-- A matrix of 2^4 rows cannot hold the planes of the lookup's counts. This is refused before the
-- first table on that matrix is placed, which would be refused for its length.
#guard refusal (tablesAt { exampleShape with cf := { exampleShape.cf with lmb := 4 } } 34152) ==
  some "forest-planes"

-- A block of 4 features with 64 tokens each has 256 weights.
#guard (ran (lng exampleShape (zeros 7) fun _ => zeros 64)).map (·.1.size) == some 256
-- 63 token weights; a block of 8 features, which does not have 2^8 rows; a point of one coordinate
#guard (ran (lng exampleShape (zeros 7) fun _ => zeros 63)).isNone
#guard (ran (lng { exampleShape with ls := 3 } (zeros 7) fun _ => zeros 64)).isNone
#guard (ran (lng exampleShape (zeros 1) fun _ => zeros 64)).isNone

end OnBytes.Attention.TestTables
