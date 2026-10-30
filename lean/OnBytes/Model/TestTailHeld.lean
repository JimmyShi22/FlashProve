-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestTailHeld.lean: the conditions of the smallness test's tests on itself, one at a
time.

HTailF2.selfTestF and tileSelfTestF (OnBytes/Model/Tail.lean) are long conjunctions. tileSelfTestF
is written in parts: forestHeld, callHeld with pieceHeld, piecesTile, pointsHeld, pieceWeightsHeld,
tieShapeHeld, tieWeightsHeld, planesShapeHeld, planesWeightsHeld, readShapeHeld, readWeightsHeld.
This file takes the small example of OnBytes/Model/TestTailRun.lean, on which all conditions hold,
and changes one number, size or weight so that, where that is possible, exactly one condition fails.
The part that has the condition must then be false. Only the last two sections run selfTestF and
tileSelfTestF themselves; they compare the name under which the routine fails. That only one
condition fails is by the choice of the change; the file does not test it. The list of conditions is
that of Tail.lean's own text: this file does not test that the list is complete.

Some conditions follow from others and cannot fail alone: in pieceHeld, Rp != 0 (from 2^a = Rp) and
b <= n (from off + 2^b <= 2^n); in callHeld, 10 <= n (from n = max 10 ..); in pieceWeightsHeld, that
ka and the two first weights are not 0 (from the products that are not 0) and the last corner (from
the first row and the first column); in planesShapeHeld, K = 2^(kT + cK) (from K = bzColumns); in
readShapeHeld, len != 0 (from m != 0 and m % len = 0, since m % 0 is m).

No change in this file reaches these conditions: in pieceWeightsHeld, that the expected products are
not 0; in tieWeightsHeld, that the row weights and the expected weights of the digits are not 0 and
that the row weights differ; in planesShapeHeld, cK = 1. OnBytes/Model/TestTailCases.lean and
TestTailMore.lean try them, except "the row weights are not 0". That condition cannot fail alone:
where a row weight is 0, the expected weights of its digits are 0 too.

No proof is read. The terms are explained in OnBytes/Model/Tail.lean (the docstring of HTailF2 says
where). The file is not imported by the program.
-/
import OnBytes.Model.TestTailRun

namespace OnBytes.Model.TestTailHeld

open OnBytes OnBytes.Model OnBytes.Model.TestTailRun

/-- True if held is true of base and false of each changed copy. -/
def eachBreaks {σ : Type} (held : σ → Bool) (base : σ) (changes : List (σ → σ)) : Bool :=
  held base && changes.all fun change => !held (change base)

/-! ## One piece of a call -/

/-- The first piece of the example's first call: 128 rows, 6 columns in places for 8. -/
def piece : Piece := { tree := 2, Rp := 128, Cp := 6, CP := 8, a := 7, b := 10 }

#guard eachBreaks (HTailF2.pieceHeld 11) piece [
  fun p => { p with Cp := 0 }, fun p => { p with Rp := 64 }, fun p => { p with r0 := 64 },
  fun p => { p with Cp := 9 }, fun p => { p with CP := 7 }, fun p => { p with b := 9 },
  fun p => { p with off := 512 }, fun p => { p with off := 2048 }]
-- At most 2^40 rows.
#guard HTailF2.pieceHeld 50 { piece with a := 40, Rp := 2 ^ 40, b := 43 } &&
  !HTailF2.pieceHeld 50 { piece with a := 41, Rp := 2 ^ 41, b := 44 }

/-! ## Rectangles that overlap -/

/-- The rectangle with the rows r0, r0 + 1 and the columns c0, c0 + 1. -/
def square (r0 c0 : Nat) : HTailF2.Want := { r0 := r0, Rp := 2, c0 := c0, Cp := 2 }

#guard (square 2 2).meets (square 3 3) && (square 2 2).meets (square 1 1) &&
  (square 2 2).meets (square 2 2)
#guard !(square 2 2).meets (square 4 2) && !(square 2 2).meets (square 0 2) &&
  !(square 2 2).meets (square 2 4) && !(square 2 2).meets (square 2 0)
#guard HTailF2.noneMeet [square 0 0, square 0 2, square 2 0] && HTailF2.noneMeet []
#guard !HTailF2.noneMeet [square 0 0, square 0 2, square 1 1] &&
  !HTailF2.noneMeet [square 0 0, square 1 1, square 4 4] &&
  !HTailF2.noneMeet [square 4 4, square 0 0, square 1 1]

/-! ## The example with all weights set -/

/-- The example's states. -/
structure Both where
  /-- the smallness test's state -/
  tl : HTailF2
  /-- the sub-proof's state -/
  F : Fork

/-- The example after all claims are added and the weights on the rows are set. -/
def ready : Option Both :=
  (claimsAdded false).bind fun (tl, F) =>
    ((tl.coefficientsF F).outcome (noRounds false)).map fun x => { tl := tl, F := x.1.2 }

/-- True if the example could be made, held is true of it and false of each changed copy. -/
def onReady (held : Both → Bool) (changes : List (Both → Both)) : Bool :=
  ready.any fun s => eachBreaks held s changes

/-- What the lookup has received and drawn. -/
def Both.g (s : Both) : Forest.Heard := s.tl.heard.getD (heard false s.tl)

/-- Changes what the lookup has received and drawn. -/
def onG (f : Forest.Heard → Forest.Heard) (s : Both) : Both :=
  { s with tl := { s.tl with heard := some (f s.g) } }

/-- Changes the smallness test's state. -/
def onTl (f : HTailF2 → HTailF2) (s : Both) : Both := { s with tl := f s.tl }

/-- Changes array number t. -/
def onTree (t : Nat) (f : HTree → HTree) (s : Both) : Both :=
  { s with F := { s.F with trees := s.F.trees.modify t f } }

/-- Changes virtual row r of array t. -/
def onRow (t r : Nat) (f : HRow → HRow) (s : Both) : Both :=
  { s with F := HTailF2.onRow s.F t r f }

/-- Changes piece i of call q. -/
def onPiece (q i : Nat) (f : Piece → Piece) : Both → Both :=
  onTl fun tl =>
    if q == 0 then { tl with z1 := { tl.z1 with pieces := tl.z1.pieces.modify i f } }
    else { tl with z2 := { tl.z2 with pieces := tl.z2.pieces.modify i f } }

/-- Changes the first call. -/
def onCall (f : Call → Call) : Both → Both :=
  onTl fun tl => { tl with z1 := { tl.z1 with call := f tl.z1.call } }

/-- Changes the lookup's public numbers. -/
def onShape (f : Forest.Shape → Forest.Shape) : Both → Both :=
  onTl fun tl => { tl with f9 := f tl.f9 }

/-! ## The lookup's public numbers -/

#guard onReady (fun s => s.tl.forestHeld s.g) [
  onTl fun tl => { tl with z2 := { tl.z2 with call := { tl.z2.call with n := 12 } } },
  onShape fun h => { h with dT := 12 }, onShape fun h => { h with kT := 11 },
  onShape fun h => { h with NT := 3 }, onShape fun h => { h with rK := 2 },
  onShape fun h => { h with iota := #[0, 1] }, onShape fun h => { h with first := #[0, 2] },
  onG fun g => { g with zy := g.zy.push oneE }, onG fun g => { g with zx := g.zx.push oneE },
  onG fun g => { g with e := g.e.push oneE }]

/-! ## One call -/

#guard onReady (fun s => s.tl.callHeld s.g 2 0) [
  onCall fun c => { c with name := "R8d" }, onCall fun c => { c with fn := 1 },
  onCall fun c => { c with k := 8 }, onCall fun c => { c with kappa := 4 },
  onCall fun c => { c with t0 := 1 }, onCall fun c => { c with iota := 1 },
  onG fun g => { g with zk := g.zk.modify 0 (·.push oneE) },
  onPiece 0 0 fun p => { p with Cp := 0 },
  -- the second piece's keys begin inside the first piece's
  onPiece 0 1 fun p => { p with off := 0 },
  -- fewer keys, so that 2^10 places would do
  fun s => onPiece 0 1 (fun p => { p with Cp := 3, CP := 4, b := 7, off := 512 })
    (onPiece 0 0 (fun p => { p with Cp := 3, CP := 4, b := 9 }) s)]
#guard onReady (fun s => s.tl.callHeld s.g 2 1) [
  onTl fun tl => { tl with z2 := { tl.z2 with call := { tl.z2.call with name := "R10z" } } },
  onTl fun tl => { tl with z2 := { tl.z2 with call := { tl.z2.call with k := 10 } } }]
-- The number of pieces.
#guard ready.any fun s => !s.tl.callHeld s.g 1 0 && !s.tl.callHeld s.g 3 0

/-- A call of one piece with 2^n keys, for the bound on n. -/
def wide (n : Nat) (s : Both) : Both :=
  onG (fun g => { g with zk := g.zk.set! 0 (Array.replicate n oneE) })
    (onTl (fun tl => { tl with
      z1 := { call := { tl.z1.call with n := n, iota := n - tl.lidb },
              pieces := #[{ piece with CP := 2 ^ (n - 7), b := n }] } }) s)

#guard ready.any fun s => (wide 44 s).tl.callHeld (wide 44 s).g 1 0 &&
  !(wide 45 s).tl.callHeld (wide 45 s).g 1 0

/-! ## The pieces tile ZZ -/

/-- The expected pieces. -/
def Both.W (s : Both) : List HTailF2.Want := (s.tl.wants.map (·.2)).getD []

/-- Changes piece i of call q, and with it the expected piece. -/
def moved (q i : Nat) (f : Piece → Piece) (fw : HTailF2.Want → HTailF2.Want) (s : Both) :
    Both × List HTailF2.Want :=
  (onPiece q i f s, s.W.map fun w => if w.call == q && w.i == i then fw w else w)

#guard onReady (fun s => s.tl.piecesTile s.F s.W) [
  onTree 2 fun X => { X with name := "ZY" },
  onPiece 0 0 fun p => { p with tree := 3 }, onPiece 0 1 fun p => { p with row := 0 },
  onPiece 1 1 fun p => { p with r0 := 0 }, onPiece 1 0 fun p => { p with Rp := 64 },
  onPiece 1 0 fun p => { p with c0 := 0 }, onPiece 0 0 fun p => { p with Cp := 5 },
  onRow 2 3 fun row => { row with coef := row.coef.push zeroE },
  onRow 2 0 fun row => { row with L := row.L.push zeroE }]
-- The list W stays as it is while tau or mz is changed.
#guard ready.any fun s => !({ s.tl with tau := 161 } : HTailF2).piecesTile s.F s.W &&
  !({ s.tl with mz := 7 } : HTailF2).piecesTile s.F s.W
-- Two pieces on one rectangle and a gap elsewhere: the areas still add up.
#guard ready.any fun s =>
  let x := moved 1 1 (fun p => { p with c0 := 0 }) (fun w => { w with c0 := 0 }) s
  !x.1.tl.piecesTile x.1.F x.2
-- A piece that is one column short.
#guard ready.any fun s =>
  let x := moved 1 1 (fun p => { p with Cp := 5 }) (fun w => { w with Cp := 5 }) s
  !x.1.tl.piecesTile x.1.F x.2
-- A piece that reaches below the last row, and one that reaches past the last column.
#guard ready.any fun s =>
  let x := moved 0 1 (fun p => { p with r0 := 130 }) (fun w => { w with r0 := 130 }) s
  !x.1.tl.piecesTile x.1.F x.2
#guard ready.any fun s =>
  let x := moved 1 1 (fun p => { p with c0 := 7 }) (fun w => { w with c0 := 7 }) s
  !x.1.tl.piecesTile x.1.F x.2

/-! ## The calls' points -/

#guard onReady (fun s => s.tl.pointsHeld s.g) [
  onG fun g => { g with e := g.e.modify 0 (addE · oneE) },
  onG fun g => { g with e := g.e.modify 1 (addE · oneE) },
  onG fun g => { g with zk := g.zk.modify 0 fun z => z.modify 0 (addE · oneE) },
  onG fun g => { g with zk := g.zk.modify 1 fun z => z.modify 10 (addE · oneE) }]

/-- The example with lidb = 9, that is, trees of 2^9 places, so that each call has four trees and
its point begins with two coordinates of zy. Only lidb and what the lookup has drawn are changed: f9
keeps the example's numbers, which pointsHeld does not read. -/
def split (s : Both) : Both :=
  onG (fun g =>
      let zy := els false 100 3
      let zx := els false 200 9
      { g with zy := zy, zx := zx, e := #[subE oneE (zy.getD 0 zeroE), zy.getD 0 zeroE],
               zk := #[zy.extract 1 3 ++ zx, zy.extract 1 3 ++ zx] })
    (onTl (fun tl => { tl with lidb := 9 }) s)

#guard ready.any fun s => eachBreaks (fun s => s.tl.pointsHeld s.g) (split s) [
  onG fun g => { g with zk := g.zk.modify 0 fun z => z.modify 1 (addE · oneE) },
  onG fun g => { g with zk := g.zk.modify 1 fun z => z.modify 2 (addE · oneE) },
  onG fun g => { g with zy := g.zy.modify 2 (addE · oneE) },
  onG fun g => { g with zx := g.zx.modify 8 (addE · oneE) }]

/-! ## The weights of the claim on the key vectors -/

/-- Adds 1 to weight r of virtual row number row of array t on the array's rows. -/
def nudgeRow (t row r : Nat) : Both → Both :=
  onRow t row fun x => { x with coef := x.coef.modify r (addE · oneE) }

/-- Adds 1 to column weight c of virtual row number row of array t. -/
def nudgeColumn (t row c : Nat) : Both → Both :=
  onRow t row fun x => { x with L := x.L.modify c (addE · oneE) }

/-- True if the weights of all four pieces are as the second computation has them. -/
def piecesWeighed (s : Both) : Bool :=
  s.tl.joinObj9.any fun jo =>
    s.W.all (s.tl.pieceWeightsHeld s.F s.g (t2fKappaByText s.F.theta jo))

#guard onReady piecesWeighed [
  -- inside a rectangle: a column weight, a row weight
  nudgeColumn 2 0 3, nudgeColumn 2 3 11, nudgeRow 2 0 5, nudgeRow 2 3 159,
  -- outside: columns on the right and on the left, rows below and above
  nudgeColumn 2 0 7, nudgeColumn 2 2 1, nudgeRow 2 0 130, nudgeRow 2 1 5,
  onTl fun tl => { tl with joinObj9 := tl.joinObj9.map (· + 1) },
  onG fun g => { g with zk := g.zk.modify 0 fun z => z.modify 4 (addE · oneE) }]

/-! ## The tie's shape -/

/-- Changes the shape of the one matrix's symbol array. -/
def onShp (f : ShP → ShP) : Both → Both := onTl fun tl => { tl with shp := tl.shp.modify 0 f }

#guard onReady (fun s => s.tl.tieShapeHeld s.F 0) [
  onTree 1 fun X => { X with kind := .table },
  onTree 1 fun X => { X with rows := X.rows.push {} },
  onTree 1 fun X => { X with R := 3 }, onTree 1 fun X => { X with K := 3 },
  onTl fun tl => { tl with tieObj := #[] }, onTl fun tl => { tl with tieObj := #[1000] },
  onShp fun x => { x with mS := 3 }, onShp fun x => { x with J := 2 },
  onShp fun x => { x with R := 3 }, onShp fun x => { x with Rd := 1 },
  onShp fun x => { x with K1 := 3 },
  -- Rr, with the array's rows and the row weights to match
  fun s => onShp (fun x => { x with Rr := 3 })
    (onTree 1 (fun X => { X with R := 3 })
      (onRow 1 0 (fun r => { r with coef := r.coef.push oneE }) s)),
  -- Kc, with the array's columns to match
  fun s => onShp (fun x => { x with Kc := 3 }) (onTree 1 (fun X => { X with K := 3 }) s),
  onTl fun tl => { tl with mats := tl.mats.modify 0 fun M => { M with k := 3 } },
  onTl fun tl => { tl with rowX := tl.rowX.modify 0 (·.push oneE) },
  onTl fun tl => { tl with loX := tl.loX.modify 0 (·.push oneE) },
  onRow 1 0 fun r => { r with coef := r.coef.push oneE },
  onRow 1 0 fun r => { r with L := r.L.push oneE },
  onTl fun tl => { tl with gamX := tl.gamX.modify 0 (·.push oneE) },
  onTl fun tl => { tl with gamV := tl.gamV.modify 0 (·.push oneE) }]

/-! ## The tie's weights -/

/-- True if the tie's weights are as the second computation has them. -/
def tieWeighed (s : Both) : Bool :=
  s.tl.tieWeightsHeld s.F ((s.F.trees.getD 2 {}).rows.getD 5 {}).L 0

#guard onReady tieWeighed [
  onTl fun tl => { tl with loX := #[#[ofNat 2]] },
  nudgeRow 1 0 1, nudgeColumn 1 0 0, nudgeColumn 1 0 1,
  -- low digits and high digits in the ties' row of ZZ
  nudgeColumn 2 5 0, nudgeColumn 2 5 5, nudgeColumn 2 5 6, nudgeColumn 2 5 11,
  onTl fun tl => { tl with gamX := tl.gamX.modify 0 fun g => g.modify 0 (addE · oneE) },
  onTl fun tl => { tl with gamV := tl.gamV.modify 0 fun g => g.modify 1 (addE · oneE) },
  onTl fun tl => { tl with cfF := tl.cfF.modify 200 fun x => if x == 1 then 0 else 1 },
  onShp fun x => { x with m := 7 }]
-- Two rows of symbols with one weight, as under the batching element 1. Only neighboursDiffer runs
-- here, on the weights that the second computation gives.
#guard !HTailF2.neighboursDiffer ((HTailF2.powersAgain oneE 256 2).toList.mergeSort HTailF2.leE)

/- ## The reads' weights -/

/-- The column weights of the reads' row of ZZ. -/
def Both.readColumns (s : Both) : Array E := ((s.F.trees.getD 2 {}).rows.getD 4 {}).L

/-- Changes the example's one table. It has two segments of three rows of cells. -/
def onTable (f : HFun → HFun) : Both → Both :=
  onTl fun tl => { tl with funs := tl.funs.modify 0 f }

#guard onReady (fun s => s.tl.readShapeHeld s.readColumns) [
  onRow 2 4 fun r => { r with L := r.L.push oneE },
  onTable fun Fn => { Fn with phi := Fn.phi.push oneE },
  onTl fun tl => { tl with nX4Laid := 3 },
  -- mz and the row's length together, so that only the matrices' rows of cells disagree
  fun s => onTl (fun tl => { tl with mz := 7 })
    (onRow 2 4 (fun r => { r with L := r.L ++ #[oneE, oneE] }) s),
  -- a segment of four rows does not divide the six rows; 6 / 4 = 1 read is what is counted
  fun s => onTl (fun tl => { tl with nX4Laid := 1 })
    (onTable (fun Fn => { Fn with len := 4, phi := Fn.phi.push oneE }) s),
  -- a second matrix without a row, and a table on it: it adds no read and no row
  onTl fun tl => { tl with NM := 2, mats := tl.mats.push { name := "y", m := 0, k := 1 },
                           funs := tl.funs.push { mat := 1, len := 1, phi := #[oneE], tree := 2 } },
  -- the one table is passed over, so that no read is counted
  onTable fun Fn => { Fn with tree := 1 }, onTable fun Fn => { Fn with mat := 1 },
  -- a segment of no row: this fails more than one condition
  onTable fun Fn => { Fn with len := 0, phi := #[] }]
-- A further table on no matrix, or in another vector, is passed over, whatever its numbers.
#guard ready.any fun s =>
  ({ s.tl with funs := s.tl.funs ++ #[{ mat := 1, len := 0 }, { mat := 0, len := 0, tree := 1 }] }
    : HTailF2).readShapeHeld s.readColumns

/-- True if the reads' weights on ZZ's columns are as the second computation has them. -/
def readWeighed (s : Both) : Bool := s.tl.readWeightsHeld s.F s.readColumns

#guard onReady readWeighed [
  -- low digits and high digits, of the first and of the second read
  nudgeColumn 2 4 0, nudgeColumn 2 4 5, nudgeColumn 2 4 6, nudgeColumn 2 4 11,
  fun s => { s with F := { s.F with planClaimsF := s.F.planClaimsF + 1 } },
  onTable fun Fn => { Fn with phi := Fn.phi.modify 2 (addE · oneE) },
  -- Np becomes 128, where tau = 160 gives 256; the tie's equations take the room of four rows of
  -- symbols, not of two
  onTl fun tl => { tl with tau := 128 },
  onTl fun tl => { tl with mats := tl.mats.modify 0 fun M => { M with m := 7 } }]
-- The second read stands under theta^256 times the first read's power (tau = 160); a high digit has
-- 2^10 times the low digit's weight. Written out by hand.
#guard ready.any fun s =>
  let w := s.tl.readWeightsAgain s.F
  w.size == 12 && !isZeroE (w.getD 0 zeroE) &&
    w.getD 3 zeroE == mulE (w.getD 0 zeroE) (powE s.F.theta 256) &&
    w.getD 6 zeroE == scaleNat (w.getD 0 zeroE) 1024

/-! ## BZ -/

#guard onReady (fun s => s.tl.planesShapeHeld s.F s.g) [
  onTree 3 fun X => { X with rows := X.rows.push {} }, onTree 3 fun X => { X with R := 31 },
  onTree 3 fun X => { X with K := 2047 }, onShape fun h => { h with NC := 3 },
  onRow 3 0 fun r => { r with coef := r.coef.push oneE },
  onRow 3 2 fun r => { r with L := r.L.push oneE },
  onG fun g => { g with zb0 := g.zb0.push oneE }, onG fun g => { g with zb1 := g.zb1.push oneE }]

#guard onReady (fun s => s.tl.joinObj9.any fun jo => s.tl.planesWeightsHeld s.F s.g jo) [
  nudgeRow 3 2 31, nudgeRow 3 0 0, nudgeRow 3 1 31, nudgeColumn 3 0 0, nudgeColumn 3 1 2047,
  nudgeColumn 3 2 33, onTl fun tl => { tl with bitFactor9 := addE tl.bitFactor9 oneE },
  onTl fun tl => { tl with joinObj9 := tl.joinObj9.map (· + 1) }]

/-! ## selfTestF: every column has a weight; the slots; the lengths nU -/

/-- Sets column weight c of virtual row number row of array t to 0. -/
def zeroColumn (t row c : Nat) : Both → Both :=
  onRow t row fun x => { x with L := x.L.set! c zeroE }

/-- The name under which a routine fails on the example's state; "" if it does not fail. -/
def nameOf (x : SubM Unit) (s : Both) : String :=
  match (x s.F) (noRounds false) with
  | .ok _ => ""
  | .error e => e.name

/-- True if the example could be made, run gives "" on it, and on each changed copy run gives the
name that stands beside the change. -/
def namesOnReady (run : Both → String) (cases : List (String × (Both → Both))) : Bool :=
  ready.any fun s => run s == "" && cases.all fun c => run (c.2 s) == c.1

/-- The name under which selfTestF fails. -/
def selfName (nU : Array Nat) (s : Both) : String := nameOf (s.tl.selfTestF nU) s

#guard namesOnReady (selfName #[0, 0, 4]) ([
    zeroColumn 0 0 3, zeroColumn 1 0 1,
    -- the pieces' rows of ZZ: low digits, then high digits
    zeroColumn 2 0 5, zeroColumn 2 1 0, zeroColumn 2 2 6, zeroColumn 2 3 11,
    -- the reads' row and the ties' row
    zeroColumn 2 4 0, zeroColumn 2 4 11, zeroColumn 2 5 0, zeroColumn 2 5 11,
    zeroColumn 3 0 2047, zeroColumn 3 1 0, zeroColumn 3 2 5].map
      fun change => ("internal-t2f-untyped", change)) &&
  namesOnReady (selfName #[0, 0, 4])
    [("internal-f-tail-slot", onTl fun tl => { tl with lsTail := tl.lsTail.push zeroE }),
     ("internal-f-tail-slot",
      fun s => { s with F := { s.F with LS := s.F.LS.modify 3 (addE · oneE) } }),
     -- a column without a weight and a changed slot: the column's name comes first
     ("internal-t2f-untyped",
      fun s => zeroColumn 0 0 3 { s with F := { s.F with LS := s.F.LS.modify 3 (addE · oneE) } })]
#guard ready.any fun s =>
  selfName #[0, 0, 3] s == "refused" && selfName #[0, 0, 4, 0] s == "refused"

/-! ## tileSelfTestF's own conditions, and that it calls its parts -/

/-- The name under which tileSelfTestF fails. -/
def tileName (s : Both) : String := nameOf s.tl.tileSelfTestF s

#guard namesOnReady tileName ([
    onTl fun tl => { tl with heard := none }, onTl fun tl => { tl with joinObj9 := none },
    -- 224 = 128 + 96: wants returns none
    onTl fun tl => { tl with tau := 224 }].map fun change => ("refused", change))
#guard namesOnReady tileName ([
    onTree 2 fun X => { X with rows := X.rows.push {} },
    -- forestHeld, callHeld of either call, piecesTile, pointsHeld, pieceWeightsHeld
    onShape fun h => { h with kT := 11 }, onCall fun c => { c with kappa := 4 },
    onTl fun tl => { tl with z2 := { tl.z2 with call := { tl.z2.call with kappa := 4 } } },
    onPiece 0 0 fun p => { p with tree := 3 },
    onG fun g => { g with e := g.e.modify 1 (addE · oneE) },
    nudgeColumn 2 0 3].map fun change => ("internal-t2f-untiled", change))
#guard namesOnReady tileName ([
    onRow 2 4 fun r => { r with coef := r.coef.push zeroE },
    onRow 2 5 fun r => { r with coef := r.coef.push zeroE },
    onRow 2 5 fun r => { r with L := r.L.push zeroE },
    onTl fun tl => { tl with gamX := tl.gamX.push #[] },
    onTl fun tl => { tl with gamV := tl.gamV.push #[] },
    -- tieShapeHeld, the shapes' rows of cells against mz, planesShapeHeld
    onShp fun x => { x with Rd := 1 }, onShp fun x => { x with m := 7 },
    onTree 3 fun X => { X with R := 31 },
    -- the weights of the reads' and the ties' rows on ZZ's rows
    nudgeRow 2 4 7, nudgeRow 2 5 7, nudgeRow 2 4 159,
    -- tieWeightsHeld, planesWeightsHeld
    nudgeColumn 1 0 1, nudgeColumn 3 2 33].map fun change => ("internal-f-tie-weights", change))
#guard namesOnReady tileName ([
    -- readShapeHeld, readWeightsHeld
    onRow 2 4 fun r => { r with L := r.L.push zeroE }, onTl fun tl => { tl with nX4Laid := 3 },
    nudgeColumn 2 4 0, nudgeColumn 2 4 11].map fun change => ("internal-f-read-weights", change))
-- The name is in the file's list, from which the lists of all names take it (Stages.allNames,
-- OnBytes/Model/StagesNames.lean; subProofNames, OnBytes/Model/VerifyStages.lean).
#guard Tail.names.contains "internal-f-read-weights"
-- A changed weight of BZ and one of the reads: BZ's test comes first here (in the C++ the reads').
#guard namesOnReady tileName
  [("internal-f-tie-weights", fun s => nudgeColumn 3 2 33 (nudgeColumn 2 4 0 s))]

end OnBytes.Model.TestTailHeld
