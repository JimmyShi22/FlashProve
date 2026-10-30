-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestTailMore.lean: further conditions and numbers of Tail.lean, each on a state made
for it.

The other test files of Tail.lean leave some conditions untried, because on their examples another
condition fails at the same time, or because a number is 0 or two numbers are equal there. Each
guard here has a state on which the condition, or the number, decides alone. The states are made up:
most of them cannot arise from shapeF and addTreesF. The list of conditions is that of Tail.lean's
own text. The expected names and numbers were worked out by hand from that text.

No proof is read. The terms are explained in OnBytes/Model/Tail.lean (the docstring of HTailF2 says
where). The file is not imported by the program.
-/
import OnBytes.Model.TestTailHeld
import OnBytes.Model.TestTailNames
import OnBytes.Model.TestTailRefusals

namespace OnBytes.Model.TestTailMore

open OnBytes OnBytes.Model OnBytes.Model.TestTailRun

/-! ## addTreesF: each array must get the index that shapeF gave it -/

/-- One matrix that no other sub-proof reads, one that another reads, one of an earlier sub-proof.
The arrays: U3 0, PK0 1, PX0 2, ZZ 3, BZ 4, PXf0 5. -/
def mixed : Except String HTailF2 :=
  TestTailRefusals.shapeOf
    #[TestTailRefusals.own 6 2, { TestTailRefusals.own 6 3 with name := "qa" },
      TestTailRefusals.earlier 0 9 4]
    #[none, some 0, none] #[TestTailRefusals.array 9 4]

/-- The name under which addTrees refuses the changed shape; "" if it does not. -/
def listName (change : HTailF2 → HTailF2) (nU : Array Nat := #[0, 0, 4]) : String :=
  TestTailRefusals.nameOf (mixed.bind fun tl => (change tl).addTrees {} {} nU #[2] 100 128)

/-- Changes the indices of the arrays. -/
def onIx (f : T2Map → T2Map) (tl : HTailF2) : HTailF2 := { tl with ix := f tl.ix }

#guard listName id == ""
#guard listName (onIx fun x => { x with U := x.U.set! 3 (some 9) }) == "internal-t2f-lists"
#guard [onIx fun x => { x with U := x.U.set! 2 (some 1) }, onIx fun x => { x with PK := #[2] },
    onIx fun x => { x with TX := #[1] }, onIx fun x => { x with ZZ := 4 },
    onIx fun x => { x with BZ := 3 }, onIx fun x => { x with FT := #[4] },
    -- the earlier sub-proof's array has other rows of cells, or other columns, than the matrix
    fun tl => { tl with ft := tl.ft.modify 0 fun X => { X with m := 12 } },
    fun tl => { tl with ft := tl.ft.modify 0 fun X => { X with K := 5 } }].all
  fun change => listName change == "internal-t2f-map"
-- What addTrees records besides the arrays.
#guard (mixed.bind fun tl => tl.addTrees {} {} #[7, 8, 4] #[2] 100 128).toOption.any
  fun (tl, _, _) => tl.nUF == #[7, 8, 4] && tl.tabFirst == #[0, 0] && tl.tabLen == #[0, 4] &&
    (tl.plOwn.map fun p => (p.padRows, p.off, p.lanes, p.J)) == #[(2, 0, 3, 1)] &&
    (tl.plFor.map fun p => (p.padRows, p.off, p.mS, p.K)) == #[(3, 0, 3, 4)]
#guard mixed.toOption.any fun tl => tl.col0 == #[0, 0, 0] && tl.gtRow == #[0, 0, 0]
-- Two arrays of earlier sub-proofs get consecutive indices.
#guard (TestTailRefusals.shapeOf
    #[TestTailRefusals.earlier 0 9 4, TestTailRefusals.earlier 1 9 4] #[none, none]
    #[TestTailRefusals.array 9 4, TestTailRefusals.array 9 4]).toOption.any
  fun tl => tl.ix.FT == #[3, 4] && tl.gtTree == #[3, 4]

/-! ## Small functions -/

#guard !HTailF2.allDistinct [1, 2, 2]
#guard TestTailRefusals.listed fun tl F =>
  (tl.powersF { TestTailRefusals.drawn F with thetaDrawnF := false }).isNone
-- A table without an entry (segments longer than the matrix) does not count as a tile.
#guard TestTailRefusals.listed fun tl _ =>
  tl.tablesTile #[TestTailRefusals.table 0 3 0, TestTailRefusals.table 0 7 4] 2 == none
-- The tables end after the vector's last entry: none. Where the sub-proof has no such vector, the
-- length is not compared, and the same tables pass.
#guard TestTailRefusals.listed fun tl _ =>
  ({ tl with nUF := #[0, 0, 3] } : HTailF2).tablesTile #[TestTailRefusals.table 0 3 0] 2 == none &&
    (onIx (fun x => { x with U := x.U.set! 2 none }) { tl with nUF := #[0, 0, 3] }).tablesTile
      #[TestTailRefusals.table 0 3 0] 2 == some 2
-- The part that holds tables begins at entry 1 of U3: entry 0 is outside, and marks count from 1.
#guard TestTailRefusals.listed fun tl _ =>
  let late : HTailF2 := { tl with tabFirst := #[0, 1] }
  late.markRead (TestTailRefusals.table 0 3 0) 0 TestTailRefusals.noMark == none &&
    late.markRead (TestTailRefusals.table 0 3 1) 0 TestTailRefusals.noMark ==
      some #[#[], #[true, false, true, false]] &&
    late.tablesTile #[TestTailRefusals.table 0 3 1] 2 == none &&
    ({ late with nUF := #[0, 0, 5] } : HTailF2).tablesTile #[TestTailRefusals.table 0 3 1] 2 ==
      some 2
-- Only rowLo is given, the factors for bits that are 0: the factor for a bit that is 1 is then 0.
#guard rowFactors { rowLo := #[ofNat 2, ofNat 2, ofNat 2] } 1 == (ofNat 2, zeroE)
-- A sub-proof without U3 has no part that holds tables.
#guard ((({} : HTailF2).shape #[TestTailRefusals.own 6 2] #[none] #[] #[false, false, false, false]
    160).bind fun tl => tl.addTrees {} {} #[0, 0, 4] #[] 100 128).toOption.any
  fun (tl, _, _) => tl.tabLen == #[0, 0]
-- A piece of one row.
#guard HTailF2.pieceHeld 11 { TestTailHeld.piece with Rp := 1, a := 0, b := 3 }

/-! ## The second computation, on states made for one condition -/

open TestTailHeld in
-- The second piece's keys come before the first piece's: no overlap.
#guard ready.any fun s =>
  let t := onPiece 0 1 (fun p => { p with off := 0 })
    (onPiece 0 0 (fun p => { p with off := 1024 }) s)
  t.tl.callHeld t.g 2 0

open TestTailHeld in
-- A call of 2^10 keys, the least number.
#guard ready.any fun s =>
  let t := onG (fun g => { g with zk := g.zk.set! 0 (Array.replicate 10 oneE) })
    (onCall (fun c => { c with n := 10 })
      (onPiece 0 1 (fun p => { p with Cp := 3, CP := 4, b := 7, off := 512 })
        (onPiece 0 0 (fun p => { p with Cp := 3, CP := 4, b := 9 }) s)))
  t.tl.callHeld t.g 2 0

open TestTailHeld in
-- Four trees a call: the second call's first tree is number 4.
#guard ready.any fun s =>
  let t := onShape
    (fun h => { h with dT := 9, NT := 8, rK := 3, iota := #[2, 2], first := #[0, 4] }) (split s)
  t.tl.forestHeld t.g &&
    !(onShape (fun h => { h with first := #[0, 9] }) t).tl.forestHeld t.g

open TestTailHeld in
-- A weight in the first row after a piece's rows, and in the first column after its columns.
#guard onReady piecesWeighed [nudgeRow 2 0 128, nudgeColumn 2 0 6]

open TestTailHeld in
-- Four calls' worth of planes: every size fits, and only cK = 1 fails.
#guard ready.any fun s =>
  let wide (r : HRow) : HRow := { r with L := Array.replicate 4096 zeroE }
  let t := onG (fun g => { g with zb0 := g.zb0.push oneE, zb1 := g.zb1.push oneE })
    (onRow 3 0 wide (onRow 3 1 wide (onRow 3 2 wide
      (onTree 3 (fun X => { X with K := 4096 }) (onShape (fun h => { h with cK := 2 }) s)))))
  !t.tl.planesShapeHeld t.F t.g && t.tl.bzColumns == 4096

open TestTailHeld in
-- BZ has a column less, and so has each of its rows' column weights: only the number of columns is
-- wrong.
#guard onReady (fun s => s.tl.planesShapeHeld s.F s.g) [fun s =>
  let cut (r : HRow) : HRow := { r with L := r.L.extract 0 2047 }
  onRow 3 0 cut (onRow 3 1 cut (onRow 3 2 cut (onTree 3 (fun X => { X with K := 2047 }) s)))]

open TestTailHeld in
-- The reads' and the ties' rows of ZZ have the same wrong weight on row 7.
#guard namesOnReady tileName
  [("internal-f-tie-weights", fun s => nudgeRow 2 5 7 (nudgeRow 2 4 7 s))]

/-- The example in a dry run, with all weights set. -/
def readyDry : Option TestTailHeld.Both :=
  (claimsAdded true).bind fun (tl, F) =>
    ((tl.coefficientsF F).outcome (noRounds true)).map fun x => { tl := tl, F := x.1.2 }

/-- The name under which tileSelfTestF fails in a dry run, which skips the tests on values. -/
def tileNameDry (s : TestTailHeld.Both) : String :=
  match (s.tl.tileSelfTestF s.F) (noRounds true) with
  | .ok _ => ""
  | .error e => e.name

-- The shapes' rows of cells do not add up to mz. No test on values can fail in its place.
#guard readyDry.any fun s => tileNameDry s == "" &&
  tileNameDry (TestTailHeld.onShp (fun x => { x with m := 7 }) s) == "internal-f-tie-weights"
-- Of the reads' weights the public conditions are tested in a dry run, the values are not.
#guard readyDry.any fun s =>
  tileNameDry (TestTailHeld.onTl (fun tl => { tl with nX4Laid := 3 }) s)
      == "internal-f-read-weights" &&
    tileNameDry (TestTailHeld.nudgeColumn 2 4 0 s) == ""

/-- The name under which selfTestF fails in a dry run, which skips the tests on values. -/
def selfNameDry (s : TestTailHeld.Both) : String :=
  match (s.tl.selfTestF #[0, 0, 4] s.F) (noRounds true) with
  | .ok _ => ""
  | .error e => e.name

-- The kept weights of the slots are one too many. On a view the comparison of the slots fails too,
-- under the same name; in a dry run only the condition on the length is left.
#guard readyDry.any fun s => selfNameDry s == "" &&
  selfNameDry (TestTailHeld.onTl (fun tl => { tl with lsTail := tl.lsTail.push zeroE }) s) ==
    "internal-f-tail-slot"

/-! ## The claims -/

open TestTailNames in
-- The lookup's numbers of padding keys differ from the places at which the claim reads nothing.
#guard claimsName #[table] (fun tl => { tl with
    heard := tl.heard.map fun g => { g with shape := { g.shape with pub := #[1087, 1088] } } }) ==
  "internal-forest-padding-places"

open TestTailNames in
-- Two pieces read 200 * 8 and 100 * 8 places of one tree, which has 2048.
#guard claimsName #[table] (fun tl => { tl with
    z1 := { tl.z1 with
      pieces := (tl.z1.pieces.modify 0 fun p => { p with Rp := 200, Cp := 8 }).modify 1
        fun p => { p with Rp := 100, Cp := 8, off := 0 } } }) == "internal-f-join-place"

open TestTailNames in
-- The lookup adds one claim more than Forest.lins says.
#guard claimsName #[table] (fun tl => { tl with
    heard := tl.heard.map fun g => { g with rows := g.rows.push (Aff.slot 8) } }) ==
  "internal-f-exist"

open TestTailNames in
-- The array on which the tie was added does not count as a symbol array.
#guard claimsName #[table] id (fun F => { F with
    trees := F.trees.modify 1 fun X => { X with kind := .table } }) == "internal-f-exist"

end OnBytes.Model.TestTailMore
