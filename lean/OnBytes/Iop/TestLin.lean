-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/TestLin.lean: tests, at small sizes, of some functions of Cs.lean, Foldeq.lean and
Lin.lean. Their steps of type Blk are not run here. Of Cs.lean: where the rest is placed
(SwitchPlaces, switchPieces, switchBox) and switchLift; its rows are not made here. The rows of
Foldeq.lean and Lin.lean, and Lin.lean's row weights, are compared entry by entry with what those
files' heads and docstrings say; these also explain the words used here (rest, pad, record).
The verifier program does not import this file.
-/
import OnBytes.Iop.Lin

namespace OnBytes.TestLin

open Params (IndexShape FoldeqShape LinShape)

/-- A fixed element of the extension field E for each n. The tests use it as an arbitrary one. -/
def rnd (n : Nat) : E :=
  E.mk3 (normF (UInt64.ofNat (n * 2654435761 + 12345))) (normF (UInt64.ofNat (n * n * 40503 + 7)))
    (normF (UInt64.ofNat (n * 97 + n * n * n)))

/-- The elements rnd (1000 s), .., rnd (1000 s + count - 1). -/
def rv (s count : Nat) : List E := (List.range count).map fun i => rnd (1000 * s + i)

/-- Entry j of the equality vector at z. -/
def eqAt (z : List E) (j : Nat) : E := (Tensor.eq z).entry j

/-! ## Cs.lean: where the rest lies in the new oracle message of a code switch -/

/-- Two base and two mask codes, each as (log2 of word length, message length, tail length). -/
def codes : Codes :=
  { base := #[⟨6, 8, 2⟩, ⟨6, 4, 2⟩], mask := #[⟨6, 2, 1⟩, ⟨6, 16, 1⟩] }

/-- Where the rest lies in two mask rows of 16 places: all 32 entries but one for each answer. -/
def places (answers : Nat) : SwitchPlaces :=
  SwitchPlaces.make codes (switchTargetStage 1 1 1 1 answers)

#guard (places 1).size == 31 && (places 1).pad == [31]
#guard (List.range 31).all fun i => (places 1).get i == i
#guard (places 2).size == 30 && (places 2).pad == [29, 31]
#guard (List.range 30).map (places 2).get == (List.range 29) ++ [30]
#guard switchPieces (places 1) 3 5 == [⟨0, 5, 3, 1⟩]
#guard switchPieces (places 2) 27 3 == [⟨0, 2, 27, 1⟩, ⟨2, 3, 30, 1⟩]
#guard switchPieces (places 1) 3 0 == [] && switchPieces (places 1) 3 1 == [⟨0, 1, 3, 1⟩]
#guard switchBox (places 1) 4 2 == some ⟨0, 4⟩
#guard switchBox (places 1) 2 2 == none
-- the pad's entry 29 lies between the two entries: they are two apart, which is still a box
#guard switchBox (places 2) 28 1 == some ⟨1, 28⟩
#guard switchBox (places 2) 27 1 == none
#guard cutIndex ⟨.main, 1, 2⟩ 2 5 == 3 + 2 * 4

/-- A target whose rest lies in a main row: row 1 of two main rows of eight places. -/
def inMain : SwitchTarget :=
  { shape := { code := 0, mainRows := 2, mainDeg := 3, maskRows := 0, maskCode := noId,
               answers := 1 }
    main := ⟨.main, 0, 0⟩, rest := ⟨.main, 0, 1⟩ }

-- the rest's places are the entries of row 1, in order, without the pad's
#guard
  let P := SwitchPlaces.make codes inMain
  let got := (List.range P.size).map P.get
  P.size + P.pad.length == 8 &&
  (got.all fun x => x % 2 == 1 && decide (x < 16)) &&
  ((got.zip got.tail).all fun p => decide (p.1 < p.2)) &&
  (padPlaces codes inMain.shape).all fun p => !got.contains p.index

-- a form on eight entries, carried into rows 2 and 3 of a table of four rows and eight places
#guard
  let c : Form := (Form.ofTensor (Tensor.eq (rv 1 3))).addEntry 5 (rnd 2)
  let cut : RowCut := ⟨.main, 1, 2⟩
  let lifted := switchLift c 3 cut 2 5
  lifted.fits 5 &&
    ((List.range 8).all fun j => lifted.entry (cutIndex cut 2 j) == c.entry j) &&
    (List.range 32).all fun i =>
      ((List.range 8).any fun j => cutIndex cut 2 j == i) || lifted.entry i == zeroE

/-! ## Foldeq.lean: the rows (Row, a linear equation on oracle messages) on the folded row -/

/-- A table of two rows under a code whose message length is no power of two, with a record of
two answers for each row. -/
def fold : FoldeqShape :=
  { index := { code := ⟨5, 12, 5⟩, v := 1, answers := 2, saltBytes := 40 }
    u := { code := 0, mainRows := 4, mainDeg := 3, maskRows := 0, maskCode := noId, answers := 1 }
    rowsHigh := true, leafClass := 0, columns := 3 }

/-- The folded row in oracle message number 7, which has four rows of eight places. -/
def u : FoldedRow := ⟨7, ⟨2, 3, true⟩⟩

#guard fold.index.plain == 6 && fold.index.padPlace 1 2 == 11 && fold.index.cubeBits == 4
#guard fold.tailFirst == 16 && fold.entries == 21

-- the conditions on the shapes, each with shapes that miss it
#guard fold.index.ok && !{ fold.index with v := 41 }.ok && !{ fold.index with answers := 4 }.ok
#guard fold.ok && !{ fold with columns := 0 }.ok &&
  !{ fold with u := { fold.u with mainDeg := 1 } }.ok &&
  !{ fold with u := { fold.u with answers := 0 } }.ok
#guard foldeqOk codes fold && !foldeqOk codes { fold with u := { fold.u with code := 2 } } &&
  !foldeqOk codes { fold with u := { fold.u with mainRows := 2 } }
#guard
  let key : TableKey := { record := (rv 7 4).toArray, seeds := [⟨rv 4 4, rnd 5⟩, ⟨rv 8 4, rnd 9⟩] }
  key.fits fold.index && !{ key with record := (rv 7 3).toArray }.fits fold.index &&
  !{ key with seeds := key.seeds.take 1 }.fits fold.index &&
  !{ key with seeds := [⟨rv 4 4, rnd 5⟩, ⟨rv 8 3, rnd 9⟩] }.fits fold.index

-- vectorRoom: the whole table without a sample; 0 where rows are no power of two or bits exceed 60.
-- With one answer the pad is the last place of the last row (Send.pad): entry 23 of 24, 31 of 32
#guard
  let s : OracleShape :=
    { code := 0, mainRows := 3, mainDeg := 3, maskRows := 0, maskCode := noId, answers := 0 }
  vectorRoom codes s true == 24 && vectorRoom codes s false == 0 &&
  vectorRoom codes { s with mainRows := 4 } false == 32 &&
  vectorRoom codes { s with mainRows := 2 ^ 58 } true == 0 &&
  vectorRoom codes { s with answers := 1 } true == 23 &&
  vectorRoom codes { s with mainRows := 4, answers := 1 } false == 31
#guard
  let s := fold.u
  let lay := vectorLay codes s true
  let room := vectorRoom codes s true
  decide (0 < room) && decide (room < 32) &&
  (padPlaces codes s).all fun p => p.part != .main || decide (room ≤ lay.entryAt p.index)

-- foldeqColumnRow: the generator matrix's coefficients on message and tail, 0 between and after
#guard
  match foldeqColumnRow fold 9 (rnd 3) u with
  | none => false
  | some row =>
    let at_ := fun j => row.coefficient 7 .main (u.lay.index j)
    let c := fold.index.code
    row.kind == .generator && row.target == rnd 3 &&
    ((List.range 12).all fun p => at_ p == ofF ((generatorMessage c 9).getD p 0)) &&
    ((List.range 4).all fun j => at_ (12 + j) == zeroE) &&
    ((List.range 5).all fun q => at_ (16 + q) == ofF ((generatorTail c 9).getD q 0)) &&
    (List.range 11).all fun j => at_ (21 + j) == zeroE

-- the record's row for answer 1
#guard
  let seed : SampleSeed := ⟨rv 4 4, rnd 5⟩
  let eqGamma := foldeqWeights [rnd 6]
  let record := (rv 7 4).toArray
  match foldeqRecordRow fold seed record 1 eqGamma u with
  | none => false
  | some row =>
    let at_ := fun j => row.coefficient 7 .main (u.lay.index j)
    row.kind == .plain &&
    ((List.range 6).all fun p => at_ p == eqAt seed.z p) &&
    ((List.range 3).all fun t => at_ (6 + t) == zeroE && at_ (9 + t) == mulE (rnd 5) (thetaE t)) &&
    ((List.range 20).all fun j => at_ (12 + j) == zeroE) &&
    row.target == addE (mulE (subE oneE (rnd 6)) (rnd 7001)) (mulE (rnd 6) (rnd 7003))

#guard foldeqSymbol (foldeqWeights [rnd 6]) #[3, 5] ==
  addE (mulE (subE oneE (rnd 6)) (ofF 3)) (mulE (rnd 6) (ofF 5))

/-! ## Lin.lean: the rows (Eval), (Fold) and (Dot) -/

/-- A shape for a matrix of five rows and four columns, on the table of fold at `answers := 0`. -/
def shape : LinShape :=
  { fold := { fold with index := { fold.index with answers := 0 } }
    kLo := 1, matrixRows := 5
    omega := { code := 1, mainRows := 1, mainDeg := 3, maskRows := 0, maskCode := noId }
    w := { code := 1, mainRows := 1, mainDeg := 3, maskRows := 0, maskCode := noId }
    omegaRowsHigh := false, wRowsHigh := false
    sharedSplit := {}, ownSplit := {}
    omegaLeafClass := 1, sharedSplitLeafClass := 2, wLeafClass := 0, ownSplitLeafClass := 3
    sharedMaskCode := 0, ownMaskCode := 0, masksAhead := false
    testU := [], testOmega := [], testOwn := [], testOwnOmega := []
    choice := ⟨false⟩ }

/-- How Omega and W lie: one row of eight places. -/
def flat : VectorLay := ⟨0, 3, false⟩

#guard shape.kCol == 2 && shape.kRow == 3

-- (Eval)
#guard
  let claim : LinClaim :=
    { g := [], psi := rv 10 2, masks := #[⟨4, .mask, 6, rnd 11⟩], target := rnd 12 }
  match linEvalRow shape claim 3 flat with
  | none => false
  | some row =>
    row.target == rnd 12 && row.coefficient 4 .mask 6 == rnd 11 &&
    (List.range 8).all fun j =>
      row.coefficient 3 .main j == if j < 4 then eqAt (rv 10 2) j else zeroE

-- (Fold)
#guard
  let psi := rv 13 2
  let zeta := rv 14 3
  match linFoldRow shape psi zeta u 5 flat with
  | none => false
  | some row =>
    row.target == zeroE &&
    ((List.range 8).all fun y =>
      row.coefficient 5 .main y == if y < 5 then eqAt zeta y else zeroE) &&
    (List.range 32).all fun e =>
      row.coefficient 7 .main (u.lay.index e) ==
        if e < 10 then negE (mulE (eqAt (psi.take 1) (e % 2)) (eqAt zeta (e / 2))) else zeroE

-- (Dot)
#guard
  let psi := rv 15 2
  let g := [Tensor.eq (rv 16 3) (rnd 17), Tensor.eq (rv 18 3)]
  match linDotRow shape g psi 5 flat 3 flat with
  | none => false
  | some row =>
    row.target == zeroE &&
    ((List.range 8).all fun y =>
      row.coefficient 5 .main y ==
        if y < 5 then addE (mulE (rnd 17) (eqAt (rv 16 3) y)) (eqAt (rv 18 3) y) else zeroE) &&
    (List.range 8).all fun j =>
      row.coefficient 3 .main j == if j < 4 then negE (eqAt psi j) else zeroE

#guard (linDotRow shape [Tensor.eq (rv 16 2)] (rv 15 2) 5 flat 3 flat).isNone
#guard (linEvalRow shape { psi := rv 10 3 } 3 flat).isNone
#guard (linFoldRow shape (rv 13 3) (rv 14 3) u 5 flat).isNone
#guard (linFoldRow shape (rv 13 2) (rv 14 2) u 5 flat).isNone

-- (Dot) with row weights that are written out on the rows 1 to 4, as a caller hands them in
#guard
  let psi := rv 15 2
  match (memberWeightsOnRows shape 1 (rv 19 4).toArray).bind fun g =>
      linDotRow shape g psi 5 flat 3 flat with
  | none => false
  | some row =>
    (List.range 8).all fun y =>
      row.coefficient 5 .main y == if 1 ≤ y && y < 5 then rnd (19000 + y - 1) else zeroE

/-- shape with Omega and W under G_u's code, of eight places, so that no row is split: it meets
linOk. shape itself does not: there (Fold) is split, and the split's message has no shape. -/
def oneCode : LinShape :=
  { shape with omega := { shape.omega with code := 0 }, w := { shape.w with code := 0 } }

#guard oneCode.ok && linOk codes oneCode && !shape.ok
#guard !{ oneCode with w := { oneCode.w with answers := 0 } }.ok
#guard !{ oneCode with matrixRows := 0 }.ok && !{ oneCode with matrixRows := 7 }.ok &&
  !{ oneCode with kLo := 31 }.ok &&
  !{ oneCode with omega := { oneCode.omega with maskRows := 1, maskCode := 0 } }.ok
-- Omega's one row of eight places, less its pad, has no room for eight rows of the matrix
#guard !linOk codes { oneCode with kLo := 0, matrixRows := 8 } &&
  !linOk codes { oneCode with sharedMaskCode := 2 }
#guard linMessageW oneCode == some #[⟨oneCode.w, oneCode.wLeafClass⟩] &&
  linMessageW { oneCode with masksAhead := true } == none

/-! ## Lin.lean: row weights that are written out on a stretch of rows -/

/-- The sum of the tensors' entries at row y. -/
def weightAt (l : List Tensor) (y : Nat) : E := l.foldl (fun s t => addE s (t.entry y)) zeroE

#guard (List.range 33).all fun first =>
  (List.range (33 - first)).all fun count =>
    match stretchInTheCube 5 first (rv 20 count).toArray with
    | none => false
    | some l =>
      l.all (fun t => t.ok && t.vars == 5) && decide (l.length ≤ 10) &&
      (List.range 32).all fun y =>
        weightAt l y == if first ≤ y && y < first + count then rnd (20000 + y - first) else zeroE
#guard (stretchInTheCube 5 30 (rv 20 3).toArray).isNone
#guard (memberWeightsOnRows shape 3 (rv 20 3).toArray).isNone
#guard (memberWeightsOnRows shape 3 (rv 20 2).toArray).isSome

-- a pending row as a claim, and the comparison of the pending rows with the shape
#guard
  let row := memberPendingRow [Tensor.eq (rv 21 3)] (rv 22 2) ⟨4, 6⟩ (rnd 23) (rnd 24)
  let claim := memberClaim row
  claim.psi == rv 22 2 && claim.target == rnd 24 && claim.g.length == 1 &&
  claim.masks.toList.map (fun m => (m.oracle, m.part, m.index, m.coeff)) == [(4, .mask, 6, rnd 23)]

/-- A statement whose message number 0 has mask rows only, under mask code 0, and is sampled. -/
def withMasks : Statement :=
  { codes := codes, oracles := #[{ shape := { maskRows := 2, maskCode := 0, answers := 1 } }] }

/-- A pending row that fits shape: weights on three variables, a point of two coordinates, and a
mask entry of message number o. -/
def pendingOn (o : Nat) : TensorRow :=
  memberPendingRow [Tensor.eq (rv 21 3)] (rv 22 2) ⟨o, 6⟩ (rnd 23) (rnd 24)

#guard memberRowsFit withMasks shape 0 [pendingOn 0, pendingOn 0]
-- no pending row; no such message; a mask entry of another message; a point or weights of another
-- length; a message that has main rows, is not sampled, or is under another mask code
#guard !memberRowsFit withMasks shape 0 [] && !memberRowsFit withMasks shape 1 [pendingOn 1] &&
  !memberRowsFit withMasks shape 0 [pendingOn 0, pendingOn 1] &&
  !memberRowsFit withMasks shape 0 [{ pendingOn 0 with psi := rv 22 3 }] &&
  !memberRowsFit withMasks shape 0 [{ pendingOn 0 with g := [Tensor.eq (rv 21 2)] }]
#guard [({ maskRows := 2, maskCode := 0, answers := 0 } : OracleShape),
    { maskRows := 2, maskCode := 1, answers := 1 },
    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 2, maskCode := 0, answers := 1 }].all
  fun s => !memberRowsFit { withMasks with oracles := #[{ shape := s }] } shape 0 [pendingOn 0]

end OnBytes.TestLin
