-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestTailRefusals.lean: refusals and bounds of Trees.lean and Tail.lean on public
numbers.

Many guards give a function of OnBytes/Model/Trees.lean or OnBytes/Model/Tail.lean an input on which
one of its conditions fails, and expect the refusal: a name, or none from a function that returns an
Option. Where the condition is a bound, inputs on both sides of it are tried, in most cases next to
the bound (not for t2f-columns-range). The other guards compare what a function returns with
expected numbers.

Not reached here: in shapeF, hid-tau and the length of hasU (OnBytes/Model/TestTail.lean tries
both); in piecesF, hid-call-floor and the refusals of Forest.shape, Forest.pubRun and Forest.pubAsk;
the refusal inside t2BL; in addTreesF, internal-t2f-map and the test that there is no U4
(OnBytes/Model/TestTailMore.lean tries both, on made-up states); in t2AddN, t2AddP and t2Plan, a
list that addTreesF has not begun and a list whose length is not that of Fork.trees.

The names that are expected were read off the C++ source at the condition's counterpart
(verifier/src/vf_subproof_segment.h, vf_smallness_test_members.inc), without the prefix that the C++
puts before some of them and without the matrix's name that it appends to shape-matrix and
shape-foreign (Tail.names). No C++ program printed them. The expected numbers were worked out by
hand; none was taken from the output of the Lean functions. The condition on the length of nU has no
counterpart: the C++ declares nU as an array of three. No proof is read. The terms are explained in
OnBytes/Model/Tail.lean (the docstring of HTailF2 says where). The file is not imported by the
program. -/
import OnBytes.Model.Tail

namespace OnBytes.Model.TestTailRefusals

open OnBytes OnBytes.Model

/-- The name of a refusal; the empty string if there is none. -/
def nameOf {α : Type} (r : Except String α) : String :=
  match r with
  | .error e => e
  | .ok _ => ""

/-- A matrix that the sub-proof commits to. -/
def own (m k : Nat) : TMat := { name := "x", m := m, k := k }

/-- A matrix of an earlier sub-proof: the whole of array j of the list of such arrays. -/
def earlier (j m k : Nat) : TMat := { name := "y", m := m, k := k, kind := 1, foreign := some j }

/-- An array of an earlier sub-proof, for a matrix with m rows of cells and K columns. -/
def array (m K : Nat) : T2Foreign := { name := "PXf0", K := K, a := 2, m := m }

/-- The shape for a list of matrices, at tau = 160. Of U1 to U3 the sub-proof has only U3. -/
def shapeOf (m : Array TMat) (txOf : Array (Option Nat)) (f : Array T2Foreign := #[]) :
    Except String HTailF2 :=
  ({} : HTailF2).shape m txOf f #[false, false, true, false] 160

/-! ## shapeF -/

#guard nameOf (shapeOf #[own 6 2] #[none]) == ""
#guard nameOf (shapeOf #[own 6 2] #[]) == "internal-t2f-lists"
#guard nameOf (({} : HTailF2).shape #[own 6 2] #[none] #[] #[false, false, true, true] 160) ==
  "internal-t2f-lists"
-- The arrays PX_i are numbered in the order of the list.
#guard nameOf (shapeOf #[own 6 2, own 6 3] #[some 0, some 1]) == ""
#guard nameOf (shapeOf #[own 6 2, own 6 3] #[some 1, some 0]) == "internal-t2f-TX-order"
#guard nameOf (shapeOf #[own 6 2, own 6 3] #[none, some 1]) == "internal-t2f-TX-order"
#guard (shapeOf #[own 6 2, own 6 3, own 3 4] #[some 0, none, some 1]).toOption.any fun tl =>
  tl.pxMat == #[0, 2] && tl.pkMat == #[1] && tl.kTX == #[2, 4] && tl.off == #[0, 6, 12] &&
    tl.mz == 15 && tl.gtTree == #[2, 1, 3] && tl.ix.ZZ == 4 && tl.ix.BZ == 5 && tl.ix.count == 6
-- A list has fewer than 256 matrices.
#guard nameOf (shapeOf (Array.replicate 255 (own 3 1)) (Array.replicate 255 none)) == ""
#guard nameOf (shapeOf (Array.replicate 256 (own 3 1)) (Array.replicate 256 none)) == "plan-link"
#guard nameOf (shapeOf #[own 0 2] #[none]) == "shape-matrix"
#guard nameOf (shapeOf #[own 6 0] #[none]) == "hid-k-range"
#guard nameOf (shapeOf #[own 6 8191] #[none]) == ""
#guard nameOf (shapeOf #[own 6 8192] #[none]) == "hid-k-range"
-- A matrix of an earlier sub-proof is the whole of its owner's array.
#guard nameOf (shapeOf #[own 6 2, earlier 0 9 4] #[none, none] #[array 9 4]) == ""
#guard nameOf (shapeOf #[own 6 2, { earlier 0 9 4 with foreign := none }] #[none, none]
  #[array 9 4]) == "shape-foreign"
#guard nameOf (shapeOf #[own 6 2, earlier 1 9 4] #[none, none] #[array 9 4]) == "shape-foreign"
#guard nameOf (shapeOf #[own 6 2, earlier 0 9 3] #[none, none] #[array 9 4]) == "shape-foreign"
#guard nameOf (shapeOf #[own 6 2, earlier 0 8 4] #[none, none] #[array 9 4]) == "shape-foreign"
#guard nameOf (shapeOf #[own 6 2, { earlier 0 9 4 with ttOff := 1 }] #[none, none]
  #[array 9 4]) == "shape-foreign"
#guard nameOf (shapeOf #[own 6 2, { earlier 0 9 4 with wp := 1 }] #[none, none]
  #[array 9 4]) == "shape-foreign"
-- The arrays of earlier sub-proofs are used in their order, each once, and none is left over.
#guard nameOf (shapeOf #[earlier 1 9 4, earlier 0 9 4] #[none, none] #[array 9 4, array 9 4]) ==
  "internal-t2f-ZF-order"
#guard nameOf (shapeOf #[earlier 0 9 4, earlier 0 9 4] #[none, none] #[array 9 4]) ==
  "internal-t2f-ZF-order"
#guard nameOf (shapeOf #[own 6 2] #[none] #[array 9 4]) == "internal-t2f-ZF-order"
#guard (shapeOf #[own 6 2, earlier 0 9 4] #[none, none] #[array 9 4]).toOption.any fun tl =>
  tl.gtTree == #[1, 4] && tl.ix.FT == #[4] && tl.ix.count == 5 &&
    (tl.plFor.map (·.matrix)) == #[some (0, 4, 9)]
#guard nameOf (shapeOf #[{ own 6 2 with kind := 2 }] #[none]) == "t2f-weight-class"
-- ZZ has 2 mz columns, which must fit 32 bits.
#guard nameOf (shapeOf #[own (2 ^ 31) 1] #[none]) == "t2f-columns-range"

/-! ## piecesF: the blocks of ZZ's rows -/

/-- The shape of one small matrix at another tau. -/
def atTau (tau : Nat) : Except String HTailF2 :=
  ({ tau := tau } : HTailF2).shape #[own 6 2] #[none] #[] #[false, false, true, false] tau

#guard nameOf (atTau 128) == "" && nameOf (atTau 160) == "" && nameOf (atTau 192) == ""
-- 224 = 128 + 64 + 32 would need three blocks.
#guard nameOf (atTau 224) == "internal-t2f-blocks"
#guard nameOf (atTau 0) == "internal-t2f-blocks"
#guard (atTau 128).toOption.any fun tl => tl.zzBlocks == 1 && tl.zzRowReads == 2 && tl.stepF == 128
#guard (atTau 192).toOption.any fun tl => tl.blocks == #[(0, 128), (128, 64)] && tl.stepF == 256

/-! ## The records of shared matrices -/

/-- Two matrices that other sub-proofs read, and one of an earlier sub-proof. -/
def shared : Except String HTailF2 :=
  shapeOf #[{ own 6 2 with name := "qa" }, { own 6 3 with name := "xbO" }, earlier 0 9 4]
    #[some 0, some 1, none] #[array 9 4]

#guard nameOf shared == ""
#guard nameOf (shared.bind fun tl => tl.borderMeans 0 7 3) == ""
#guard nameOf (shared.bind fun tl => tl.borderMeans 1 7 3) == "internal-border-count"
#guard nameOf (shared.bind fun tl => (tl.borderMeans 0 7 3).bind fun tl => tl.borderMeans 0 7 3) ==
  "internal-border-count"
#guard (shared.bind fun tl => tl.borderMeans 0 7 3).toOption.any fun tl =>
  (tl.plFor.map fun p => (p.owner, p.rootIndex)) == #[(some 7, some 3)]
-- Before the list of arrays is made the owner's record is not complete.
#guard nameOf (shared.bind fun tl => (tl.ownerIs 5).ownEntry "qa") == "internal-border-count"

/-- The example shared, with its list of arrays. aTX: the numbers of readers of PX0 and PX1, plus 1.
-/
def sharedListed (aTX : Array Nat := #[2, 3]) (nU : Array Nat := #[0, 0, 4]) (hbLine : Nat := 128)
    (T : Tail2 := {}) : Except String (HTailF2 × Fork × Tail2) :=
  shared.bind fun tl => (tl.ownerIs 5).addTrees {} T nU aTX 100 hbLine

#guard nameOf (sharedListed) == ""
#guard (sharedListed).toOption.any fun (tl, _, _) =>
  ((tl.ownEntry "qa").toOption.map fun p => (p.owner, p.rootIndex, p.matrix, p.hb, p.K)) ==
      some (some 5, some 0, some (0, 2, 6), 100, 2) &&
    ((tl.ownEntry "stream").toOption.map fun p => (p.rootIndex, p.matrix, p.mS)) ==
      some (some 1, some (0, 3, 6), 2)
#guard nameOf ((shapeOf #[own 6 2] #[some 0]).bind fun tl => tl.ownEntry "qa") ==
  "internal-border-count"

/-! ## addTreesF -/

#guard nameOf (sharedListed #[2]) == "internal-t2f-lists"
#guard nameOf (sharedListed #[2, 3] #[0, 0]) == "internal-t2f-lists"
#guard nameOf (sharedListed #[2, 3] #[0, 0, 4] 160) == ""
#guard nameOf (sharedListed #[2, 3] #[0, 0, 4] 161) == "policy-tau-hb"
-- The list must be empty when the arrays are added.
#guard nameOf ((sharedListed).bind fun (tl, F, T) => tl.addTrees F T #[0, 0, 4] #[2, 3] 100 128) ==
  "internal-t2-order"
#guard (sharedListed).toOption.any fun (tl, F, T) =>
  (F.trees.map fun X => (X.name, X.R, X.K, X.rows.size)) ==
      #[("U3", 1, 4, 1), ("PX0", 2, 2, 1), ("PX1", 2, 3, 1), ("ZZ", 160, 42, 6),
        ("BZ", 32, 2048, 3), ("PXf0", 3, 4, 1)] &&
    T.nt.size == 6 && T.link && tl.nUF == #[0, 0, 4] && tl.tabLen == #[0, 4] &&
    (tl.shp.map fun s => (s.m, s.k, s.mS)) == #[(6, 2, 2), (6, 3, 2), (9, 4, 3)]

/-! ## The list of arrays (Trees.lean) -/

-- No array is added after the list is closed (t2Plan), and the list is closed once.
#guard nameOf ((sharedListed).bind fun (_, F, T) => t2Plan F T) == ""
#guard nameOf ((sharedListed).bind fun (_, F, T) =>
  (t2Plan F T).bind fun T => t2AddN F T "more" 1 1 3 1 false 1) == "internal-t2-order"
#guard nameOf ((sharedListed).bind fun (_, F, T) =>
  (t2Plan F T).bind fun T => t2AddP F T "more" 6 2 0 1 false) == "internal-t2-order"
#guard nameOf ((sharedListed).bind fun (_, F, T) => (t2Plan F T).bind fun T => t2Plan F T) ==
  "internal-t2-order"
#guard nameOf ((sharedListed).bind fun (_, F, T) => t2AddP F T "more" 6 2 1 1 false) ==
  "plan-w-zero"

/-! ## Places, tables and counts -/

/-- True if sharedListed gives a list of arrays and the test holds on it. -/
def listed (test : HTailF2 → Fork → Bool) : Bool :=
  (sharedListed).toOption.any fun (tl, F, _) => test tl F

/-- A table on U3 for matrix mat, in segments of len rows of cells, from entry start on. -/
def table (mat len start : Nat) : HFun :=
  { mat := mat, len := len, phi := Array.replicate len oneE, tree := 2, start := start }

-- zzCol: matrix 1 begins at row 6 of 21 rows of cells; the high digits begin at column 21.
#guard listed fun tl _ => tl.zzCol 1 0 0 == some 6 && tl.zzCol 1 1 5 == some 32 &&
  tl.zzCol 2 1 8 == some 41
#guard listed fun tl _ => tl.zzCol 1 0 6 == none && tl.zzCol 3 0 0 == none && tl.zzCol 0 2 0 == none
-- tabAt: matrix 1 has three columns; segments of three rows make two segments.
#guard listed fun tl _ => tl.tabAt (table 1 3 10) 0 0 == some 10 &&
  tl.tabAt (table 1 3 10) 2 1 == some 15
#guard listed fun tl _ => tl.tabAt (table 1 3 10) 3 0 == none &&
  tl.tabAt (table 1 3 10) 0 2 == none && tl.tabAt (table 3 3 10) 0 0 == none &&
  tl.tabAt (table 1 0 10) 0 0 == none
-- The list of tables is closed once.
#guard listed fun tl _ => tl.funOpen && (tl.closeFuns #[table 0 6 0]).any fun tl =>
  !tl.funOpen && (tl.closeFuns #[]).isNone && tl.funsHeld #[table 0 6 0] &&
    !tl.funsHeld #[table 0 6 1] && !tl.funsHeld #[] && !tl.funsHeld #[table 0 6 0, table 0 6 0]
#guard listed fun tl _ => !tl.funsHeld #[]
-- Two tables are the same only if all five fields agree.
#guard HTailF2.sameFun (table 0 6 0) (table 0 6 0) &&
  [{ table 0 6 0 with mat := 1 }, { table 0 6 0 with len := 5 }, { table 0 6 0 with tree := 0 },
    { table 0 6 0 with start := 1 }, { table 0 6 0 with phi := Array.replicate 6 zeroE }].all
    fun other => !HTailF2.sameFun (table 0 6 0) other
#guard listed fun tl _ =>
  tl.groupsRun == 0 && ({ tl with heard := some default } : HTailF2).groupsRun == 1
-- Before the claims are added there is no count of equations.
#guard listed fun tl _ => tl.equationsLaidF == none
-- equationsF: the matrices take 256 * 2, 256 * 2 and 256 * 4 indices, each of five reads 256.
#guard listed fun tl _ => tl.equationsF 5 == 256 * (2 + 2 + 4 + 5) && tl.lins 5 == tl.lins 0 + 5
#guard listed fun tl _ => tl.firstAgain 0 == 0 && tl.firstAgain 1 == 512 &&
  tl.firstAgain 2 == 1024 && tl.firstAgain 3 == 2048

/-! ## The batching element's powers -/

/-- The sub-proof's state with the batching element 3 drawn and a plan of ten claims. added: the
number of claims added so far. -/
def drawn (F : Fork) (added : Nat := 0) : Fork :=
  { F with theta := ofNat 3, thetaDrawnF := true, planClaimsF := 10, nClaim := added }

#guard listed fun tl F => (tl.powersF F).isNone
#guard listed fun tl F => (tl.powersF { drawn F with planClaimsF := 0 }).isNone
#guard listed fun tl F => (tl.powersF (drawn F)).any fun tl =>
  tl.eqFirst == #[0, 512, 1024, 2048] && tl.vt.size == 160 && tl.vp == tl.vt &&
    tl.vt.getD 4 zeroE == ofNat 81 && (tl.rowX.map (·.size)) == #[2, 2, 3] &&
    (tl.rowX.getD 2 #[]).getD 1 zeroE == powE (ofNat 3) 256 && tl.loX == Array.replicate 3 #[oneE]
-- Each symbol array holds one row of symbols in each row, and ceil(m / 3) rows.
#guard listed fun tl F => (tl.powersF (drawn F)).isSome &&
  [fun (s : ShP) => { s with J := 2 }, fun s => { s with Rd := 1 }, fun s => { s with R := 4 },
    fun s => { s with Rr := 4 }, fun s => { s with mS := 4, R := 4, Rr := 4 }].all fun change =>
    (({ tl with shp := tl.shp.modify 2 change } : HTailF2).powersF (drawn F)).isNone
-- leadF: claim number 4 of 10 is brought from 3^4 to 3^(10 + 7).
#guard listed fun _ F => HTailF2.leadF (drawn F 4) 7 == some (powE (ofNat 3) 13)
#guard listed fun _ F => HTailF2.leadF (drawn F 9) 0 == some (ofNat 3) &&
  HTailF2.leadF (drawn F 10) 0 == none

/-! ## Sums over the drawn matrix -/

-- One column with the entries 1, -1, 0, 1 under the weights 2, 3, 5, 7.
#guard HTailF2.foldColumn #[9, 9, 1, -1, 0, 1] 2 4 #[ofNat 2, ofNat 3, ofNat 5, ofNat 7] == ofNat 6
#guard HTailF2.foldColumn #[1, 1, 1] 0 2 #[ofNat 2, ofNat 3, ofNat 5] == ofNat 5
#guard listed fun tl F => (tl.powersF (drawn F)).any fun tl =>
  let tl := { tl with
    cfF := Array.replicate (9 * 160) 1, cfFirst := #[0, 2, 5, 9],
    gamX := Array.replicate 3 #[], gamV := Array.replicate 3 #[] }
  (tl.foldSums 3).isNone && !tl.foldAllTakenF && (tl.foldSums 1).any fun tl =>
    (tl.foldSums 1).isNone && !tl.foldAllTakenF && (tl.gamX.map (·.size)) == #[0, 3, 0] &&
      tl.gamV == tl.gamX && (tl.gamX.getD 1 #[]).getD 2 zeroE == sumE tl.vt

#guard listed fun tl _ =>
  ({ tl with foldTakenF := #[true, true, true] } : HTailF2).foldAllTakenF &&
    !({ tl with foldTakenF := #[true, false, true] } : HTailF2).foldAllTakenF &&
    !({ tl with foldTakenF := #[true, true] } : HTailF2).foldAllTakenF

/-! ## The places that the claim on the key vectors reads -/

-- Trees of eight places. The call has two trees, numbers 3 and 4 of five.
#guard HTailF2.placesRead 3 1 3 3 (Array.replicate 5 0) 6 5 == some #[0, 0, 0, 2, 3]
#guard HTailF2.placesRead 3 1 3 3 (Array.replicate 5 0) 0 16 == some #[0, 0, 0, 8, 8]
#guard HTailF2.placesRead 3 1 3 3 (Array.replicate 5 0) 0 17 == none
#guard HTailF2.placesRead 3 1 3 3 (Array.replicate 5 0) 16 1 == none
#guard HTailF2.placesRead 3 1 3 3 (Array.replicate 5 0) 16 0 == some (Array.replicate 5 0)
-- Too few steps for the places that are left.
#guard HTailF2.placesRead 3 1 3 1 (Array.replicate 5 0) 6 5 == none

/-! ## The tables tile U3 -/

-- U3 has four entries. Matrix 0 has two columns: one table in two segments fills it.
#guard listed fun tl _ => tl.tablesTile #[table 0 3 0] 2 == some 2
#guard listed fun tl _ => tl.tablesTile #[table 0 6 2, table 0 6 0] 2 == some 2
#guard listed fun tl _ => tl.tablesTile #[table 0 6 0] 2 == none
#guard listed fun tl _ => tl.tablesTile #[table 0 6 0, table 0 6 1] 2 == none
#guard listed fun tl _ => tl.tablesTile #[table 0 6 0, table 0 6 3] 2 == none
#guard listed fun tl _ => tl.tablesTile #[table 0 6 1, table 0 6 3] 2 == none
#guard listed fun tl _ => tl.tablesTile #[table 0 3 0, table 0 6 4] 2 == none
-- No table is on U1, whose part is empty.
#guard listed fun tl _ => tl.tablesTile #[table 0 3 0] 0 == some 0
#guard listed fun tl _ => tl.tablesTile #[{ table 0 6 0 with tree := 0 }] 0 == none

/-! ## Marks on the entries that the reads read -/

/-- No entry of U3 is marked. -/
def noMark : Array (Array Bool) := #[#[], Array.replicate 4 false]

#guard listed fun tl _ =>
  tl.markRead (table 0 3 0) 1 noMark == some #[#[], #[false, true, false, true]]
#guard listed fun tl _ => ((tl.markRead (table 0 3 0) 1 noMark).bind
  fun rd => tl.markRead (table 0 3 0) 1 rd) == none
#guard listed fun tl _ => tl.markRead (table 0 3 1) 1 noMark == none
#guard listed fun tl _ => tl.markRead (table 0 3 0) 2 noMark == none
#guard listed fun tl _ => tl.markRead { table 0 3 0 with tree := 0 } 0 noMark == none

/-! ## Small functions -/

#guard HTailF2.isPow2 1 && HTailF2.isPow2 64 && !HTailF2.isPow2 0 && !HTailF2.isPow2 96
#guard HTailF2.allDistinct [3, 1, 2] && !HTailF2.allDistinct [3, 1, 3] && HTailF2.allDistinct []
#guard HTailF2.neighboursDiffer [oneE, zeroE, oneE] && !HTailF2.neighboursDiffer [zeroE, oneE, oneE]
#guard HTailF2.leE (E.mk3 1 9 9) (E.mk3 2 0 0) && HTailF2.leE (E.mk3 1 1 9) (E.mk3 1 2 0) &&
  HTailF2.leE (E.mk3 1 1 1) (E.mk3 1 1 1) && !HTailF2.leE (E.mk3 1 1 2) (E.mk3 1 1 1) &&
  !HTailF2.leE (E.mk3 1 2 0) (E.mk3 1 1 9) && !HTailF2.leE (E.mk3 2 0 0) (E.mk3 1 9 9)
#guard HTailF2.powersAgain (ofNat 2) 3 5 == #[ofNat 1, ofNat 8, ofNat 64, ofNat 512, ofNat 4096]
#guard (HTailF2.powersAgain (ofNat 3) 2 300).getD 299 zeroE == powE (ofNat 3) 598
#guard HTailF2.squares (ofNat 3) 3 == #[ofNat 3, ofNat 9, ofNat 81]
#guard HTailF2.highDigit (ofNat 3) == ofNat 3072
#guard (HTailF2.lessBeta (ofNat 3)).const == subE zeroE (ofNat (3 * 2 ^ 17))
#guard noneZero #[oneE, zeroE, oneE, oneE] 2 2 && !noneZero #[oneE, zeroE, oneE, oneE] 1 2 &&
  !noneZero #[oneE, oneE] 1 2
#guard sumE #[ofNat 2, ofNat 3, ofNat 5] == ofNat 10
-- wants: at tau = 160 two blocks, so four pieces; at tau = 224 the rest, 96, is no power of two.
#guard listed fun tl _ => (tl.wants.map fun w => (w.1, w.2.map fun x => (x.call, x.i, x.row, x.r0,
  x.Rp, x.c0, x.Cp))) == some (2, [(0, 0, 0, 0, 128, 0, 21), (0, 1, 1, 128, 32, 0, 21),
    (1, 0, 2, 0, 128, 21, 21), (1, 1, 3, 128, 32, 21, 21)])
#guard listed fun tl _ => ({ tl with tau := 224 } : HTailF2).wants.isNone
#guard listed fun tl _ => (({ tl with tau := 128 } : HTailF2).wants.map (·.1)) == some 1

end OnBytes.Model.TestTailRefusals
