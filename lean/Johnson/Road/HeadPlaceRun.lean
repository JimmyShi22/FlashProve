-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadPlaceRun.lean: where the cells of the output head's matrices stand: the verifier's
tables of reads against the library's places, by evaluation at the full-size example.

Everything here is a run. A line "#guard" is evaluated when this file is compiled, by Lean's
interpreter, and the compilation fails if the value is not true. It is no theorem, and it says
nothing of other numbers.

What is run. publicOf (OnBytes/Model/VerifyPublic.lean) on the parameter file and the scale file of
prover/examples/target_full_f2, as Johnson/Road/FormsKeysRunK.lean writes them out. Then the
verifier's own tablesOf (OnBytes/Model/HeadTables.lean) on the head's numbers, layout and plan that
publicOf returns, with made-up points of the lengths that the check gives them.

What is compared with what.
 1. numbersHP: the sizes of the head's matrices in the verifier's layout and in its plan's list of
    matrices against the library's n1, n2, perCol, nFeat (Inst/Model/Head/Index.lean), and the
    verifier's record of the borrowed stream against the library's matrix x.
 2. tensorsHP: the first feature of each tensor in the verifier's layout against the library's
    features fNw, fRn, fD1, fD2, fEx, fNrm, fX, at the first and the last index of each limb.
 3. orderHP: in each of the twelve tables on hf, the stream, hd and hr, the places that the
    smallness test's tabAt gives, taken part by part, column by column and run by run, are the
    table's entries in rising order, all of them.
 4. placesHP: for every entry of these tables and every feature of its run of rows, at the first and
    the last position: the library's place of that feature (Name.place of Cm/SegLayout.lean; ownX
    for the stream) is the row on which the table's weight stands, in the slot that has the number
    of the table's matrix in the head's list, and the table's column. All 1,232,896 features of
    hf, all 25,600 of the stream, all 10,240 of hd and all 120 of hr are gone through, each at two
    of the 1,024 positions. For the stream the library's place lies in the lender's segment, and
    the matrix stands in the lender's list under a number of its own; that the head's number for
    its copy, 7, is the library's slot there is a coincidence of this example's sizes
    (Johnson/Road/HeadPlaceCtl.lean has the three numbers).
 5. readsHP: the array of reads in the plan, its number of columns, and the length of the reads.
 6. fullHP: the nine public numbers of the record FullH (Johnson/Road/HeadPlace.lean), as the
    verifier reads them from the parameter file.
 7. cellsHP: the definition cellsH of Johnson/Road/HeadPlace.lean against the tables: for every
    entry and every feature of its run, at the first and the last position, cellsH reads the matrix,
    the row and the column on which the table's weight stands.
 8. madeHP: layout and planH2, called as publicOf calls them, return what publicOf hands on, as far
    as sizes, the list of matrices and the arrays of the reads go.

What comes out. All of this agrees. One number beside it differs, and is kept here as a number:
the matrix bH of the lookup's counts has 384 columns in the verifier's plan, 64 for each of the six
calls, and 576 in the library's n2, 64 for each of the nine trees. bH holds no cell of the library's
record, and no place of Cm/SegLayout.lean lies in it.

Which name of a table stands for which matrix of the library is said here by hand (mxHP): the
letters before the sign @.

The guard holds numbers that a first run printed; where it does, it shows that the program says the
same twice. Controls with planted faults are in
Johnson/Road/HeadPlaceCtl.lean.

What is not claimed. Nothing on the three tables of bH but their lengths. Nothing on what a table's
weights are. The points are made up; no proof is read. The program does not import this file.
-/
import Johnson.Road.FormsKeysRunK
import Johnson.Road.HeadPlace
import OnBytes.Model.HeadTables

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model (HFun HTailF2 lastOf)
open OnBytes.Model.Verify (publicOf Public borderOf)
open OnBytes.Model.Head (Heard Tables tablesOf Covered callNo)
open Inst.Model.Head (Mx n1 n2 perCol nFeat colOf rowOf fX fNw fRn fD1 fD2 fEx fNrm)
open Cm.Seg (Name ownX)

/-- What the verifier holds when it fixes the head's tables, as far as tablesOf reads it: made-up
points, each of the length that the check gives it; each call's point is made from the lookup's
point as the lookup makes it (Forest.pad in OnBytes/Model/Look.lean). -/
def heardHP (h : Model.Head.Shape) (L : Model.Head.HL) : Heard :=
  let fs := L.fs
  let zx := elemsR 2000 fs.dT
  let zy := elemsR 2100 fs.rK
  { win := #[],
    g1 := { shape := fs, leaves := {}, zx := zx, zy := zy,
            zk := (Array.range fs.NC).map fun c =>
              zy.extract (fs.rK - fs.iota.getD c 0) zy.size ++ zx,
            zb0 := elemsR 2200 (fs.kT + fs.cK + 5), zb1 := elemsR 2300 (fs.kT + fs.cK + 5) },
    Zl := (lastOf zx h.la).toOption.getD #[], PV := elemsR 2500 h.lt, sW := 0, gp := #[],
    wpl := { r := elemsR 2800 (h.lPd + h.lt) }, sPv := 0, omV := #[],
    tV := { r := elemsR 2900 h.lt }, tN := { r := elemsR 3000 h.lt },
    tH := { r := elemsR 3100 h.lt }, rs := #[],
    qN := (callNo L "NF").getD 0, qH := (callNo L "HD0").getD 0 }

/-- The covered positions of a request for the next token: the last position alone, no position with
a cost. -/
def covHP (T : ℕ) : Covered :=
  { tokv := Array.replicate T 0, hOn := (Array.range T).map fun t => t + 1 == T,
    hWin := Array.replicate T 0, hOnC := Array.replicate T false, hRC := 0 }

/-- The head's tables at an example's files: the verifier's own tablesOf, run from the plan's list
of arrays in a dry context. -/
def tablesHP (X : Public) : Option Tables :=
  match tablesOf X.hS X.HLy X.H (covHP X.hS.T) (heardHP X.hS X.HLy) X.H.Fp
      { ch := { dry := true, entries := [] } } with
  | .ok r => some r.1.1
  | .error _ => none

/-- 1. The sizes: for hf, hd, hr and the stream the rows of a part, the columns of all parts, the
features of a column and the features in use, the verifier's and the library's. Then the plan's list
of matrices, and the number that the smallness test keeps of them. -/
def numbersHP (X : Public) : List (ℕ × ℕ) × List (String × ℕ × ℕ) × ℕ :=
  let h := X.hS
  let L := X.HLy
  let b := borderOf X.y
  ([(L.m, n1 .hf), (h.NHf * L.k, n2 .hf), (L.m / h.T, perCol .hf), (L.feat, nFeat .hf),
    (L.mD, n1 .hd), (L.kD, n2 .hd), (L.mD / h.T, perCol .hd), (2 * h.d, nFeat .hd),
    (L.mR, n1 .hr), (L.kR, n2 .hr), (L.mR / h.T, perCol .hr), (Model.ledNRH h.XL, nFeat .hr),
    (b.mxb, n1 .x), (b.kxb, n2 .x), (b.mxb / h.T, perCol .x), (b.nl * b.cnt * b.J, nFeat .x),
    (L.k, Cm.Seg.colsHead), (h.T, Inst.Model.Head.nT), (h.d, Inst.Model.Head.nD),
    (h.V, Inst.Model.Head.nV), (L.JV, Inst.Model.Head.nV), (h.S2, 64)],
   X.H.tl.mats.toList.map fun M => (M.name, M.m, M.k), X.H.tl.NM)

/-- 2. The tensors: limb l of the entry with the index j of each tensor, as the verifier's forms
count its feature, against the library's feature; at the first and the last index of each limb. -/
def tensorsHP (X : Public) : Bool :=
  let h := X.hS
  let L := X.HLy
  let b := borderOf X.y
  let ends (n : ℕ) : List ℕ := [0, 1, n / 2, n - 1]
  ((List.range 2).all fun l => (ends h.d).all fun j =>
      L.oAw + l * h.d + j == fNw l j && L.oRa + l * h.d + j == fRn l j &&
        l * h.d + j == fNrm l j) &&
    ((List.range 2).all fun l => (ends h.V).all fun v => L.oD1 + l * L.JV + v == fD1 l v) &&
    ((ends h.V).all fun v => L.oD2 + v == fD2 v) &&
    ((List.range 3).all fun l => (ends h.V).all fun v => L.oE + l * L.JV + v == fEx l v) &&
    ((List.range 5).all fun l => (ends h.d).all fun j => b.cell l j == fX l j) &&
    b.nl == 5

/-- Which matrix of the library a table's name stands for: the letters before the sign @. -/
def mxHP (nm : String) : Option Mx :=
  match (nm.splitOn "@").head? with
  | some "hf" => some .hf
  | some "hd" => some .hd
  | some "hr" => some .hr
  | some "xbL" => some .x
  | _ => none

/-- The library's place of feature φ of a matrix at position i: segment, row, column. -/
def placeHP : Mx → ℕ → ℕ → ℕ × ℕ × ℕ
  | .hf, φ, i => (Name.hf φ i).place
  | .hd, φ, i => (Name.hd φ i).place
  | .hr, φ, i => (Name.hr φ i).place
  | _, φ, i => (ownX φ i).place

/-- The records of the parts of the table that begins at entry tb and has len entries. -/
def partsHP (t : Tables) (tb len : ℕ) : List HFun :=
  t.funs.toList.filter fun Fn => tb ≤ Fn.start && Fn.start < tb + len

/-- The entries of a table, part by part, column by column, run by run: the record, the column, the
run, and the place that the smallness test gives. -/
def entriesHP (tl : HTailF2) (fns : List HFun) : List (HFun × ℕ × ℕ × Option ℕ) :=
  fns.flatMap fun Fn =>
    let M := tl.mats.getD Fn.mat {}
    (List.range M.k).flatMap fun c =>
      (List.range (M.m / Fn.len)).map fun sg => (Fn, c, sg, tl.tabAt Fn c sg)

/-- 3. The order of the entries, for every table that mxHP knows; with the number of such tables.
-/
def orderHP (X : Public) (t : Tables) : Bool × ℕ :=
  let ts := t.tab.filter fun e => (mxHP e.1).isSome
  (ts.all fun (_, tb, len) =>
    (entriesHP X.H.tl (partsHP t tb len)).map (·.2.2.2) ==
      (List.range len).map fun e => some (tb + e), ts.length)

/-- 4. The places. For every entry of every table that mxHP knows, every feature r of its run and
the positions 0 and T - 1: the library's place of feature e (len / T) + r is (segment, slot 2^16 +
row, column) with the row on which weight number r T + i of the table stands, the table's column,
and as slot the number of the table's matrix in the verifier's list. The segment is 24 for the
head's own matrices and 22 for the stream. -/
def placesHP (X : Public) (t : Tables) : Bool :=
  let T := X.hS.T
  t.tab.all fun (nm, tb, len) =>
    match mxHP nm with
    | none => true
    | some mx =>
      (entriesHP X.H.tl (partsHP t tb len)).all fun (Fn, c, sg, pos) =>
        match pos with
        | none => false
        | some p =>
          (List.range (Fn.len / T)).all fun r =>
            [0, T - 1].all fun i =>
              placeHP mx ((p - tb) * (Fn.len / T) + r) i ==
                (if mx == .x then 22 else 24, Fn.mat * 2 ^ 16 + (sg * Fn.len + r * T + i), c)

/-- 5. The array of reads in the plan: its number in the list of arrays, the number of its columns,
the number of its rows, and the length of the reads by the plan and by the tables. -/
def readsHP (X : Public) (t : Tables) : Option (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (X.H.tl.ix.U.getD 2 none).map fun iU3 =>
    (iU3, ((X.H.Fp.trees[iU3]?).map (·.K)).getD 0, ((X.H.Fp.trees[iU3]?).map (·.R)).getD 0,
      X.H.nU.getD 2 0, t.p)

/-- 6. The nine numbers of FullH: lt, la, d, V, XL, lmhf, NHf, lmhd, lmhr. -/
def fullHP (X : Public) : List ℕ :=
  let h := X.hS
  [h.lt, h.la, h.d, h.V, h.XL, h.lmhf, h.NHf, h.lmhd, h.lmhr]

/-- 7. cellsH against the tables. The entries of the matrices are taken to be their own places:
number in the list, row, column. For every entry of every table that mxHP knows, every feature r of
its run and the positions 0 and T - 1: cellsH has at feature e (len / T) + r the place on which
weight number r T + i of the table stands. -/
def cellsHP (X : Public) (t : Tables) : Bool :=
  let T := X.hS.T
  let cs := cellsH X.hS X.HLy (borderOf X.y) fun a r c => (a, r, c)
  t.tab.all fun (nm, tb, len) =>
    match mxHP nm with
    | none => true
    | some mx =>
      let cell : ℕ → ℕ → ℕ × ℕ × ℕ :=
        match mx with
        | .hf => cs.hf
        | .hd => cs.hd
        | .hr => cs.hr
        | _ => cs.x
      (entriesHP X.H.tl (partsHP t tb len)).all fun (Fn, c, sg, pos) =>
        match pos with
        | none => false
        | some p =>
          (List.range (Fn.len / T)).all fun r =>
            [0, T - 1].all fun i =>
              cell ((p - tb) * (Fn.len / T) + r) i == (Fn.mat, sg * Fn.len + r * T + i, c)

/-- 8. The record MadeH of Johnson/Road/HeadReads.lean, as far as a run can hold it. First: layout,
called as publicOf calls it, returns, with the sizes of the layout that publicOf hands on. Second:
planH2, called as publicOf calls it, returns a plan whose record of the smallness test has the list
of matrices, its length and the arrays of the reads of the plan that publicOf hands on, and the same
lengths of the reads. -/
def madeHP (X : Public) : Bool × Bool :=
  let sizes (L : Model.Head.HL) : List ℕ :=
    [L.JV, L.JVa, L.oE, L.feat, L.filled, L.k, L.m, L.oAw, L.oRa, L.oD1, L.oD2, L.fillD, L.kD,
      L.mD, L.fillR, L.kR, L.mR, L.kb]
  (match Model.Head.layout X.hS X.y.tauFC with
    | .ok L => sizes L == sizes X.HLy
    | .error _ => false,
   match Model.Head.planH2 X.P.settings X.hS X.HLy (borderOf X.y) X.owner X.y.NGr X.P.lkW with
    | .ok H0 => H0.tl.mats == X.H.tl.mats && H0.tl.NM == X.H.tl.NM &&
        H0.tl.ix.U == X.H.tl.ix.U && H0.nU == X.H.nU
    | .error _ => false)

/-- The whole run. The last members: the columns of bH, the verifier's and the library's; madeHP.
-/
def runHP : Option ((List (ℕ × ℕ) × List (String × ℕ × ℕ) × ℕ) × Bool × List (String × ℕ × ℕ) ×
    (Bool × ℕ) × Bool × Option (ℕ × ℕ × ℕ × ℕ × ℕ) × List ℕ × Bool × (ℕ × ℕ) × Bool × Bool) :=
  match publicOf (textK linesKF) (wordsK scalesKF) none with
  | .error _ => none
  | .ok X =>
    (tablesHP X).map fun t =>
      (numbersHP X, tensorsHP X, t.tab, orderHP X t, placesHP X t, readsHP X t, fullHP X,
        cellsHP X t, (X.HLy.kb, n2 .b), madeHP X)

#guard (match runHP with
  | none => false
  | some r =>
    r.1.1.all (fun p => p.1 == p.2) &&
    r.1.2.1 == [("hf0", 65536, 4816), ("hf1", 65536, 4816), ("hf2", 65536, 4816),
      ("hf3", 65536, 4816), ("hd", 16384, 640), ("hr", 8192, 15), ("bH", 32768, 384),
      ("xbL", 65536, 400)] &&
    r.1.2.2 == 8 && r.2.1 &&
    r.2.2.1 == [("hf@Z", 0, 19264), ("hf@phiZ", 19264, 19264), ("xbL@Z_V", 38528, 400),
      ("xbL@Y_N", 38928, 400), ("hd@zt_FC", 39328, 10240), ("hd@r_H", 49568, 10240),
      ("hr@zt_ROW", 59808, 120), ("hr@P_V", 59928, 120), ("hr@r_tV", 60048, 120),
      ("hr@rt_N", 60168, 120), ("hr@phiC", 60288, 120), ("hr@rhoC", 60408, 120),
      ("bH-bits-0", 60528, 384), ("bH-bits-1", 60912, 384), ("bH-pin", 61296, 384)] &&
    r.2.2.2.1 == (true, 12) && r.2.2.2.2.1 &&
    r.2.2.2.2.2.1 == some (0, 61680, 1, 61680, 61680) &&
    r.2.2.2.2.2.2.1 == [10, 16, 5120, 202048, 5, 16, 4, 14, 13] &&
    r.2.2.2.2.2.2.2.1 && r.2.2.2.2.2.2.2.2.1 == (384, 576) &&
    r.2.2.2.2.2.2.2.2.2 == (true, true))

end OnBytes.Road.Hd
