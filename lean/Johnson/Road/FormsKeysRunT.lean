-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/FormsKeysRunT.lean: which entry of which committed matrix stands under an entry of a
table of the reads: the verifier's rule, the cells of Johnson/Road/FormsKeysMat.lean and the
library's addresses, evaluated side by side on made-up numbers.

A layer sub-proof keeps tables of evaluations of its matrices in one vector, the reads. The
verifier's forms name an entry of a family of tables by a feature's or a block's number. The
smallness test names the same entries by part, column and run of rows (tabAt in
OnBytes/Model/Tail.lean). The library gives every cell a row and a column of its matrix (featAt,
afPart, addr in Inst/Model/FF/Index.lean). This file runs the three against each other before
anything is proved of them.

Every line "#guard" is evaluated when this file is compiled, by Lean's interpreter, and the
compilation fails if the value is not true. It is a run. It is no theorem: nothing that only a guard
shows can be used in a proof. The only theorems here are switchesS, sizedS, sized2S and equalS.

The shapes. hR (Johnson/Road/FormsKeysRun.lean): the columns of af hold 8 features, those of qa and
of the stream 4, a block is 2 features, ad is in 2 parts. hS: the columns of af, qa and the stream
hold 4 features, a block is 2 features, af is in 3 parts (with 4 features of fill), ad in 1. hSb: as
hS, but a block is 4 features, a whole column. The calls are pcR throughout. dimT h: sizes of the
library with the features of a column taken from the shape's heights.

What is run, and what is compared with what.
 G1   at hR, hS, hSb, in both groups, for all families of tables: the verifier's layTables against
      the verifier's tabAt. Part by part, column by column, run by run, tabAt gives the family's
      entries in rising order, all of them.
 G1b  same shapes, all families but the three on b: cellsAt against tabAt and the row on which Holds
      puts a weight. Also firstM and partsM against the families that tableAsks lists.
 G2   at hS, hSb: tabAt against the library's featAt and afPart.
 G3   at hS, hSb: the verifier's sizes against the library's nFeatMx, afCols, nCol, lRow, mZ.
 G4   at hS, hSb, families at the points Z and zt: the sum that an entry is meant to hold, under the
      verifier's weights, against the sum over features and positions at the library's addresses,
      in the verifier's field, on made-up entries.
 G5   at hS, hSb, for all 34 arrays, every cell of a value, instance and channel: the verifier's
      tenCell against the library's feat; at the first and the last position: cellsOf of cellsAt
      against the entry at the library's addr.
 None of G1 to G5 asks that a block be a whole column: all hold at hS and at hSb.
 Controls. At hR, where no sizes of the library fit: with the features of a column taken from af, G2
 holds for af, ad and ar and fails for qa and the stream; four lines of G3 fail; G5 fails. At hS
 three false rules for the cells fail G1b.
 The library's Dim.OK, field by field, at dimT hS and dimT hSb: six fields hold; whole and full do
 not (at dimT hR blk does not hold either). So these made-up sizes are no witness for a theorem that
 takes Dim.OK.
 The plans. At hS and at hR, with made-up settings, plansG returns a plan for each group. In each:
 the plan's matrices have the rows and columns of the list from which the check lays the tables, and
 are as many; the reads are array number 0, with as many columns as entries; the length that the
 plan gives them is the first free entry behind the tables; G1 holds with the plan's own numbers;
 tablesTile passes and counts as many runs as the plan counts reads. The verifier's functions
 against each other. The plan's list of matrices is, field by field, that of tailsOf: more than
 trueAt_of_holds (Johnson/Road/FormsKeysTrue.lean) asks, which is their rows
 and columns.

What is made up: all numbers of the shapes, the calls, the entries of the matrices (idM, meT), the
point of G4, and for the plans the scales, the vocabulary, the tokens and the settings. None is
taken from a parameter file.

What is not claimed. Nothing is said of any other shape. hS and hSb are shapes for which layout
returns, and hS one for which plansG returns, not shapes that the verifier is shown to admit
(Johnson/Road/FormsKeysRun.lean lists the tests that are not run). No proof is made or checked, and
no world is looked at: whether an entry of the reads holds what its table says is not the matter
here. The three families on b are looked at in G1 alone. The order of the matrices in the
sub-proof's list against any order of the library's, and the other kinds of sub-proof, are not
looked at. The program does not import this file.

Where the guards stand. So that no module costs over a minute of Lean's time, the guards on G4, G5
and the fields of Dim.OK and the controls at hR and hS stand in Johnson/Road/FormsKeysRunTB.lean
[not in this library];
all others here.

What this comment says of Johnson/Road/FormsKeysRunTB.lean [not in this library] (the runs G4 and
G5, the fields of Dim.OK, the controls at hR and hS) cannot be checked here: those runs are made by
no file of this library.




-/
import Johnson.Road.FormsKeysRun
import Johnson.Road.FormsKeysAddr

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (HFun HTailF2 eqTab longPhi tenCell TenAt wsLayOf)
open OnBytes.Model.Layer (Lay Shape Reads TableAsk TableAt layout readsOf tableAsks layTables
  tailsOf scalesOf ropeOf Pub plansG readsCount)
open Inst.Model.FFSeg (Dim Mx Arr Cell feat featAt afPart afCols nFeatMx nCol lFeat lRow mZ addr lJ
  Dk NT sg)

/-! ## The made-up numbers -/

/-- The shape hR with other sizes of the matrices: af, qa and the stream have columns of one height,
which hold 4 features, that is two blocks; af is in three parts; ad is in one part; the columns of
ad and ar hold 2 features. -/
def hS : Shape := { hR with lmaf := 6, NAf := 3, lmad := 5, NAd := 1, lmar := 5 }

/-- The shape hS with blocks of 4 features: a column of af, qa or the stream is one block. -/
def hSb : Shape := { hS with la := 6 }

/-- Sizes of the library for a shape: those of dimOf, and the numbers that the library's addresses
read: the features of a column from the height of af for af, qa and the stream, from the heights of
ad and of ar for these; the parts of af; the rows of b; the cap on a tree's depth. -/
def dimT (h : Shape) : Dim :=
  { dimOf h with
    fBig := h.lmaf - h.lt, fAd := h.lmad - h.lt, fAr := h.lmar - h.lt, parts := h.NAf,
    r := h.lmb, cap := h.lidb, lp := 5 }

/-- Matrices whose entry at a place is the place. -/
def idM : Mats (ℕ × ℕ × ℕ) := fun a r c => (a, r, c)

/-- Matrices with made-up entries in the field. -/
def meT : Mats E := fun a r c => Model.ofNat (1 + 7 * a + 131 * r + 10007 * c)

/-- The kit's number of the matrix of a family of tables, from the family's name; none for the three
families on b. -/
def matOf (n : String) : Option ℕ :=
  let m := (n.splitOn "@").headD ""
  if m == "af" then some 0 else if m == "ad" then some 1 else if m == "ar" then some 2
  else if m == "qa" then some 3 else if m == "xbI" then some 4 else if m == "xbO" then some 5
  else none

/-- The library's matrix for the kit's number. -/
def mxOf : ℕ → Mx
  | 0 => .af | 1 => .ad | 2 => .ar | 3 => .qa | 4 => .xin | _ => .xout

/-- The library's 34 arrays. -/
def arrsT : List Arr :=
  [.g0, .gc, .sl, .up, .rg, .ru, .xs, .ro, .rd, .aw, .ra, .mw, .rm, .qkw, .rqk, .vw, .rv, .gh,
   .a, .m, .xr, .lr, .rl, .sel, .sc, .D, .ly, .l3, .q, .kx, .v, .o, .x0, .x8]

/-! ## What is evaluated -/

/-- A family of tables as layTables returns it: its place, what was asked for, and for each part the
matrix's number in the list and the first entry of its table. -/
abbrev FamT : Type := TableAt × TableAsk × List (ℕ × ℕ)

/-- Evaluates f in each group of layers on the layout, the numbers of the smallness test that tabAt
reads (the list of matrices and its length), the matrices' rows and columns, and the families of
tables. False if layout, readsOf or layTables does not return. -/
def withT (h : Shape) (f : Lay → HTailF2 → Array (ℕ × ℕ) → List FamT → Bool) : Bool :=
  match layout h pcR with
  | .error _ => false
  | .ok y =>
    match readsOf y with
    | .error _ => false
    | .ok rd =>
      (List.range y.NGr).all fun g =>
        let tm := ((tailsOf y).getD g {}).mats
        let mats := tm.map fun M => (M.m, M.k)
        match layTables mats (tableAsks y rd g) 0 with
        | none => false
        | some t =>
          t.1.length == t.2.1.length &&
            f y { NM := tm.size, mats := tm } mats
              ((t.1.zip t.2.1).map fun x => (x.1, x.2.1, x.2.2))

/-- The entries of a family: part by part, column by column, run of rows by run of rows, each with
the place that the smallness test's tabAt gives it. -/
def entriesT (tl : HTailF2) (mats : Array (ℕ × ℕ)) (a : TableAsk) (ps : List (ℕ × ℕ)) :
    List (ℕ × ℕ × ℕ × Option ℕ) :=
  ps.flatMap fun p =>
    let mk := mats.getD p.1 (0, 0)
    (List.range mk.2).flatMap fun c =>
      (List.range (mk.1 / a.L)).map fun sg =>
        (p.1, c, sg, tl.tabAt { mat := p.1, len := a.L, start := p.2 } c sg)

/-- G1. In every family the places that tabAt gives, taken part by part, column by column and run by
run, are the family's entries in rising order, all of them. -/
def g1T (_ : Lay) (tl : HTailF2) (mats : Array (ℕ × ℕ)) (fs : List FamT) : Bool :=
  fs.all fun (x, a, ps) =>
    x.name == a.name &&
      (entriesT tl mats a ps).map (·.2.2.2) == (List.range x.len).map fun e => some (x.first + e)

/-- G1, second half. For every family but those on b, every entry e and every row j of its run: the
cells, given as a function of the layout, have at feature e (L / T) + j / T and position j mod T the
entry of the matrix on which the table's weight number j stands. Also: the family's first matrix and
number of parts are firstM and partsM. -/
def g1bT (cells : Lay → Cells (ℕ × ℕ × ℕ)) (y : Lay) (tl : HTailF2) (mats : Array (ℕ × ℕ))
    (fs : List FamT) : Bool :=
  fs.all fun (x, a, ps) =>
    match matOf a.name with
    | none => true
    | some mat =>
      a.M0 == firstM y mat && a.parts == partsM y mat &&
        (entriesT tl mats a ps).all fun (M, c, sg, pos) =>
          match pos with
          | none => false
          | some p =>
            (List.range a.L).all fun j =>
              cells y mat ((p - x.first) * (a.L / y.T) + j / y.T) (j % y.T) == (M, sg * a.L + j, c)

/-- G2. For every family whose name passes the filter, every entry e and every feature r of its
run: the library's featAt gives feature e (L / T) + r, at position 0, the first row of that feature
in the run and the column counted across the parts; for af the library's afPart gives that column
its part and its number in the part. -/
def g2T (D : Dim) (only : String → Bool) (y : Lay) (tl : HTailF2) (mats : Array (ℕ × ℕ))
    (fs : List FamT) : Bool :=
  fs.all fun (x, a, ps) =>
    match matOf a.name with
    | none => true
    | some mat =>
      !only a.name ||
        (entriesT tl mats a ps).all fun (M, c, sg, pos) =>
          match pos with
          | none => false
          | some p =>
            let col := (M - a.M0) * colsM y mat + c
            ((List.range (a.L / y.T)).all fun r =>
              featAt D (mxOf mat) ((p - x.first) * (a.L / y.T) + r) 0 ==
                (sg * a.L + r * y.T, col)) &&
              (mat != 0 || afPart D col == (M - a.M0, c))

/-- The rows of all matrices of a group's list together. -/
def rowsT (y : Lay) : ℕ := ((tailsOf y).getD 0 {}).mats.foldl (fun s M => s + M.m) 0

/-- G3. The sizes, the verifier's against the library's: the features in use of af, ad, ar, qa; of
the stream that comes in; of the stream that goes out; the columns of a part of af; the columns of
all parts of the four matrices; the columns of the stream's matrices; the rows of the six; the rows
of all matrices together. -/
def g3T (h : Shape) (D : Dim) : List Bool :=
  match layout h pcR with
  | .error _ => []
  | .ok y =>
    [y.feat.toList == [nFeatMx D .af, nFeatMx D .ad, nFeatMx D .ar, nFeatMx D .qa],
     h.xl * h.d == nFeatMx D .xin, h.xl * h.d == nFeatMx D .xout,
     y.kcol.getD 0 0 == afCols D,
     (List.range 4).all fun m => partsM y m * colsM y m == nCol D (mxOf m),
     y.kxb == nCol D .xin && y.kxb == nCol D .xout,
     (List.range 6).all fun m => rowsM y m == 2 ^ lRow D (mxOf m),
     rowsT y == mZ D]

/-- The numbers of G3, the verifier's and the library's, to be read. -/
def n3T (h : Shape) (D : Dim) : List (List ℕ) :=
  match layout h pcR with
  | .error _ => []
  | .ok y =>
    [y.feat.toList, [nFeatMx D .af, nFeatMx D .ad, nFeatMx D .ar, nFeatMx D .qa], y.filled.toList,
     y.kcol.toList, [afCols D, nCol D .af, nCol D .ad, nCol D .ar, nCol D .qa, nCol D .xin],
     y.mrow.toList, y.parts.toList, [y.kxb, y.mxb, y.kbm, rowsT y, mZ D, y.S2, y.T]]

/-- G4. The order of the weights, in the field. For every family at the point Z or zt and every
entry: the sum that a table's entry is meant to hold, with the verifier's weights on the rows of the
run in the matrices meT, equals the sum over the features r of the run and the positions i of the
product of the two equality weights and the entry of meT at the library's address of feature
e (L / T) + r at position i. -/
def g4T (D : Dim) (y : Lay) (tl : HTailF2) (mats : Array (ℕ × ℕ)) (fs : List FamT) : Bool :=
  let Z := elemsR 50 (y.ls + y.h.lt)
  let lo := eqTab (Z.extract 0 y.ls)
  let tk := eqTab (Z.extract y.ls (y.ls + y.h.lt))
  fs.all fun (x, a, ps) =>
    match matOf a.name with
    | none => true
    | some mat =>
      !(a.point == "Z" || a.point == "zt") ||
        let phi := if a.lng then longPhi Z y.ls y.h.lt else tk
        (entriesT tl mats a ps).all fun (M, c, sg, pos) =>
          match pos with
          | none => false
          | some p =>
            let lhs := (List.range a.L).foldl
              (fun s j => addE s (mulE (phi.getD j zeroE) (meT M (sg * a.L + j) c))) zeroE
            let rhs := (List.range (a.L / y.T)).foldl (fun s r =>
              (List.range y.T).foldl (fun s i =>
                let rc := featAt D (mxOf mat) ((p - x.first) * (a.L / y.T) + r) i
                let pc := if mat == 0 then afPart D rc.2 else (0, rc.2)
                let w := if a.lng then mulE (lo.getD r zeroE) (tk.getD i zeroE)
                  else tk.getD i zeroE
                addE s (mulE w (meT (a.M0 + pc.1) rc.1 pc.2))) s) zeroE
            lhs == rhs

/-- G5. Cells by name. For every array, every cell of a value, instance and channel, at the first
and the last position: the feature that the verifier's rule gives the cell is the library's; the
cell, read by cellsOf in the cells cellsAt, is the entry at the library's address (for af through
afPart), in the matrix of the list that firstM names; and an array that is read by blocks begins at
a whole block and has a whole number of blocks in a channel's range. -/
def g5T (h : Shape) (D : Dim) : Bool :=
  match layout h pcR with
  | .error _ => false
  | .ok y =>
    arrsT.all fun X =>
      let pl : Option TenAt :=
        if X == .x0 || X == .x8 then some y.xb else (y.T_ (arrName X)).map (·.place)
      match pl with
      | none => false
      | some pl =>
        (!readLong X || X.width D % y.S2 == 0) &&
        (List.range X.nCell).all fun k => (List.range (X.cnt D)).all fun inst =>
          (!readLong X || tenCell pl k inst 0 % y.S2 == 0) &&
          (List.range (X.width D)).all fun j => [0, y.T - 1].all fun i =>
            let ad := addr D ⟨X, k, inst, j, i⟩
            let pc := if ad.1 == .af then afPart D ad.2.2 else (0, ad.2.2)
            tenCell pl k inst j == feat D X k inst j &&
              cellsOf D (cellsAt y idM) ⟨X, k, inst, j, i⟩ ==
                (firstM y (mxNo ad.1) + pc.1, ad.2.1, pc.2)

/-- The eight fields of the library's Dim.OK, one by one. -/
def okT (D : Dim) : List Bool :=
  [D.P.T == D.T, decide (1 ≤ D.lL), D.f == 2 * D.fe, decide (0 < D.parts),
   arrsT.all fun X => lFeat D X.mx != D.fBig || X.width D % 2 ^ D.fBig == 0,
   (List.finRange 8).all fun c => decide (lJ D c + D.lT ≤ Dk D),
   decide (D.fBig + D.lT ≤ Dk D), NT D == 2 ^ sg D]

/-! ## Three false rules, for the controls -/

/-- Position by position instead of feature by feature. -/
def cellsBadA (y : Lay) : Cells (ℕ × ℕ × ℕ) := fun mat φ i =>
  idM (firstM y mat + φ / fcM y mat / colsM y mat) (i * fcM y mat + φ % fcM y mat)
    (φ / fcM y mat % colsM y mat)

/-- The parts take the columns in turn. -/
def cellsBadB (y : Lay) : Cells (ℕ × ℕ × ℕ) := fun mat φ i =>
  idM (firstM y mat + φ / fcM y mat % partsM y mat) (φ % fcM y mat * y.T + i)
    (φ / fcM y mat / partsM y mat)

/-- Inside a part, neighbouring features lie in neighbouring columns. -/
def cellsBadC (y : Lay) : Cells (ℕ × ℕ × ℕ) := fun mat φ i =>
  idM (firstM y mat + φ / fcM y mat / colsM y mat)
    (φ % (fcM y mat * colsM y mat) / colsM y mat * y.T + i) (φ % colsM y mat)

/-! ## The run -/

/-- hS has the switches and digit forms for which the library has keys. -/
theorem switchesS : Switches hS := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- dimT hS agrees with hS in the nine numbers of Sized. -/
theorem sizedS : Sized hS (dimT hS) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- dimT hS agrees with hS in the sizes of the matrices: the seven equations of Sized2
(Johnson/Road/FormsKeysAddr.lean). -/
theorem sized2S : Sized2 hS (dimT hS) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- In hS the matrices af, qa and the stream's have one height, and ad is in one part. -/
theorem equalS : hS.lmq = hS.lmaf ∧ hS.lmx = hS.lmaf ∧ hS.NAd = 1 := ⟨rfl, rfl, rfl⟩

/- the layouts -/
#guard (layout hS pcR).isOk && (layout hSb pcR).isOk

/- G1 -/
#guard withT hR g1T && withT hS g1T && withT hSb g1T

/- G1b -/
#guard withT hR (g1bT fun y => cellsAt y idM) && withT hS (g1bT fun y => cellsAt y idM) &&
  withT hSb (g1bT fun y => cellsAt y idM)

/- G2 -/
#guard withT hS (g2T (dimT hS) fun _ => true) && withT hSb (g2T (dimT hSb) fun _ => true)

/- G3, and its numbers -/
#guard g3T hS (dimT hS) == List.replicate 8 true && g3T hSb (dimT hSb) == List.replicate 8 true
#guard n3T hS (dimT hS) ==
  [[2120, 160, 854, 192], [2120, 160, 854, 192], [2124, 160, 854, 192], [177, 80, 427, 48],
   [177, 531, 80, 427, 48, 10], [64, 32, 32, 64], [3, 1, 1, 1], [10, 64, 2560, 4544, 4544, 2, 16]]
#guard n3T hSb (dimT hSb) ==
  [[2120, 160, 854, 192], [2120, 160, 854, 192], [2124, 160, 854, 192], [177, 80, 427, 48],
   [177, 531, 80, 427, 48, 10], [64, 32, 32, 64], [3, 1, 1, 1], [10, 64, 2560, 4544, 4544, 4, 16]]

/-! ## The plans -/

/-- The tables of a group without their weights, as funsOf lists them. -/
def funsT (fs : List FamT) : Array HFun :=
  (fs.flatMap fun (_, a, ps) =>
    ps.map fun m => ({ mat := m.1, len := a.L, tree := 2, start := m.2 } : HFun)).toArray

/-- For each group of layers, from the plan that planG makes at the security target hb: whether the
plan's matrices have the rows and columns of the list from which the tables are laid, and are as
many; the number of the array of the reads and of its columns; the length that the plan gives the
reads and the first free entry behind the tables; the rows of all matrices; whether G1 holds with
the plan's own numbers; the number of runs that tablesTile counts and the plan's count of reads.
Refuses where the verifier's functions refuse. -/
def planT (h : Shape) (hb : ℕ) :
    Except String (List (Bool × Bool × Option ℕ × Option ℕ × ℕ × ℕ × ℕ × Bool × Option ℕ × ℕ)) := do
  let y ← layout h pcR
  let sc ← scalesOf h klR
  let wsLay ← wsLayOf (wsShapeR y) y.h.p3 6
  let rope ← ropeOf y.h
  let P ← Pub.of y sc rope wsLay 16 ((Array.range y.T).map fun t => (5 * t + 3) % 16)
    { lidb := h.lidb, tau := h.tau, hb := hb }
  let hps ← plansG P
  hps.toList.zipIdx.mapM fun (hp, g) =>
    let tm := (P.tails.getD g {}).mats
    let mats := tm.map fun M => (M.m, M.k)
    match layTables mats (tableAsks y P.rd g) 0 with
    | none => throw "no tables"
    | some t =>
      let fs : List FamT := (t.1.zip t.2.1).map fun x => (x.1, x.2.1, x.2.2)
      let iU3 := hp.tl.ix.U.getD 2 none
      pure (hp.tl.mats.map (fun M => (M.m, M.k)) == mats, hp.tl.NM == tm.size, iU3,
        iU3.bind fun i => (hp.Fp.trees[i]?).map (·.K), hp.nU.getD 2 0, t.2.2, hp.tl.mz,
        g1T y hp.tl mats fs, hp.tl.tablesTile (funsT fs) 2, readsCount y P.rd g)

/-- True if plansG returns and, in each group g, the plan's numbers of the smallness test tl meet
tl.mats = ((tailsOf y).getD g {}).mats and tl.NM = tl.mats.size (the second is a hypothesis of
trueAt_of_holds, Johnson/Road/FormsKeysTrue.lean; the first gives its other
one, which asks the rows and columns alone); and the number of the array of the reads and the number
of its columns, taken from the plan as the check takes them (hearOwn in OnBytes/Model/Layer.lean),
are there, the second not 0 and equal to the length that the plan gives the reads. -/
def planHeldT (h : Shape) (hb : ℕ) : Bool :=
  let r : Except String Bool := do
    let y ← layout h pcR
    let sc ← scalesOf h klR
    let wsLay ← wsLayOf (wsShapeR y) y.h.p3 6
    let rope ← ropeOf y.h
    let P ← Pub.of y sc rope wsLay 16 ((Array.range y.T).map fun t => (5 * t + 3) % 16)
      { lidb := h.lidb, tau := h.tau, hb := hb }
    let hps ← plansG P
    pure (hps.size == y.NGr && hps.toList.zipIdx.all fun (hp, g) =>
      hp.tl.mats == ((tailsOf y).getD g {}).mats && hp.tl.NM == hp.tl.mats.size &&
        match hp.tl.ix.U.getD 2 none with
        | none => false
        | some iU3 =>
          let K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0
          K3 != 0 && K3 == hp.nU.getD 2 0)
  match r with
  | .ok b => b
  | .error _ => false

/- the plans' numbers meet what trueAt_of_holds asks of tl -/
#guard planHeldT hS 128 && planHeldT hR 128

/- the plans, at two made-up security targets -/
#guard (match planT hS 128, planT hS 64 with
  | .ok a, .ok b =>
    a == [(true, true, some 0, some 17114, 17114, 17114, 4544, true, some 61, 61),
      (true, true, some 0, some 17094, 17094, 17094, 4544, true, some 59, 59)] && a == b
  | _, _ => false)
#guard (match planT hR 128 with
  | .ok a =>
    a == [(true, true, some 0, some 17132, 17132, 17132, 4736, true, some 91, 91),
      (true, true, some 0, some 17112, 17112, 17112, 4736, true, some 89, 89)]
  | .error _ => false)

#print axioms switchesS
#print axioms sizedS
#print axioms sized2S
#print axioms equalS

end OnBytes.Road
