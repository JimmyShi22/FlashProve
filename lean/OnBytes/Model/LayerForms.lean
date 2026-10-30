-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/LayerForms.lean: the forms of a layer sub-proof that read its tables.

A layer sub-proof commits to matrices of cells: the values of the model's run on a group of layers.
The claims that are built here read no cell. The prover commits to one vector of tables, the reads
(U3 in the C++ source and in names here). Its root goes to the request's chain (rootInH,
OnBytes/Model/Trees.lean). A table belongs to a matrix and a point. It has one entry for each column
and each run of L rows: the sum of these L cells under public weights that follow from the point. In
a short table L is T, and an entry belongs to one feature. In a long table L is 2^la, and an entry
belongs to a block of 2^ls features (OnBytes/Model/Tensors.lean). In the three tables on matrix b L
is the number of all rows. That the tables are these sums is claimed by the smallness test
(OnBytes/Model/Tail.lean, item 3 at HTailF2), not here. Every claim of the sub-proof is a form
(Aff) in entries of the reads and in hidden values (OnBytes/Model/Hide.lean).

Calls, segments and columns are those of OnBytes/Model/Calls.lean. The lookup's trees, padding,
planes and join are those of OnBytes/Model/Forest.lean and OnBytes/Model/Look.lean. The matrices
(af, ad, ar, b, qa and the two of the residual stream), the tensors and the segments have the names
of OnBytes/Model/LayerLayout.lean (its head, tensorAsks, segmentList).

This file follows the parts of verifier/src/vf_layers_check.inc that lay the tables out and build
forms from them:
 - the list of tables and the place of each in the reads (tableAsks, layTables),
 - the readings of a tensor's entry from a short or a long table (shortA, longA, xbA, SA, SxsA,
   SBA, shA),
 - the row of digits of a norm with four limbs (rowAt),
 - for each segment of a lookup call the form of its keys at the lookup's point (line), without
   the inner products with weights, which the batched sumcheck proves,
 - the factor of one call in the lookup's join (joinPart).

A definition that has the name of a local type or function of the C++ routine runForkHidG2 in that
file follows it. line follows LINE.

No function here receives a message or draws a challenge. Where the C++ source refuses, the function
that follows it returns none, with one exception (see ewh). The caller (form in
OnBytes/Model/Layer.lean) turns none into a refusal without a name of its own. None of these
refusals depends on a value of a proof: they follow from public numbers and from the lengths of
points.

Main definitions: TableAsk, tableAsks, TableAt, layTables, Env, U3at, shortA, longA, SA, SBA, shA,
RowA, rowAt, row5At, site, high, line, weighedOf, laidOf, joinPart.

What is not claimed: nothing is proved here.
-/
import OnBytes.Model.LayerLayout
import OnBytes.Model.Look
import OnBytes.Model.Ledger

namespace OnBytes.Model.Layer

/-! ## Small tools -/

/-- 2^k as an element of the field. -/
def pw (k : Nat) : E := ofNat (2 ^ k)

/-- The exponent by which a site with the shift k is scaled: 16 - k, or 0 from k = 16 on. -/
def tOf (k : Nat) : Nat := 16 - k

/-- The sum of all members. -/
def sumE (v : Array E) : E := v.foldl addE zeroE

/-- The sum of the members a to b - 1. -/
def sumR (v : Array E) (a b : Nat) : E := (v.extract a b).foldl addE zeroE

/-- The form 0. -/
def aff0 : Aff := Aff.ofConst zeroE

/-- The sum over x below n of k b, where f x = (b, k). -/
def sumForms (n : Nat) (f : Nat → Option (Aff × E)) : Option Aff :=
  (List.range n).foldlM (fun a x => (f x).map fun t => a.addMul t.1 t.2) aff0

/-! ## The tables and their places in the reads -/

/-- One family of tables: the tables of the parts of one matrix at one point. -/
structure TableAsk where
  /-- the family's name: the matrix, the sign @ and the point; or one of three names on matrix b -/
  name : String
  /-- the number of the matrix's first part in the sub-proof's list of matrices -/
  M0 : Nat
  /-- the number of parts -/
  parts : Nat
  /-- the rows over which one entry sums -/
  L : Nat
  /-- the name of the point; empty for matrix b -/
  point : String := ""
  /-- true for a long table, whose entries stand for blocks of features -/
  lng : Bool := false
  deriving Repr, Inhabited

/-- The numbers of the matrices in a layer sub-proof's list. -/
structure MatIx where
  /-- the first part of af -/
  iAF : Nat
  /-- the first part of ad -/
  iAD : Nat
  /-- the matrix ar -/
  iAR : Nat
  /-- the matrix b -/
  iB : Nat
  /-- the matrix qa -/
  iQA : Nat
  /-- the stream that goes out -/
  iXO : Nat
  /-- the stream that comes in -/
  iXI : Nat
  deriving Repr, Inhabited

/-- The numbers of the matrices for a layout: the parts of af, the parts of ad, ar, b, qa, the
stream that goes out, the stream that comes in. -/
def matIx (y : Lay) : MatIx :=
  let iAD := y.parts.getD 0 0
  let iAR := iAD + y.parts.getD 1 0
  ⟨0, iAD, iAR, iAR + 1, iAR + 2, iAR + 3, iAR + 4⟩

/-- The families of tables of group g, in their order in the reads. -/
def tableAsks (y : Lay) (rd : Reads) (g : Nat) : List TableAsk :=
  let ix := matIx y
  let La := 2 ^ y.h.la
  let tables (mn : String) (M0 parts : Nat) (pts : List String) (lng : Bool) : List TableAsk :=
    pts.map fun n => ⟨mn ++ "@" ++ n, M0, parts, if lng then La else y.T, n, lng⟩
  let mb := 2 ^ y.h.lmb
  tables "af" ix.iAF (y.parts.getD 0 0) rd.rdAF true ++
  tables "qa" ix.iQA 1 rd.rdQA true ++
  tables "xbI" ix.iXI 1 rd.rdXI true ++
  (if g == 0 then tables "xbI" ix.iXI 1 ["Z_E"] true else []) ++
  tables "xbO" ix.iXO 1 rd.rdXO true ++
  tables "ad" ix.iAD (y.parts.getD 1 0) rd.rdAD false ++
  tables "ar" ix.iAR 1 rd.rdAR false ++
  (if y.h.p4 then tables "qa" ix.iQA 1 rd.rdQS false else []) ++
  [⟨"b-bits-0", ix.iB, 1, mb, "", false⟩, ⟨"b-bits-1", ix.iB, 1, mb, "", false⟩,
   ⟨"b-pin", ix.iB, 1, mb, "", false⟩]

/-- Where a family of tables lies in the reads: its first entry and the number of its entries, all
parts together. -/
structure TableAt where
  /-- the family's name -/
  name : String
  /-- its first entry -/
  first : Nat
  /-- the number of its entries -/
  len : Nat
  deriving Repr, Inhabited

/-- Places the tables of one family, part by part. Returns for each part the matrix's number and the
first entry of its table, and then the first free entry after the last table. A part's table has one
entry for each column and each run of a.L rows. The argument after a counts the parts still to
place. p: the first free entry. mats: the rows and the columns of each matrix. -/
def layParts (mats : Array (Nat × Nat)) (a : TableAsk) : Nat → Nat → List (Nat × Nat) × Nat
  | 0, p => ([], p)
  | n + 1, p =>
    let M := a.M0 + (a.parts - (n + 1))
    let mk := mats.getD M (0, 0)
    let r := layParts mats a n (p + mk.2 * (mk.1 / a.L))
    ((M, p) :: r.1, r.2)

/-- Places the families one after the other from entry p on. Returns each family's place, for each
family its parts, and the first free entry after them. Returns none if a family is empty: it would
share its first entry with the next. C++: addFun and tables in runForkHidG2. -/
def layTables (mats : Array (Nat × Nat)) :
    List TableAsk → Nat → Option (List TableAt × List (TableAsk × List (Nat × Nat)) × Nat)
  | [], p => some ([], [], p)
  | a :: rest, p =>
    let x := layParts mats a a.parts p
    if x.2 == p then none
    else (layTables mats rest x.2).map fun r =>
      (⟨a.name, p, x.2 - p⟩ :: r.1, (a, x.1) :: r.2.1, r.2.2)

/-! ## What the forms read -/

/-- What the forms of one layer sub-proof depend on. -/
structure Env where
  /-- the layout -/
  y : Lay
  /-- the quantization scales -/
  sc : Scales
  /-- the number of the group of layers -/
  g : Nat
  /-- the number of the array of the reads among the sub-proof's arrays -/
  iU3 : Nat
  /-- the columns of that array -/
  K3 : Nat
  /-- the places of the families of tables -/
  tab : List TableAt
  /-- for each call the point at which its key vector is read: the coordinates of the layer, then
  those of the column, then those of the token. It comes from the lookup. For a call with 2^iota
  trees the first iota coordinates are the last iota of the point over the trees' numbers, and the
  others are the point inside a tree, which all calls share. So if iota is above ll, the column's
  first coordinates come from the point over the trees' numbers -/
  zk : Array (Array E)

namespace Env

/-- True if layer lam of the group has routed experts. -/
def isMoe (v : Env) (lam : Nat) : Bool := v.y.h.p3 && lam % 2 == 1

/-- The number of layer lam of the group in the whole model. -/
def lay (v : Env) (lam : Nat) : Nat := v.g * v.y.Lam + lam

/-- The call that holds a segment: its number, the call, the segment. -/
def callOf (v : Env) (sn : String) : Option (Nat × CallD × Seg) :=
  (v.y.calls.toList.zipIdx.findSome? fun c => (c.1.seg? sn).map fun s => (c.2, c.1, s))

/-- The coordinates of the layer in the point of call q. -/
def zl (v : Env) (q : Nat) : Array E := (v.zk.getD q #[]).extract 0 v.y.h.ll

/-- The coordinates of the column in the point of call q, which has 2^lJ columns. -/
def zj (v : Env) (q lJ : Nat) : Array E := (v.zk.getD q #[]).extract v.y.h.ll (v.y.h.ll + lJ)

/-- The first entry of a family of tables. -/
def tabAt (v : Env) (n : String) : Option Nat := (v.tab.find? fun t => t.name == n).map (·.first)

/-- Entry i of the family of tables that begins at entry t of the reads, as a form. The layer
sub-proof's own claims name an entry of the reads through this function alone. The smallness test's
claims on the reads build their entries themselves (readEnts, OnBytes/Model/Tail.lean). Returns none
if no family begins at t, if i is not below the family's length, if the array has no column, or if
the entry's row does not fit 32 bits. These refusals do not catch an index that strays to another
tensor, layer or limb of the same matrix, nor a t that is the start of a family other than the one
meant. -/
def U3at (v : Env) (t i : Nat) : Option Aff :=
  match v.tab.find? fun x => x.first == t with
  | none => none
  | some x =>
    let e := t + i
    if i < x.len && v.K3 != 0 && e / v.K3 < 2 ^ 32 then some (Aff.ent v.iU3 (e / v.K3) (e % v.K3))
    else none

/-- The weight of each entry of segment s. e: the equality table of the column's coordinates in the
point of the segment's call. -/
def ewFrom (e : Array E) (s : Seg) : Array E := s.pos.map fun p => e.getD p zeroE

/-- The weight of each block of S2 entries of segment s, without the block's own coordinates.
eh: the equality table of all the column's coordinates except the last ls, where S2 = 2^ls. -/
def ewhFrom (S2 : Nat) (eh : Array E) (s : Seg) : Array E :=
  (Array.range (s.n / S2)).map fun xh => eh.getD (s.pos.getD (S2 * xh) 0 / S2) zeroE

/-- The weight of each entry of a segment at the point of its call. -/
def ewOf (v : Env) (sn : String) : Option (Array E) :=
  (v.callOf sn).map fun (q, c, s) => ewFrom (eqTab (v.zj q c.lJ)) s

/-- The weight of each block of 2^ls entries of a segment, without the block's own coordinates. The
layout has refused, under shape-call, a call with fewer than 2^ls columns, so lJ - ls is never cut
off at 0. The C++ routine tests that once more; this one does not. -/
def ewh (v : Env) (sn : String) : Option (Array E) :=
  (v.callOf sn).map fun (q, c, s) => ewhFrom v.y.S2 (eqTab (v.zj q (c.lJ - v.y.ls))) s

/-! ## Readings of a tensor -/

/-- The sum over the limbs l of 256^l times entry (cell l) of the family at t. -/
def limbs (v : Env) (t nl : Nat) (cell : Nat → Nat) : Option Aff :=
  sumForms nl fun l => (v.U3at t (cell l)).map fun a => (a, ofNat (256 ^ l))

/-- Entry (i, j) of tensor X, read from a short table at t. -/
def shortA (v : Env) (t : Nat) (X : Ten) (i j : Nat) : Option Aff :=
  v.limbs t X.nl fun l => tenCell X.place l i j

/-- Block jh of layer i of tensor X, read from a long table at t. -/
def longA (v : Env) (t : Nat) (X : Ten) (i jh : Nat) : Option Aff :=
  v.limbs t X.nl fun l => tenCell X.place l i 0 / v.y.S2 + jh

/-- Block kh of a residual stream, read from a long table at t. -/
def xbA (v : Env) (t kh : Nat) : Option Aff :=
  v.limbs t v.y.xb.nl fun l => tenCell v.y.xb l 0 0 / v.y.S2 + kh

/-- The name of the matrix that holds a tensor. -/
def mname (mat : Nat) : String := ["af", "ad", "ar", "qa"].getD mat ""

/-- A tensor with the first entry of its matrix's tables at the point Z. -/
def tensorAt (v : Env) (X Z : String) : Option (Ten × Nat) := do
  let t ← v.y.T_ X
  let tb ← v.tabAt (mname t.mat ++ "@" ++ Z)
  pure (t, tb)

/-- The sum over the blocks xh of wh[xh] times block xh of layer i of tensor X at the point Z. -/
def SA (v : Env) (wh : Array E) (X : String) (i : Nat) (Z : String) : Option Aff := do
  let (t, tb) ← v.tensorAt X Z
  sumForms wh.size fun xh => (v.longA tb t i xh).map fun a => (a, wh.getD xh zeroE)

/-- The same for the residual stream after write number sg of the group: the stream that comes in
for sg = 0, the stream that goes out after the last write, and a layer of tensor xs for every sg
between them. -/
def SxsA (v : Env) (wh : Array E) (Z : String) (sg : Nat) : Option Aff := do
  let last := v.y.NW * v.y.Lam
  let border := sg == 0 || sg == last
  let tb ← v.tabAt ((if sg == 0 then "xbI" else if sg == last then "xbO" else "af") ++ "@" ++ Z)
  let txs ← v.y.T_ "xs"
  sumForms (v.y.h.d / v.y.S2) fun xh =>
    (if border then v.xbA tb xh else v.longA tb txs (sg - 1) xh).map fun a =>
      (a, wh.getD xh zeroE)

/-- The sum over the entries a to b - 1 of a segment, block by block, of wh times tensor X at layer
i and the point Z. Entry x0 of the segment is the tensor's first feature. -/
def SBA (v : Env) (wh : Array E) (a b : Nat) (X : String) (i : Nat) (Z : String) (x0 : Nat) :
    Option Aff := do
  let (t, tb) ← v.tensorAt X Z
  let S2 := v.y.S2
  sumForms (b / S2 - a / S2) fun k =>
    let xh := a / S2 + k
    (v.longA tb t i (xh - x0 / S2)).map fun f => (f, wh.getD xh zeroE)

/-- Entry (i, j) of the tensor that tensorAt has found. Returns none if it has found none. A loop
over many entries of one tensor calls tensorAt once, before the loop. -/
def shIn (v : Env) (found : Option (Ten × Nat)) (i j : Nat) : Option Aff :=
  found.bind fun x => v.shortA x.2 x.1 i j

/-- Entry (i, j) of tensor X at the token point P. -/
def shA (v : Env) (X P : String) (i j : Nat) : Option Aff := v.shIn (v.tensorAt X P) i j

/-- The sum over x below n of ew[x] times entry (i, x) of tensor X at the token point P. -/
def shSum (v : Env) (ew : Array E) (n : Nat) (X P : String) (i : Nat) : Option Aff :=
  let found := v.tensorAt X P
  sumForms n fun x => (v.shIn found i x).map fun a => (a, ew.getD x zeroE)

/-! ## The row of digits of a norm -/

/-- The row of a norm with four limbs: its 74 digits and the numbers composed from them. Each field
says what an honest row holds. That a row holds it is claimed by claimsLedger4
(OnBytes/Model/Layer.lean) and by the lookup of the digits. The public numbers eps and M are
explained at the head of OnBytes/Model/Ledger.lean. -/
structure RowA where
  /-- the digits -/
  Dg : Array Aff
  /-- the sum of squares -/
  V : Aff
  /-- the carries into the bytes of V, c[0] to c[7] -/
  c : Array Aff
  /-- the lowest bit of sig -/
  s0 : Aff
  /-- the whole part of the square root of V + eps -/
  sig : Aff
  /-- V + eps minus the square of sig -/
  l1 : Aff
  /-- twice sig minus l1 -/
  h1 : Aff
  /-- the low 24 bits of R -/
  Rlo : Aff
  /-- the bits of R above them -/
  Rhi : Aff
  /-- the reciprocal: the whole part of (2^M + sig / 2) / sig -/
  R : Aff
  /-- the product of Rhi and sig -/
  p1 : Aff
  /-- the remainder of the division that gives R -/
  rr : Aff
  /-- sig - 1 minus the remainder -/
  rq : Aff

/-- The number with the n digits from digit a on, the lowest first. -/
def digits (Dg : Array Aff) (a n : Nat) : Aff :=
  (List.range n).foldl (fun s j => s.addMul (Dg.getD (a + j) aff0) (ofNat (256 ^ j))) aff0

/-- The cells of row i of the tensor of rows at the token point P. cells: the number of cells in a
row. -/
def rowCells (v : Env) (P : String) (i cells : Nat) : Option (Array Aff) := do
  let t ← v.tabAt ("ar@" ++ P)
  let trow ← v.y.T_ "row"
  (Array.range cells).mapM fun j => v.U3at t (trow.OFF + i * cells + j)

/-- Row i with four limbs at the token point P. A cell holds its digit minus 128. -/
def rowAt (v : Env) (P : String) (i : Nat) : Option RowA := do
  let Dg := (← v.rowCells P i 74).map fun a => a + Aff.ofConst (ofNat 128)
  let D (j : Nat) : Aff := Dg.getD j aff0
  let Rlo := digits Dg 57 3
  let Rhi := digits Dg 60 3
  pure {
    Dg := Dg
    V := digits Dg 0 8
    c := #[aff0] ++ ((Array.range 6).map fun s =>
      digits Dg (8 + 6 * s) 6 - Aff.ofConst (ofNat (2 ^ 47))) ++ #[D 7]
    s0 := D 45
    sig := (D 44).scale (ofNat 2) + D 45 + (D 46).scale (ofNat 256) + (D 47).scale (ofNat 65536) +
      (D 48).scale (ofNat (2 ^ 24))
    l1 := digits Dg 49 4
    h1 := digits Dg 53 4
    Rlo := Rlo
    Rhi := Rhi
    R := Rlo + Rhi.scale (ofNat (2 ^ 24))
    p1 := digits Dg 63 3
    rr := digits Dg 66 4
    rq := digits Dg 70 4 }

/-- Row i with five limbs at the token point P. -/
def row5At (v : Env) (P : String) (i : Nat) : Option (Row5 Aff) := do
  let cells ← v.rowCells P i 99
  pure (row5 fun j => cells.getD j aff0)

/-- The reciprocal R of row i at the token point P, in either form of the row. -/
def rowR (v : Env) (P : String) (i : Nat) : Option Aff :=
  if v.y.h.xl == 5 then (v.row5At P i).map (·.R) else (v.rowAt P i).map (·.R)

/-! ## The keys of a segment at the lookup's point -/

/-- The offset of a digit tensor of form 1. -/
def o1 : E := ofNat 128

/-- The offset of a digit tensor of form 2. -/
def o2 : E := ofNat 32896

/-- The offset of a digit tensor of the given form. -/
def oOf (form : Nat) : E := if form == 1 then o1 else o2

/-- The low key of a rounding site, without its accumulator. A rounding site is a place where the
model divides an accumulator by 2^k and rounds. The remainder is looked up in digits: 16
bits if the site's digit form is 0, and 8 or 16 more, the high digits, if the form is 1 or 2.
w: the sum of the segment's weights. SQ: the quotient. k: the shift, from 1 on. Srh: the high
digits, which are read only if the form is not 0. -/
def site (w : E) (SQ : Aff) (k form : Nat) (Srh : Unit → Option Aff) : Option Aff := do
  let v := (Aff.ofConst (mulE w (pw (k - 1))) - SQ.scale (pw k)).scale (pw (tOf k))
  if form == 0 then pure v
  else pure (v - (Aff.ofConst (mulE (oOf form) w) + (← Srh ())).scale (pw 16))

/-- The key of the high digits of a rounding site. The shift k is at most 24 in form 1 and at most
32 otherwise (scalesHeld, OnBytes/Model/LayerLayout.lean), so the exponent is never cut off at 0. -/
def high (w : E) (Srh : Aff) (k form : Nat) : Aff :=
  (Aff.ofConst (mulE (oOf form) w) + Srh).scale (pw ((if form == 1 then 24 else 32) - max k 16))

/-- The constant of the key of a clamp table: 2^15 + 2^39. -/
def clampKey : E := ofNat (2 ^ 15 + 2 ^ 39)

/-- The form of the segments G and U (up says which) at layer lam: the gate's or the up product's
rounding site. On a layer with routed experts the first fe entries belong to the shared expert and
the others to the routed one, each with its own shift. -/
def lineGU (v : Env) (up : Bool) (lam : Nat) (ew wh : Array E) : Option Aff := do
  let h := v.y.h
  let l := v.lay lam
  let form := if up then h.huD else h.hgD
  let rh := if up then "ru" else "rg"
  let Q (a b : Nat) : Option Aff :=
    if up then v.SBA wh a b "u" lam "Z" 0
    else if !h.gcl then v.SBA wh a b "gi" lam "Z" 0
    else do
      pure ((← v.SBA wh a b "g0" lam "Z" 0) + (← v.SBA wh a b "gh" lam "Z" 0).scale (ofNat 256))
  let k0 := v.sc.kl l (if up then Lku else Lkg)
  if !v.isMoe lam then
    site (sumE ew) (← Q 0 h.f) k0 form fun _ => v.SA wh rh lam "Z"
  else
    let a ← site (sumR ew 0 h.fe) (← Q 0 h.fe) k0 form fun _ => v.SBA wh 0 h.fe rh lam "Z" 0
    let b ← site (sumR ew h.fe h.f) (← Q h.fe h.f) (v.sc.klM l (if up then 2 else 1)) form
      fun _ => v.SBA wh h.fe h.f rh lam "Z" 0
    pure (a + b)

/-- The form of the segments GH and UH at layer lam: the high digits of the same two sites. -/
def lineGUH (v : Env) (up : Bool) (lam : Nat) (ew wh : Array E) : Option Aff := do
  let h := v.y.h
  let l := v.lay lam
  let form := if up then h.huD else h.hgD
  let rh := if up then "ru" else "rg"
  let k0 := v.sc.kl l (if up then Lku else Lkg)
  if !v.isMoe lam then pure (high (sumE ew) (← v.SA wh rh lam "Z") k0 form)
  else
    let a := high (sumR ew 0 h.fe) (← v.SBA wh 0 h.fe rh lam "Z" 0) k0 form
    let b := high (sumR ew h.fe h.f) (← v.SBA wh h.fe h.f rh lam "Z" 0)
      (v.sc.klM l (if up then 2 else 1)) form
    pure (a + b)

/-- The form of the segments QK and QKH (hi says which) at layer lam. The first dq entries belong
to q and the others to k, each with its own shift. -/
def lineQK (v : Env) (hi : Bool) (lam : Nat) (ew wh : Array E) : Option Aff := do
  let y := v.y
  let l := v.lay lam
  let part (A0 B0 k : Nat) : Option Aff := do
    let wB := sumR ew A0 B0
    if hi then pure (high wB (← v.SBA wh A0 B0 "rqk" lam "Z" 0) k y.h.hq)
    else
      site wB (← v.SBA wh A0 B0 "qkw" lam "Z" 0) k y.h.hq fun _ => v.SBA wh A0 B0 "rqk" lam "Z" 0
  pure ((← part 0 y.dq (v.sc.kl l Lkq)) + (← part y.dq y.nqk (v.sc.kl l Lkk)))

/-- The form of the segment ROW at layer lam: every digit of the layer's rows, times the digit's
multiplier. -/
def lineROW (v : Env) (lam : Nat) (ew : Array E) : Option Aff := do
  let xl := v.y.h.xl
  let NRl := ledNR xl
  let t ← v.tabAt "ar@zt"
  let trow ← v.y.T_ "row"
  sumForms ew.size fun x =>
    let np := x / NRl
    let idx := x % NRl
    (v.U3at t (trow.OFF + (v.y.NN * lam + np) * NRl + idx)).map fun a =>
      (a + Aff.ofConst (ofNat 128), scaleNat (ew.getD x zeroE) (ledMu xl idx))

/-- The form of the segment DD at a layer with routed experts: for each expert x the logit plus the
selector's entries of all later experts, under the negative weight. -/
def lineDD (v : Env) (lamM : Nat) (ew : Array E) : Option Aff := do
  let r ← (List.range v.y.h.NE).reverse.foldlM
    (fun (s : Aff × Aff) x => do
      let a := s.1.addMul ((← v.shA "lr" "zt" lamM x) + s.2) (negE (ew.getD x zeroE))
      pure (a, s.2 + (← v.shA "sel" "zt" lamM x)))
    (aff0, aff0)
  pure r.1

/-- The form of the keys of segment sn at layer lam of the group, at the lookup's point, without the
inner products with weights. ew: the weight of each entry of the segment; wh: the weight of each
block of entries, for a segment that is read by blocks. Returns none for an unknown segment.
C++: LINE in runForkHidG2, which forms ew and wh itself. -/
def line (v : Env) (sn : String) (lam : Nat) (ew wh : Array E) : Option Aff := do
  let y := v.y
  let h := y.h
  let sc := v.sc
  let l := v.lay lam
  let w := sumE ew
  let S (X : String) : Option Aff := v.SA wh X lam "Z"
  let K (c : E) : Aff := Aff.ofConst (mulE w c)
  let lamM := lam / 2
  let NE := h.NE
  let kr := if v.isMoe lam then sc.klM l 0 else 0
  if sn == "G" then v.lineGU false lam ew wh
  else if sn == "U" then v.lineGU true lam ew wh
  else if sn == "GH" then v.lineGUH false lam ew wh
  else if sn == "UH" then v.lineGUH true lam ew wh
  else if sn == "UT" then pure ((← S "u") + K (pw LBU))
  else if sn == "QK" then v.lineQK false lam ew wh
  else if sn == "QKH" then v.lineQK true lam ew wh
  else if sn == "N1" then site w (← S "aw") (sc.kl l LK1) 2 fun _ => S "ra"
  else if sn == "N2" then site w (← S "mw") (sc.kl l LK2) 2 fun _ => S "rm"
  else if sn == "N1H" then pure (high w (← S "ra") (sc.kl l LK1) 2)
  else if sn == "N2H" then pure (high w (← S "rm") (sc.kl l LK2) 2)
  else if sn == "O" then
    site w ((← v.SxsA wh "Z" (2 * lam + 1)) - (← v.SxsA wh "Z" (2 * lam))) (sc.kl l Lko) h.ho
      fun _ => S "ro"
  else if sn == "D" then
    site w ((← v.SxsA wh "Z" (2 * lam + 2)) - (← v.SxsA wh "Z" (2 * lam + 1))) (sc.kl l Lkd) h.hdD
      fun _ => S "rd"
  else if sn == "V" then site w (← S "vw") (sc.kl l Lkv) h.hv fun _ => S "rv"
  else if sn == "OH" then pure (high w (← S "ro") (sc.kl l Lko) h.ho)
  else if sn == "DH" then pure (high w (← S "rd") (sc.kl l Lkd) h.hdD)
  else if sn == "VH" then pure (high w (← S "rv") (sc.kl l Lkv) h.hv)
  else if sn == "ROW" then v.lineROW lam ew
  else if sn == "CN1" then
    pure ((← S "aw") + (← v.shSum ew h.d "a" "zt" lam).scale (pw 28) + K clampKey)
  else if sn == "CN2" then
    pure ((← S "mw") + (← v.shSum ew h.d "m" "zt" lam).scale (pw 28) + K clampKey)
  else if sn == "CQK" then
    pure ((← S "qkw") +
      ((← v.SBA wh 0 y.dq "q" lam "Z" 0) +
        (← v.SBA wh y.dq y.nqk "kx" lam "Z" y.dq)).scale (pw 28) + K clampKey)
  else if sn == "CV" then pure ((← S "vw") + (← S "v").scale (pw 28) + K clampKey)
  else if sn == "F" then
    let key ← if h.gcl then pure ((← S "g0") + (← S "gc").scale (ofNat 256)) else S "gi"
    pure (key + (← S "s").scale (pw 28) + K (ofNat (2 ^ 15 + 2 ^ 40)))
  -- The key g0 + 128 of G0 limits g0 to a byte. The key of CG must be a row of table FS. That alone
  -- does not give gc = gh clamped to -127 .. 127: by the C++ comment it follows from CG, F and G0
  -- together, since F reads the same cell gc beside g0.
  else if sn == "G0" then pure ((← S "g0") + K (ofNat 128))
  else if sn == "CG" then
    pure ((← S "gh") + (← S "gc").scale (pw 28) + K (ofNat (49152 + 2 ^ 35 + 2 ^ 40)))
  else if sn == "XR" then
    pure (K (pw 15) - (← v.shSum ew h.d "xr" "zt" lamM).scale (pw 16))
  else if sn == "LR" then
    let q ← if h.rcl then
        sumForms NE fun x => do
          pure ((← v.shA "ly" "zt" lamM x).scale (ofNat 8) + (← v.shA "l3" "zt" lamM x),
            ew.getD x zeroE)
      else v.shSum ew NE "lr" "zt" lamM
    site w q kr h.hr fun _ => v.shSum ew NE "rl" "zt" lamM
  else if sn == "LT" then
    sumForms NE fun x => do
      pure ((← v.shA "lr" "zt" lamM x) + Aff.ofConst (pw 14), scaleNat (ew.getD x zeroE) 2)
  else if sn == "DD" then v.lineDD lamM ew
  else if sn == "LH" then pure (high w (← v.shSum ew NE "rl" "zt" lamM) kr h.hr)
  else if sn == "SEL" then
    sumForms NE fun x => do pure (← v.shA "sel" "zt" lamM x, scaleNat (ew.getD x zeroE) 128)
  else if sn == "MR" then
    pure ((Aff.ofConst (pw (if h.gcl then 14 else 15)) +
      (← v.shA "sc" "zt" lamM 0).scale (pw 17)).scale (ew.getD 0 zeroE))
  -- The key 32 l3 of L3 limits l3 to 0 .. 7. By the C++ comment the key of CLR is the row of table
  -- FC for ly exactly if lr - l3 = 8 times ly clamped to -2047 .. 2047.
  else if sn == "L3" then
    sumForms NE fun x => do pure (← v.shA "l3" "zt" lamM x, scaleNat (ew.getD x zeroE) 32)
  else if sn == "CLR" then
    let a ← sumForms NE fun x => do
      pure ((← v.shA "ly" "zt" lamM x) +
        ((← v.shA "lr" "zt" lamM x) - (← v.shA "l3" "zt" lamM x)).scale (pw 25), ew.getD x zeroE)
    pure (a + K clampKey)
  else none

/-! ## One call's factor in the lookup's join -/

/-- Marks the columns of segment s on layer lam. Returns none if one of them is marked already or
lies outside the array. -/
def markColumns (J lam : Nat) (s : Seg) (weighed : Array Bool) : Option (Array Bool) :=
  s.pos.foldlM
    (fun w p =>
      if w.getD (lam * J + p) true then none else some (w.setIfInBounds (lam * J + p) true))
    weighed

/-- For each column (lam, j) of a call, at the index lam J + j: whether a segment that exists on
layer lam lists it. The marks are taken from the segments' lists of columns (Seg.pos), not from the
forms that line builds: a form that weighs other columns than its segment lists is not seen here.
Returns none if two segments list one column. A column that no segment lists is left to the padding.
-/
def weighedOf (v : Env) (c : CallD) : Option (Array Bool) :=
  (List.range v.y.Lam).foldlM
    (fun w lam =>
      c.segs.foldlM
        (fun w s => if s.moe && !v.isMoe lam then some w else markColumns c.J lam s w) w)
    (Array.replicate (v.y.Lam * c.J) false)

/-- Adds to the count of each tree the padding keys that call q's unmarked columns hold: T keys for
each column. Returns none if a column lies in no tree. The layout has refused a depth dT below la,
and la is above lt, so dT - lt is never cut off at 0. -/
def laidOf (v : Env) (q : Nat) (weighed : Array Bool) (laid : Array Nat) : Option (Array Nat) :=
  let fo := v.y.fo
  (List.range weighed.size).foldlM
    (fun laid x =>
      if weighed.getD x true then some laid
      else
        let tree := fo.first.getD q 0 + x / 2 ^ (fo.dT - v.y.h.lt)
        if tree < laid.size then some (laid.modify tree (· + v.y.T)) else none)
    laid

/-- The factor of e_q in the lookup's join (Forest.join in OnBytes/Model/Look.lean), for call q:
alpha - q theta - (the padding key) (the weight of the padding's columns) - the segments' forms,
each layer under its weight. weighed: weighedOf of the call. -/
def joinPart (v : Env) (alpha theta : E) (q : Nat) (c : CallD) (weighed : Array Bool) :
    Option Aff := do
  let Lam := v.y.Lam
  let el := eqTab (v.zl q)
  let e := eqTab (v.zj q c.lJ)
  -- lJ - ls is never cut off at 0: see ewh.
  let eh := eqTab (v.zj q (c.lJ - v.y.ls))
  let lines ← c.segs.foldlM
    (fun a s =>
      let ew := ewFrom e s
      let wh := if s.n % v.y.S2 == 0 && s.name != "ROW" then ewhFrom v.y.S2 eh s else #[]
      (List.range Lam).foldlM
        (fun (a : Aff) lam =>
          if s.moe && !v.isMoe lam then some a
          else (v.line s.name lam ew wh).map fun f => a.addMul f (negE (el.getD lam zeroE)))
        a)
    aff0
  let padW := (List.range Lam).foldl
    (fun p lam =>
      let s := (List.range c.J).foldl
        (fun s j => if weighed.getD (lam * c.J + j) true then s else addE s (e.getD j zeroE)) zeroE
      addE p (mulE (el.getD lam zeroE) s))
    zeroE
  let call := v.y.cl.getD q {}
  pure (Aff.ofConst (subE (subE alpha (scaleNat theta q)) (scaleE (call.tauAt call.t0) padW)) +
    lines)

end Env

end OnBytes.Model.Layer
