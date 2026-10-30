-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Plan/PlaceTabs.lean: the record of every link's smallness test with its list of
tables closed, by a dry run of the verifier's own routines.

The reader's record of a smallness test (HTailF2, in PlaceNums.lean's Records) has an empty list of
tables: the verifier closes the list in the run, behind the link's first messages (closeFuns), with
the tables that the sub-proof's routine has laid out. A table has a matrix, a number of rows in a
block, a first entry in the vector of reads, and weights. The sizes of the typed smallness test
(sizeOf, OnBytes/Tie/Pv/Tail/SizeOf.lean) read the first three.

Here the routines are run dry, on zeros, under the entries that the planner gives for the link's
first moment: for attention hear and tables, for the head hear and tablesOf, for the layers hearLook
and hearOwn, each from the state of the sub-proof's arrays and slots (Fork) from which the
verifier's run starts it; the chain's statement is empty. The request's tokens are zeros at the
layers; at the head the plain reply is one zero and the record of covered positions is empty, which
the verifier's own first test (Covered.sized) would refuse: that test is not run here.

Main names:
  funsOf c n: the list of tables that the routine lays out at link n.
  openOf n, closedOf c n: the record whose list the verifier closes, and that record closed with
    the list of the dry run by the verifier's own closeFuns. In closedOf c n the first columns are
    not laid yet: it is not the record behind the draw of the matrix.
  drawnAt n funs: the closed record behind the verifier's own drawMatrixF, run dry under the
    entries of the link's second moment: that routine sets the first column of each matrix
    (cfFirst) and the drawn matrix (cfF), which is all zeros here.
  tabTestsOf n funs left, with the control tabControl: by evaluation, at link n and the dry run's
    tables: (1) the dry run uses up the planned entries of the moment, the list is not empty and
    closes, and the reader's record has an open list and no matrix drawn (so openOf n is that record
    at every kind of link); (2) every table lies in the third vector (tree = 2), which the record
    says holds all tables (the second members of tabFirst and tabLen are that vector's); each
    table's matrix is one of the record's, and its block is not empty and divides the matrix's rows;
    (3) the tables follow each other without a gap from the part's first entry, a table of matrix M
    with blocks of len rows having M.k * (M.m / len) entries, and together they fill the part's
    length; (4) the blocks of all tables together are as many as the plan's number of reads
    (Records.reads); (5) the draw of the matrix uses up the second moment's planned entries and
    keeps the closed list (funsHeld); behind it the first columns begin at 0, each matrix's is the
    one before and that matrix's columns, the last is the number of all columns, and the drawn
    matrix has tau entries a column.
Limits: a run on zeros at made-up tokens, no theorem. That a table's matrix, block and first entry
do not hang on what is drawn or on the tokens is by reading, not shown here. Once the dry draw
returns, the clauses of (5) on the kept list and on the first columns cannot fail: they restate what
drawMatrixF writes. The weights that the dry run computes are those at zeros and mean nothing. A dry
run computes these weights, so it is slow: 16 to 50 s a link at the small example and 27 to 195 s at
the full one, as measured. So the small example's test has a module for each link, and the full
example's is no module of this library.
The program does not import this file.

-/
import OnBytes.Tie.Pv.Plan.PlaceNums
import OnBytes.Model.Attention
import OnBytes.Model.Head
import OnBytes.Model.Layer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Plan

open OnBytes.Model (Fork HFun HTailF2)

/-- Runs a routine of a sub-proof dry, on zeros, under the entries of a list of rounds. Returns its
value and the number of entries that are left over. -/
def dry {α : Type} (x : OnBytes.Model.SubM α) (F0 : Fork) (l : List OnBytes.Params.PlanRound) :
    Except String (α × Nat) :=
  match (x.run F0).runNamed { entries := l.map (·.entry), st := {} } true [] [] with
  | .error e => .error s!"the dry run fails: {e.name} {e.place}"
  | .ok ((a, _), c) => .ok (a, c.ch.entries.length)

/-- The tables that the sub-proof's routine lays out, and the entries that the dry run leaves. -/
def funsOf (c : Chain1) (n : LinkNums) : Except String (Array HFun × Nat) :=
  let X := c.X
  if n.kind == "A" then
    match n.att with
    | none => .error "no plan record"
    | some a =>
      dry (do
        let f ← OnBytes.Attention.hear a
        let t ← (OnBytes.Attention.tables a.S a.mats a.nW f.g f.planes f.scores f.d f.x :
          Blk OnBytes.Attention.Tables)
        pure t.funs) (a.seam.Fp.fillL.slots a.ns) n.l0
  else if n.kind == "H" then
    dry (do
      let x ← OnBytes.Model.Head.hear X.hS X.HLy X.H default #[zeroE]
      let t ← OnBytes.Model.Head.tablesOf X.hS X.HLy X.H default x
      pure t.funs) ({ trees := X.H.Fp.trees } : Fork).fillL n.l0
  else
    match X.G[n.group]? with
    | none => .error "no plan record"
    | some hp =>
      let P := { X.layers with tokv := Array.replicate X.T 0 }
      dry (do
        let o ← OnBytes.Model.Layer.hearOwn P hp n.group
          (← OnBytes.Model.Layer.hearLook X.y n.group)
        pure o.funs) (hp.Fp.fillL.slots hp.ns) n.l0

/-- The record whose list the verifier closes. At attention it is what Seam.start returns: the
reader's record with the list open and no matrix drawn; at the layers and the head the reader's
record itself. -/
def openOf (n : LinkNums) : HTailF2 :=
  if n.kind == "A" then { n.tail with funClosed := false, foldDrawn := 0 } else n.tail

/-- That record, closed with the list of the dry run. -/
def closedOf (c : Chain1) (n : LinkNums) : Except String HTailF2 := do
  let (funs, _) ← funsOf c n
  match (openOf n).closeFuns funs with
  | none => .error "the list is closed already"
  | some tl => pure tl

/-- The closed record behind the draw of the matrix, and the entries that the dry run leaves. -/
def drawnAt (n : LinkNums) (funs : Array HFun) : Except String (HTailF2 × Nat) :=
  match (openOf n).closeFuns funs with
  | none => .error "the list is closed already"
  | some tl => dry tl.drawMatrixF {} n.l1

/-- The entries of a table. -/
def tabEntries (tl : HTailF2) (f : HFun) : Nat :=
  let M := tl.mats.getD f.mat {}
  M.k * (M.m / f.len)

/-- Whether the tables follow each other without a gap from entry a on; returns the end. -/
def follow (tl : HTailF2) : List HFun → Nat → Option Nat
  | [], a => some a
  | f :: fs, a => if f.start == a then follow tl fs (a + tabEntries tl f) else none

/-- The five tests, at a list of tables and a number of entries left over. -/
def tabTestsOf (n : LinkNums) (funs : Array HFun) (left : Nat) : List Bool :=
  let tl := n.tail
  let fs := funs.toList
  [left == 0 && !funs.isEmpty && ((openOf n).closeFuns funs).isSome && !tl.funClosed &&
     tl.foldDrawn == 0,
   fs.all fun f => f.tree == 2 && decide (f.mat < tl.NM) && f.len != 0 &&
     (tl.mats.getD f.mat {}).m % f.len == 0,
   follow tl fs (tl.tabFirst.getD 1 0) == some (tl.tabFirst.getD 1 0 + tl.tabLen.getD 1 0),
   (fs.map fun f => (tl.mats.getD f.mat {}).m / f.len).sum == n.reads,
   match drawnAt n funs with
   | .error _ => false
   | .ok (d, l) => l == 0 && d.funsHeld funs &&
       d.cfFirst.size == tl.NM + 1 && d.cfFirst.getD 0 1 == 0 &&
       d.cfFirst.getD tl.NM 0 == tl.foldColumns && d.cfF.size == tl.foldColumns * tl.tau &&
       (List.range tl.NM).all fun mu =>
         d.cfFirst.getD (mu + 1) 0 == d.cfFirst.getD mu 0 + (tl.mats.getD mu {}).k]

/-- A control: with the last table dropped the tables no longer fill the part, and their blocks are
fewer than the plan's reads: the third and the fourth test are false. -/
def tabControl (n : LinkNums) (funs : Array HFun) (left : Nat) : Bool :=
  let t := tabTestsOf n funs.pop left
  t[2]? == some false && t[3]? == some false

end OnBytes.Tie.Pv.Plan
