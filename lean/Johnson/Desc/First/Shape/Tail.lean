-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Tail.lean: THE SHAPE OF THE SMALLNESS TEST's OWN RECORD, WHOLE: what is
left of HTailF2 (OnBytes/Model/Tail.lean), of a table of its list (HFun) and of its lookup's heard
record (Forest.Heard, OnBytes/Model/Look.lean) when every field element and every drawn entry is
left out; and THE WAY BACK: the record with these numbers, flags and marks, and zeros of these
sizes. Definitions and small laws; nothing is evaluated.

What the way back is for. The library's tests on the structure are written on the records (folds
over marks, tables, pieces). With blank, such a test B becomes a test on the shape
without a second text: fun a => B a.blank: the same folds, run at a record that holds no value. What
is then owed for B is one law: B tl = B (tailSh tl).blank: "B reads the shape alone".

THESE SHAPES ARE LEAN STRUCTURES, NOT PRODUCTS. THE TYPES OF THEIR FIELDS:
  FunSh      five Nat.
  HeardAll   Forest.Shape; List AffSh; PscSh; AffSh; List Nat; ten Nat.
  TailSh     Nat; Bool; Option Nat; Array Nat; Array Bool; Array (Nat × Nat); List Nat; List FunSh;
             Option HeardAll; and the library's own records of public numbers, as they are:
             Array TMat, Array T2Foreign, T2Map, CallZ, Forest.Shape, Array ShP, Array PlaceF.
  Of these records: TMat, T2Foreign, T2Map, ShP, PlaceF, Piece hold Nat, String, Option and Array
  of these alone. CallZ is a Call and an Array Piece. Forest.Shape is an Array Call, six Nat, four
  Array Nat. Call holds a String, six Nat, an Array Nat, a List (List (Nat × Nat)), AND
  tau : Option (Array UInt64): a written lookup table: words of a public file, no field element of
  the extension, nothing sent, nothing drawn.
  AffSh, PscSh: products of Nat, Bool and lists (Johnson/Desc/First/Shape/Parts.lean).
No field is E, Array E or Array Int.
WHAT IS LEFT OUT: of HTailF2: bitFactor9, whole; of cfF (the drawn entries), vt, vp, lsTail all but
the size; of rowX, loX, gamX, gamV all but each row's size. Of HFun: of phi all but the size. Of
Forest.Heard: theta, alpha, a, leavesA, whole; of zx, zy, e, zb0, zb1, tT all but the size; of zk
all but each point's size; of rows and cEnd all but the forms' shapes; of leaves all but its shape.

WIDE, NOT NARROW, BY CHOICE: every field without a value is kept, not only those that a guard
reads. The fields from tau to plFor are laid when the plan is made and no step of a run writes them:
they cost no step an update. slotA and slotB are written in a run: by the hearing of the lookup on
the digits (seatDigits, Johnson/Desc/First/Look/K3Seat.lean).

  funSh, heardAll, tailSh        the makers. They lay no default: an Option stays an Option.
  AffSh.blank, PscSh.blank, FunSh.blank, HeardAll.blank, TailSh.blank   the way back.
  HeardAll.narrow, TailSh.narrow, heard_narrow, tail_narrow   the small shapes of Parts.lean are
                                 read off these.
  affSh_blank, funSh_blank       the shape of the blank record is the shape: shown for two of the
                                 five ways back.

Limits. That a number of these records is public, or a count, is not shown in this file. No test is
shown here to read the shape alone. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First.Look (laidDigits padKeyDigits)

/-! ## The way back for forms and sumchecks -/

/-- The form with these entries and slots, every coefficient 0. -/
def AffSh.blank (a : AffSh) : Aff where
  ents := (a.ents.map fun e =>
    ({ tree := e.1, row := e.2.1, idx := e.2.2, coef := zeroE } : Ent)).toArray
  slots := (a.slots.map fun j => (j, zeroE)).toArray
  const := zeroE

theorem affSh_blank (a : AffSh) : affSh a.blank = a := by
  obtain ⟨es, ss⟩ := a
  show AffSh.mk ((es.map fun e =>
    ({ tree := e.1, row := e.2.1, idx := e.2.2, coef := zeroE } : Ent)).map entSh)
    ((ss.map fun j => (j, zeroE)).map (·.1)) = _
  rw [List.map_map, List.map_map]
  show (es.map fun e => (e.1, e.2.1, e.2.2), ss.map fun j => j) = _
  simp

/-- The sumcheck with these flags, degrees, numbers and start form's shape; every element 0. -/
def PscSh.blank (p : PscSh) : Psc where
  start := p.start.blank
  first := p.first
  vars := (p.degrees.map fun d =>
    ({ d := d, moment := [], psi := [], fixed := 0, fixedInv := zeroE } :
      OnBytes.Psc.Weight)).toArray
  r := Array.replicate p.challenges zeroE
  ended := p.ended
  rowMade := p.rowMade
  started := p.started

/-! ## A table of the list -/

/-- A table without its weights: matrix, rows to an entry, the number of weights, vector, first
entry. -/
structure FunSh where
  mat : Nat
  len : Nat
  weights : Nat
  tree : Nat
  start : Nat
  deriving DecidableEq, Repr, Inhabited

def funSh (f : HFun) : FunSh :=
  { mat := f.mat, len := f.len, weights := f.phi.size, tree := f.tree, start := f.start }

def FunSh.blank (f : FunSh) : HFun :=
  { mat := f.mat, len := f.len, phi := Array.replicate f.weights zeroE, tree := f.tree,
    start := f.start }

theorem funSh_blank (f : FunSh) : funSh f.blank = f := by
  cases f
  simp [funSh, FunSh.blank]

/-! ## The lookup's heard record -/

/-- The heard record without its elements. -/
structure HeardAll where
  shape : Forest.Shape
  rows : List AffSh
  leaves : PscSh
  sBit : Nat
  zx : Nat
  zy : Nat
  e : Nat
  cEnd : AffSh
  zb0 : Nat
  zb1 : Nat
  tT : Nat
  zk : List Nat
  owedObjects : Nat
  owedPlanes : Nat
  owedJoin : Nat

def heardAll (g : Forest.Heard) : HeardAll :=
  { shape := g.shape, rows := g.rows.toList.map affSh, leaves := pscSh g.leaves, sBit := g.sBit,
    zx := g.zx.size, zy := g.zy.size, e := g.e.size, cEnd := affSh g.cEnd, zb0 := g.zb0.size,
    zb1 := g.zb1.size, tT := g.tT.size, zk := g.zk.toList.map (·.size),
    owedObjects := g.owedObjects, owedPlanes := g.owedPlanes, owedJoin := g.owedJoin }

def HeardAll.blank (h : HeardAll) : Forest.Heard :=
  { shape := h.shape, rows := (h.rows.map AffSh.blank).toArray, leaves := h.leaves.blank,
    sBit := h.sBit, zx := Array.replicate h.zx zeroE, zy := Array.replicate h.zy zeroE,
    e := Array.replicate h.e zeroE, cEnd := h.cEnd.blank, zb0 := Array.replicate h.zb0 zeroE,
    zb1 := Array.replicate h.zb1 zeroE, tT := Array.replicate h.tT zeroE,
    zk := (h.zk.map fun n => Array.replicate n zeroE).toArray, owedObjects := h.owedObjects,
    owedPlanes := h.owedPlanes, owedJoin := h.owedJoin }

/-- The small shape of Parts.lean. -/
def HeardAll.narrow (h : HeardAll) : HeardSh :=
  HeardSh.mk h.leaves h.owedPlanes h.owedJoin h.zb0 h.zb1 h.zk h.shape.pub.toList h.sBit h.cEnd
    h.rows.length

theorem heard_narrow (g : Forest.Heard) : (heardAll g).narrow = heardSh g := by
  show HeardSh.mk _ _ _ _ _ _ _ _ _ (g.rows.toList.map affSh).length = _
  rw [List.length_map, Array.length_toList]
  rfl

/-! ## The smallness test's record -/

/-- The record without its elements and drawn entries. Each field has the name that it has in
HTailF2; where a list of elements stood, its size or its rows' sizes stand. -/
structure TailSh where
  tau : Nat
  lidb : Nat
  mz : Nat
  NM : Nat
  mats : Array TMat
  off : Array Nat
  col0 : Array Nat
  gtTree : Array Nat
  gtRow : Array Nat
  kTX : Array Nat
  ft : Array T2Foreign
  ix : T2Map
  blocks : Array (Nat × Nat)
  z1 : CallZ
  z2 : CallZ
  f9 : Forest.Shape
  pkMat : Array Nat
  pxMat : Array Nat
  shp : Array ShP
  nUF : Array Nat
  tabFirst : Array Nat
  tabLen : Array Nat
  plOwn : Array PlaceF
  plFor : Array PlaceF
  funClosed : Bool
  funs : List FunSh
  cfF : Nat
  cfFirst : Array Nat
  foldDrawn : Nat
  slotA : Nat
  slotB : Nat
  heard : Option HeardAll
  vt : Nat
  vp : Nat
  rowX : List Nat
  loX : List Nat
  eqFirst : Array Nat
  gamX : List Nat
  gamV : List Nat
  foldTakenF : Array Bool
  joinObj9 : Option Nat
  tieObj : Array Nat
  tiesOn : Array Nat
  nX4Laid : Nat
  lsTail : Nat

def tailSh (tl : HTailF2) : TailSh :=
  { tau := tl.tau, lidb := tl.lidb, mz := tl.mz, NM := tl.NM, mats := tl.mats, off := tl.off,
    col0 := tl.col0, gtTree := tl.gtTree, gtRow := tl.gtRow, kTX := tl.kTX, ft := tl.ft,
    ix := tl.ix, blocks := tl.blocks, z1 := tl.z1, z2 := tl.z2, f9 := tl.f9, pkMat := tl.pkMat,
    pxMat := tl.pxMat, shp := tl.shp, nUF := tl.nUF, tabFirst := tl.tabFirst, tabLen := tl.tabLen,
    plOwn := tl.plOwn, plFor := tl.plFor, funClosed := tl.funClosed,
    funs := tl.funs.toList.map funSh, cfF := tl.cfF.size, cfFirst := tl.cfFirst,
    foldDrawn := tl.foldDrawn, slotA := tl.slotA, slotB := tl.slotB,
    heard := tl.heard.map heardAll, vt := tl.vt.size, vp := tl.vp.size,
    rowX := tl.rowX.toList.map (·.size), loX := tl.loX.toList.map (·.size), eqFirst := tl.eqFirst,
    gamX := tl.gamX.toList.map (·.size), gamV := tl.gamV.toList.map (·.size),
    foldTakenF := tl.foldTakenF, joinObj9 := tl.joinObj9, tieObj := tl.tieObj,
    tiesOn := tl.tiesOn, nX4Laid := tl.nX4Laid, lsTail := tl.lsTail.size }

/-- Rows of zeros of the given sizes. -/
def blankRows (l : List Nat) : Array (Array E) := (l.map fun n => Array.replicate n zeroE).toArray

/-- **The way back**: the same numbers, flags and marks; zeros of these sizes. -/
def TailSh.blank (t : TailSh) : HTailF2 :=
  { tau := t.tau, lidb := t.lidb, mz := t.mz, NM := t.NM, mats := t.mats, off := t.off,
    col0 := t.col0, gtTree := t.gtTree, gtRow := t.gtRow, kTX := t.kTX, ft := t.ft, ix := t.ix,
    blocks := t.blocks, z1 := t.z1, z2 := t.z2, f9 := t.f9, pkMat := t.pkMat, pxMat := t.pxMat,
    shp := t.shp, nUF := t.nUF, tabFirst := t.tabFirst, tabLen := t.tabLen, plOwn := t.plOwn,
    plFor := t.plFor, funClosed := t.funClosed, funs := (t.funs.map FunSh.blank).toArray,
    cfF := Array.replicate t.cfF 0, cfFirst := t.cfFirst, foldDrawn := t.foldDrawn,
    slotA := t.slotA, slotB := t.slotB, heard := t.heard.map HeardAll.blank,
    vt := Array.replicate t.vt zeroE, vp := Array.replicate t.vp zeroE, rowX := blankRows t.rowX,
    loX := blankRows t.loX, eqFirst := t.eqFirst, gamX := blankRows t.gamX,
    gamV := blankRows t.gamV, foldTakenF := t.foldTakenF, joinObj9 := t.joinObj9,
    bitFactor9 := zeroE, tieObj := t.tieObj, tiesOn := t.tiesOn, nX4Laid := t.nX4Laid,
    lsTail := Array.replicate t.lsTail zeroE }

/-- The small shape of Parts.lean. The test on the padding key and the host's count are run at the
blank record: they read the two calls and the lookup's numbers alone. -/
def TailSh.narrow (t : TailSh) : TlSh :=
  TlSh.mk (t.heard.map HeardAll.narrow) t.f9.kT t.f9.cK t.ix.BZ (padKeyDigits t.blank)
    ((laidDigits t.blank).map (·.toList)) (callSh t.z1) (callSh t.z2) t.joinObj9

theorem tail_narrow (tl : HTailF2) : (tailSh tl).narrow = tlSh tl := by
  show TlSh.mk ((tl.heard.map heardAll).map HeardAll.narrow) tl.f9.kT tl.f9.cK tl.ix.BZ
    (padKeyDigits tl) ((laidDigits tl).map (·.toList)) (callSh tl.z1) (callSh tl.z2) tl.joinObj9 = _
  rw [Option.map_map]
  have e : (HeardAll.narrow ∘ heardAll) = heardSh := funext heard_narrow
  rw [e]
  rfl

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.affSh_blank
#print axioms VerifiableInference.Desc.First.Shape.funSh_blank
#print axioms VerifiableInference.Desc.First.Shape.heard_narrow
#print axioms VerifiableInference.Desc.First.Shape.tail_narrow
