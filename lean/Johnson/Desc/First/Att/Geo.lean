-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Geo.lean: kind K5: the numbers of an attention segment's place that the kind's
claims and tables read, and the short functions on points of which their weights are made.

It imports the field's arithmetic alone. Each function's text follows the lines of OnBytes/Model
that its docstring names, over the small record `Geo` in the place of that verifier's shape.

Main names:
  `eqPair`, `eqPts`, `eqAt`, `eqTab`, `ones`: the equality polynomial at two points, at a point and a
    number, as a table; the product of a point's coordinates.
  `ofNat`, `scaleNat`, `idOf`, `leOf`, `minusOne`, `limbWeights`: a number in the field; a point's
    number; "x is at most y" at two points; the weights of a value's bytes.
  `Keys`, `Tab`, `Pc`, `CallG`, `Ten`, `UnitG`, `Geo`: the lists of keys, the kinds of table, a piece of a
    list, a lookup call as this kind reads it, a tensor's place, a unit, the place's numbers.
  `tenCell`, `headFeat`, `cutLast`, `blockRows`: the layout of a tensor's entries and of long tables.
    The layers' and the head's kinds read these four too; they have no common home yet.
  `weights`, `inner`: a unit's pieces' weights at its call's key point; the key point's last coordinates.
  `cover`, `tileSums`, `overTileRows`: the tiles below the diagonal.
A `Geo` is made from OnBytes/Model's shape (Att/GeoOf.lean).
A read at a coordinate or a weight that lacks gives 0 in silence (so do the lines of OnBytes/Model
that the docstrings name: by reading; no theorem here ties the two). The callers test some of the
lengths, NOT ALL: Att/Points.lean asks none of a remainder unit's key point; Att/TablesP.lean none
of a weight vector but the tokens'.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Field.Ext

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes

/-- x y + (1 - x)(1 - y). After OnBytes/Model/AttentionShape.lean:71. -/
def eqPair (x y : E) : E := addE (mulE x y) (mulE (subE oneE x) (subE oneE y))

/-- eq of two points, coordinate by coordinate, over x's length. After AttentionShape.lean:75-76. -/
def eqPts (x y : Array E) : E :=
  (List.range x.size).foldl (fun p v => mulE p (eqPair (x.getD v zeroE) (y.getD v zeroE))) oneE

/-- eq of a point with a number's bits, the highest first. After AttentionShape.lean:65-68. -/
def eqAt (z : Array E) (idx : Nat) : E :=
  (List.range z.size).foldl (fun p v =>
    let x := z.getD v zeroE
    mulE p (if (idx >>> (z.size - 1 - v)) % 2 == 1 then x else subE oneE x)) oneE

/-- eq of a point with every number below 2^(its length), as a table. After OnBytes/Model/Frame.lean:104-112. -/
def eqTab (z : Array E) : Array E :=
  z.foldl (fun t zv => t.foldl (fun n a =>
    let hi := mulE a zv
    (n.push (subE a hi)).push hi) (Array.emptyWithCapacity (2 * t.size))) #[oneE]

/-- The product of a point's coordinates. After AttentionShape.lean:79. -/
def ones (z : Array E) : E := z.foldl mulE oneE

/-- A number in the field. After OnBytes/Model/Frame.lean:61-70. -/
def ofNat (v : Nat) : E := ofF (v % pW.toNat).toUInt64

/-- x times a number. After Frame.lean:76. -/
def scaleNat (x : E) (v : Nat) : E := scaleE (v % pW.toNat).toUInt64 x

/-- The number whose bits, the highest first, are the point's coordinates. After AttentionShape.lean:83-85. -/
def idOf (z : Array E) : E :=
  (List.range z.size).foldl (fun s v => addE s (scaleNat (z.getD v zeroE) (2 ^ (z.size - 1 - v)))) zeroE

/-- «x is at most y», as a polynomial in two points' coordinates, the highest first. After AttentionShape.lean:90-94. -/
def leOf (x y : Array E) : E :=
  (List.range x.size).reverse.foldl (fun le v =>
    let a := x.getD v zeroE
    let b := y.getD v zeroE
    addE (mulE (subE oneE a) b) (mulE (eqPair a b) le)) oneE

/-- After OnBytes/Model/AttentionClaimsA.lean:47. -/
def minusOne : E := subE zeroE oneE

/-- 1, 256, 256^2, …: n weights. After AttentionClaimsA.lean:66. -/
def limbWeights (n : Nat) : Array E := (Array.range n).map fun l => ofNat (256 ^ l)

/-- The seven lists of keys. After AttentionShape.lean:117-137 (Seg). -/
inductive Keys where
  /-- the remainder of the gap and its flag: below the diagonal · on it -/
  | rm | rd
  /-- the gap without its remainder, the flag and the softmax weight: below the diagonal · on it -/
  | fm | fd
  /-- of the two remainders of the division: the low 16 bits · the digits above them -/
  | wl | wh
  /-- the distance from the index of the maximum to the query's position -/
  | ix
  deriving DecidableEq, Repr

/-- The four kinds of a call's table. After AttentionShape.lean:140-149 (Table). -/
inductive Tab where
  | kr | kfd | r16 | wh
  deriving DecidableEq, Repr

/-- A piece of a list of keys. -/
structure Pc where
  /-- of which list -/
  keys : Keys
  /-- the layer in the group -/
  lam : Nat
  /-- which of the query heads that share a head of keys and values -/
  a : Nat
  /-- the piece has 2^b keys -/
  b : Nat
  /-- the number of its first key -/
  off : Nat

/-- A unit: one lookup call's pieces of one list of keys. -/
structure UnitG where
  /-- the call's number -/
  call : Nat
  /-- the call has 2^n keys -/
  n : Nat
  /-- the coordinates of the unit's inner point -/
  bits : Nat
  /-- the list is fm; false at every other list, also at rm, which lies below the diagonal too -/
  below : Bool
  pcs : List Pc

/-- A lookup call, as this kind reads it. -/
structure CallG where
  tab : Tab
  /-- the shift, for a kind of table that depends on it; else 0 -/
  sh : Nat
  /-- the call has 2^n keys -/
  n : Nat
  /-- the table's row to which padding keys point -/
  t0 : Nat
  /-- the public row values; none: row t has the value t -/
  tau : Option (Array UInt64)
  /-- the lists of keys in the call, each once -/
  lists : List Keys
  /-- the pieces in the order of their keys -/
  pcs : List Pc

/-- Where a tensor lies among the features of a committed matrix: nl limbs, each of cnt layers of J features, from feature off on. After OnBytes/Model/Tensors.lean (TenAt). -/
structure Ten where
  off : Nat
  nl : Nat
  cnt : Nat
  J : Nat

/-- The numbers of the place that the kind's claims and tables read. -/
structure Geo where
  /-- bits of: a token · a column in a tile · a head of keys and values · a feature in a head -/
  lt : Nat
  lB : Nat
  lgk : Nat
  ldh : Nat
  /-- bits of the rows of a block: of the planes' matrices «as» · of a long table · of the lookup's planes' matrix -/
  lmS : Nat
  la : Nat
  lmb : Nat
  /-- query heads · the parts in which «as» is committed -/
  H : Nat
  NAs : Nat
  /-- tokens · columns in a tile · tile rows · slot rows -/
  T : Nat
  B : Nat
  nT : Nat
  hP : Nat
  /-- heads of keys and values · query heads that share one · features in a head · features of all query heads -/
  G : Nat
  HA : Nat
  dh : Nat
  dq : Nat
  /-- layers · the length of the table of exponentials · bits of a tile row -/
  Lam : Nat
  u0 : Nat
  lnT : Nat
  /-- bits of a place: below the diagonal · on it · bits of the features in a block of a long table -/
  nM : Nat
  nD : Nat
  ls : Nat
  /-- columns: of «as» · of the lookup's planes' matrix · entries of a table on: the rows' matrix · the outputs' · the queries' -/
  kAs : Nat
  kbA : Nat
  fillH : Nat
  fillO : Nat
  fillQ : Nat
  /-- first features: row maxima · denominators · index bits · the two remainders' high parts -/
  oMr : Nat
  oZr : Nat
  oIb : Nat
  oRh : Nat
  oRhp : Nat
  /-- the bound on a score -/
  Smax : Nat
  /-- queries · keys · values · outputs -/
  atQ : Ten
  atK : Ten
  atV : Ten
  atO : Ten
  calls : Array CallG

/-- Pairs (layer, query head in its group). After AttentionShape.lean:393. -/
def Geo.NP (g : Geo) : Nat := g.Lam * g.HA

/-- The coordinates of the inner point of a unit of a list of keys. After AttentionShape.lean:287-298. -/
def Geo.keyBits (g : Geo) : Keys → Nat
  | .rm | .fm => g.lgk + 2 * g.lt - 1
  | .rd | .fd => g.lgk + g.lt + g.lB
  | .wl => 1 + g.lgk + g.lt + g.ldh
  | .wh => g.lgk + g.lt + g.ldh
  | .ix => g.lgk + g.lt

/-- After AttentionShape.lean:258. -/
def CallG.holds (c : CallG) (k : Keys) : Bool := c.lists.contains k

/-- The units of the calls of one kind of table: (the call's number, the call, the list), by call, then in the order of ks. After OnBytes/Model/AttentionScores.lean:40-43. -/
def Geo.units (g : Geo) (t : Tab) (ks : List Keys) : List (Nat × CallG × Keys) :=
  g.calls.toList.zipIdx.flatMap fun x =>
    if x.1.tab == t then (ks.filter fun k => x.1.holds k).map fun k => (x.2, x.1, k) else []

/-- The last call that holds a list. After AttentionHeard.lean:119-120. -/
def Geo.lastHolding (g : Geo) (k : Keys) : Option Nat :=
  (g.calls.toList.zipIdx.filter fun x => x.1.holds k).getLast?.map (·.2)

/-- One call's pieces of one list, as a unit. -/
def Geo.unitAt (g : Geo) (q : Nat) (c : CallG) (k : Keys) : UnitG :=
  { call := q, n := c.n, bits := g.keyBits k, below := k == .fm, pcs := c.pcs.filter fun pc => pc.keys == k }

/-- The units of the softmax-table calls, in the order of hearing. -/
def Geo.scores (g : Geo) : List UnitG := (g.units .kfd [.fm, .fd]).map fun u => g.unitAt u.1 u.2.1 u.2.2

/-- The unit of a list that one call alone serves (wl · ix · wh). After OnBytes/Model/AttentionDivide.lean:51-59. -/
def Geo.single (g : Geo) (k : Keys) : Option UnitG := do
  let q ← g.lastHolding k
  let c ← g.calls[q]?
  pure (g.unitAt q c k)

/-- The value of the table's row to which padding keys point. After Frame.lean:182-185 at t0. -/
def CallG.padKey (c : CallG) : UInt64 :=
  match c.tau with
  | none => c.t0.toUInt64
  | some a => a.getD c.t0 0

/-- At a gap of this or more the softmax weight is 0 · what is added to the gap at a place above the diagonal. After AttentionShape.lean:278-281 (C · Om). -/
def Geo.gapC (g : Geo) (sh : Nat) : Nat := g.u0 * 2 ^ sh
def Geo.gapOm (g : Geo) (sh : Nat) : Nat := 2 * g.Smax + g.u0 * 2 ^ sh

/-- The matrix's feature that holds limb l of the tensor's entry at layer i and the tensor's own feature j. After Tensors.lean:63. -/
def tenCell (X : Ten) (l i j : Nat) : Nat := X.off + (l * X.cnt + i) * X.J + j

/-- The first of the dh features of head hd in a tensor; none: dh is 0 or does not divide J, or the head is past J. After Tensors.lean:67-69. -/
def headFeat (X : Ten) (hd dh : Nat) : Option Nat :=
  if dh == 0 || X.J % dh != 0 || hd ≥ X.J / dh then none else some (hd * dh)

/-- A point cut in front of its last k coordinates; none: it has fewer. After Tensors.lean:95-97. -/
def cutLast (z : Array E) (k : Nat) : Option (Array E × Array E) :=
  if k > z.size then none else some (z.extract 0 (z.size - k), z.extract (z.size - k) z.size)

/-- low[a] tok[b], a first. After Tensors.lean:79-80. -/
def blockRows (low tok : Array E) : Array E := low.flatMap fun a => tok.map fun b => mulE a b

/-- The pieces' weights at the call's key point: eq of its first coordinates with the number of the piece's block of keys; by layer, then by head. After OnBytes/Model/AttentionHeard.lean:92-103. -/
def weights (u : UnitG) (zk : Array E) : Array E :=
  ((u.pcs.map fun pc => (pc.lam, pc.a, eqAt (zk.extract 0 (u.n - pc.b)) (pc.off >>> pc.b))).mergeSort
    fun x y => x.1 < y.1 || (x.1 == y.1 && x.2.1 ≤ y.2.1)).toArray.map (·.2.2)

/-- The unit's inner point. After AttentionHeard.lean:109-110. -/
def inner (u : UnitG) (zk : Array E) : Array E := zk.extract (zk.size - u.bits) zk.size

/-- The tile (row, column) at slot row P and tile slot sg. After AttentionShape.lean:585-586. -/
def cover (nT P sg : Nat) : Nat × Nat := if sg < P then (P, sg) else (nT - 1 - P, sg - P)

/-- Each tile row's, and each tile column's, sum of the weights eP[P] es[sg] of its tile slots; the last tile slot holds no tile. After AttentionHeard.lean:129-135. -/
def tileSums (g : Geo) (eP es : Array E) : Array E × Array E :=
  let zeros := Array.replicate g.nT zeroE
  (List.range g.hP).foldl (init := (zeros, zeros)) fun acc P =>
    (List.range (g.nT - 1)).foldl (init := acc) fun (wI, wJ) sg =>
      let w := mulE (eP.getD P zeroE) (es.getD sg zeroE)
      let tile := cover g.nT P sg
      (wI.modify tile.1 (addE · w), wJ.modify tile.2 (addE · w))

/-- The sum over the tile rows I of wI[I] eI[I]. After OnBytes/Model/AttentionDivide.lean:88-89. -/
def overTileRows (g : Geo) (wI eI : Array E) : E :=
  (List.range g.nT).foldl (fun s I => addE s (mulE (wI.getD I zeroE) (eI.getD I zeroE))) zeroE

end VerifiableInference.Desc.First.Att.P
