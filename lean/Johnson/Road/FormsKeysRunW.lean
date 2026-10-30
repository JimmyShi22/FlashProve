-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysRunW.lean: where a claim on the weights reaches the matrix of weights W: the
verifier's layout, factors and settling beside the library's layout and tensor claims, evaluated on
made-up numbers.

A layer sub-proof never names a weight. It ends with claims "the weights of a unit, each times a
product of factors, sum to a hidden value" (OnBytes/Model/Weights.lean), which the merge settles on
the rows and columns of W. The library reads the weights of a layer in W by a layout of its own
(place, units in Inst/Model/Layout.lean; layerR in Inst/Model/FF/Trace.lean) and writes the value of
a panel's tensor claim as a sum over these weights (Pan.TnRow, Pan.TnPan in
Inst/Model/FF/Objects.lean). This file runs the two against each other.

Every line "#guard" is evaluated when this file is compiled, by Lean's interpreter, and the
compilation fails if the value is not true. It is a run. It is no theorem: nothing that only a guard
shows can be used in a proof. This file holds no theorem.

The numbers. The shape hR and the calls pcR of Johnson/Road/FormsKeysRun.lean; the shape hR8 and the
calls pcR8 of Johnson/Road/FormsKeysRun8.lean, which list the segments in the library's order, so
that the claims come in another order; a vocabulary of 16; 4, 6, 9 or 11 column bits. parW h: the
library's parameters with the same nine numbers (sizedW). The library's layout is defined for all
parameters and all numbers of column bits, so it can be evaluated at these.

What is run, and what is compared with what.
 W1  at 4, 6, 9, 11 column bits: the verifier's list of units (wsLayOf) against the library's
     (units, off, rows, bits, lOf, sOf): digits, first row, rows, and group by group size, class,
     low bits, bits given to the columns, what is left to the rows, first column bit; unitOf against
     first.
 W2  the cell of a weight's digit, through the verifier's own settling: for an index tuple, the
     claim whose factors weigh that tuple alone; the rows where wsGamma is not 0 and the column at
     which wsEpsT is not 0, against the library's place. On every tuple of the units named in the
     guards, and on every 37th or 41st tuple of units of queries and keys.
 W3  at 4, 6, 9 column bits, for eighteen units: a made-up factor's two halves (onColumns, and
     onRows with table) at the two parts that the library's split gives an index, against what the
     factor weighs the index with (facE, this file's reading of the factor's docstring).
 W5  the verifier's list of panels against the list that this file expects, and the units of the
     verifier's list of weight claims against the numbers of the units that the library's layerR
     reads for each panel; every claim passes wsClaimShape.
 W6  the panel of the down product: the claim's first group has fe indices on a layer with routed
     experts and f on another, while the panel has f columns.
 W7  every factor of every claim at every index, against the equality weights of the place's bits,
     the weights of the segment's entries, and the library's formulas AH and kp.
 W4  every claim's value as the verifier settles it on a made-up W, against the library's formula
     for the tensor claim's value, written in the verifier's field (tnW), with the weights read at
     layerR's tuples by the library's place.
 W8  two identities of the merge at a point that is not Boolean.
 Controls. Three false rules for the place of a digit fail W2; two false variants of tnW fail W4.
 The false rule "the first group is the slowest" is the true rule at a unit of which one group alone
 leaves more than one value to the rows; a guard holds that too. With 6 column bits only the units
 of queries and keys have two such groups.

What stands between the two sides and is this file's own: facE, descW, offW, headW, tnW. tnW and
headW are the library's formulas copied by hand into the verifier's field, with the verifier's
arrays for the equality weights and the verifier's ropeC for the rotary tables. That copy is
compared with the library's text by reading alone.

What is made up: all numbers of the shapes, the calls, the vocabulary, the numbers of column bits,
every element of the field that stands for a challenge or a point, the factors of W3, the matrix
madeW. None is taken from a parameter file.

What is not claimed. Nothing is said of any other shape. No proof is made or checked, and no world
is looked at: whether a hidden value is what its claim says is not the matter here. The embedding's
claim and the head's, the rotary tables against the library's, how W is committed, opened and
decoded, and the random steps of the merge are not looked at. The program does not import this file.

Where the guards stand. So that no module costs over a minute of Lean's time, three guards stand
apart: in Johnson/Road/FormsKeysRunWB.lean, with 6 column bits: W5 to W8 and W4 at hR; W5, W6, W7
and W4 at hR8; in Johnson/Road/FormsKeysRunWC.lean, with 9 column bits: W5, W7 and W4 at hR. All
others here.
-/
import Johnson.Road.FormsKeysRun8

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (WsShape WsLay WsUnit WsGrp WsFac WsClaim wsLayOf wsGamma wsRowPart wsEpsT
  wsClaimShape wsGammaAdd eqTab eqLow ofInt)
open OnBytes.Model.Layer (Lay Shape Env Reads Scales layout scalesOf readsOf ropeOf ClaimEnv Panels
  panelsA panelsT placePanels callsAC isAcc ropeC)
open Inst.Model (Params)
open Inst.Model.Layout (Kind Coord UnitS units first off rows bits lOf sOf split)

/-! ## The made-up numbers -/

/-- The library's parameters for a shape: those of dimOf, with the made-up vocabulary of 16 tokens
that wsShapeR has. -/
def parW (h : Shape) : Params := { (dimOf h).P with V := 16 }

/-- The numbers on which the layout of the committed weights depends, from the shape alone. A guard
below holds them against wsShapeR, which takes them from the layout. -/
def shapeW (h : Shape) : WsShape :=
  { D := h.D, L := h.L, d := h.d, dh := h.dh, dkv := h.Gk * h.dh, dq := h.H * h.dh, f := h.f,
    fe := h.fe, NE := h.NE, V := 16 }

/-- True if two shapes of the weights agree in the ten numbers that a caller sets. -/
def sameW (a b : WsShape) : Bool :=
  a.D == b.D && a.L == b.L && a.d == b.d && a.dh == b.dh && a.dkv == b.dkv && a.dq == b.dq &&
    a.f == b.f && a.fe == b.fe && a.NE == b.NE && a.V == b.V

/-- The verifier's layout of the committed weights for a shape, with lk column bits. -/
def layW (h : Shape) (lk : ℕ) : Option WsLay := (wsLayOf (shapeW h) h.p3 lk).toOption

/-- The nine numbers in which the verifier's shape of the weights and the library's parameters must
agree for the two layouts to be compared. -/
def sizedW (s : WsShape) (P : Params) : Bool :=
  s.L == P.layers && s.d == P.d && s.dh == P.ch && s.dq == P.nq * P.ch && s.dkv == P.nkv * P.ch &&
    s.f == P.f && s.fe == P.fe && s.NE == P.nexp && s.V == P.V

/-! ## W1: the units -/

/-- The class of a group as a number: 0 low, 1 high, 2 whole. -/
def kindP (g : WsGrp) : ℕ := if g.cls == 'E' then (if g.high then 1 else 0) else 2

/-- The kind of a coordinate as the same number. -/
def kindL : Kind → ℕ
  | .low => 0 | .high => 1 | .whole => 2

/-- A unit's numbers: digits, first row, rows, and for each group the size, the class, the bits of
the low part (0 for a whole index), the bits given to the columns, what is left to the rows, and the
first column bit. -/
abbrev UnitW : Type := ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)

/-- The units of the verifier's layout. -/
def unitsP (lay : WsLay) : List UnitW :=
  lay.U.toList.map fun u =>
    (u.nlw, u.off, u.rows, u.g.map fun g =>
      (g.R, kindP g, if g.cls == 'E' then g.z else 0, g.t, g.left, g.cb0))

/-- The groups of a unit of the library's layout. -/
def groupsL (k : ℕ) (U : UnitS) : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  ((U.coords.zip (bits U.coords k)).foldl
    (fun (s : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) × ℕ) ct =>
      (s.1 ++ [(ct.1.R, kindL ct.1.kind, if kindL ct.1.kind == 2 then 0 else sOf ct.1.R, ct.2,
        lOf ct.1 ct.2, s.2)], s.2 + ct.2))
    ([], 0)).1

/-- The units of the library's layout. -/
def unitsL (P : Params) (k : ℕ) : List UnitW :=
  let us := units P
  us.zipIdx.map fun x => (x.1.nU, off k us x.2, rows k x.1, groupsL k x.1)

/-- W1. The two lists of units are one; in a group of class 'E' the size is o 2^z; the verifier
finds the unit of each kind of each layer at the number that the library's order gives it; the
units' rows end at or before the verifier's number of rows. -/
def w1 (h : Shape) (lk : ℕ) : Bool :=
  match layW h lk with
  | none => false
  | some lay =>
    let P := parW h
    unitsP lay == unitsL P lk &&
    (lay.U.all fun u => u.g.all fun g => g.cls != 'E' || g.R == g.o * 2 ^ g.z) &&
    ((List.range h.L).all fun l =>
      (if l % 2 == 1 then [0, 1, 2, 5, 6, 7, 8, 9, 10, 11] else [0, 1, 2, 3, 4, 9]).zipIdx.all
        fun x => lay.unitOf x.1 l == some (first P l + x.2)) &&
    lay.unitOf 12 h.L == some (first P h.L) && lay.unitOf 13 h.L == some (first P h.L + 1) &&
    decide (off lk (units P) (units P).length ≤ lay.m0)

/-! ## W2: the cells, through the verifier's own settling -/

/-- All index tuples below the given sizes. -/
def boxW : List ℕ → List (List ℕ)
  | [] => [[]]
  | R :: Rs => (List.range R).flatMap fun v => (boxW Rs).map (v :: ·)

/-- The factor that weighs the index v of a group with 1 and every other index with 0. -/
def indW (g : WsGrp) (v : ℕ) : WsFac :=
  if g.cls == 'E' then
    { HV := (Array.range g.o).map fun hi => if hi == v / 2 ^ g.z then oneE else zeroE
      pt := (Array.range g.z).map fun i =>
        if (v % 2 ^ g.z).testBit (g.z - 1 - i) then oneE else zeroE }
  else { AV := (Array.range g.R).map fun x => if x == v then oneE else zeroE }

/-- The point on the columns that spells the column C: entry i is bit lk - 1 - i of C. -/
def bitsW (lk C : ℕ) : Array E :=
  (Array.range lk).map fun i => if C.testBit (lk - 1 - i) then oneE else zeroE

/-- The equality weight of the column C at the point rm, where rm[i] belongs to column bit
lk - 1 - i. -/
def eqAtW (lk : ℕ) (rm : Array E) (C : ℕ) : E :=
  (List.range lk).foldl
    (fun p b =>
      let X := rm.getD (lk - 1 - b) zeroE
      mulE p (if C.testBit b then X else subE oneE X)) oneE

/-- A rule that gives digit q of the weight with the index tuple idx of unit number n a row and a
column: the arguments are the column bits, the list of units, n, the unit, q, idx. -/
abbrev PlaceW : Type := ℕ → List UnitS → ℕ → UnitS → ℕ → List ℕ → ℕ × ℕ

/-- W2 for unit number n, against the rule pl, on every step-th index tuple. For such a tuple, the
claim whose factors weigh that tuple alone: it has the sizes that the layout asks; its coefficients
on the unit's rows (wsGamma) are 0 but at one row for each digit, where they are 1, 256, 256^2, ..
in rising order of the rows, and these rows are the rows that pl gives the digits; pl gives all
digits one column; the claim's factor on the columns (wsEpsT) is 1 at that column, and at a made-up
point that is not Boolean it is the equality weight of that column. -/
def w2Unit (pl : PlaceW) (step : ℕ) (lay : WsLay) (P : Params) (n : ℕ) : Bool :=
  let us := units P
  match lay.U[n]?, us[n]? with
  | some u, some U =>
    let rm := elemsR 77 lay.lk
    ((boxW (u.g.map (·.R))).zipIdx.filter fun x => x.2 % step == 0).all fun x =>
      let idx := x.1
      let c : WsClaim := { ui := n, f := (u.g.zip idx).map fun x => indW x.1 x.2 }
      let gam := wsGamma u (wsRowPart lay c oneE) oneE
      let ps := (List.range u.nlw).map fun q => pl lay.lk us n U q idx
      let C := (ps.headD (0, 0)).2
      (wsClaimShape lay c).isOk && gam.size == u.rows &&
        (gam.toList.zipIdx.filter fun x => !isZeroE x.1) ==
          (ps.zipIdx.map fun x => (Model.ofNat (256 ^ x.2), x.1.1 - u.off)) &&
        (ps.all fun x => decide (u.off ≤ x.1) && x.2 == C) &&
        wsEpsT lay c (bitsW lay.lk C) == oneE && wsEpsT lay c rm == eqAtW lay.lk rm C
  | _, _ => false

/-- W2 for the units with the given numbers. -/
def w2 (pl : PlaceW) (step : ℕ) (h : Shape) (lk : ℕ) (ns : List ℕ) : Bool :=
  match layW h lk with
  | none => false
  | some lay => ns.all fun n => w2Unit pl step lay (parW h) n

/-- The library's rule. -/
def placeL : PlaceW := Inst.Model.Layout.place

/-- The parts of an index tuple that are left to the rows, each with the number of its values, by
the library's split. -/
def rowParts (k : ℕ) (U : UnitS) (idx : List ℕ) : List (ℕ × ℕ) :=
  ((U.coords.zip (bits U.coords k)).zip idx).map fun x =>
    ((split x.1.1 x.1.2 x.2).2, lOf x.1.1 x.1.2)

/-- A false rule: the first group is the slowest in the number of a row. -/
def placeBadA : PlaceW := fun k us n U q idx =>
  (off k us n + (rowParts k U idx).reverse.foldr (fun x acc => x.1 + x.2 * acc) q,
    (placeL k us n U q idx).2)

/-- A false rule: low and high are swapped. -/
def placeBadB : PlaceW := fun k us n U q idx =>
  placeL k us n
    ⟨U.coords.map fun c =>
      ⟨c.R, match c.kind with | .low => .high | .high => .low | .whole => .whole⟩, U.nU⟩ q idx

/-- A false rule: the digit is the fastest in the number of a row. -/
def placeBadC : PlaceW := fun k us n U q idx =>
  (off k us n + (rowParts k U idx).foldr (fun x acc => x.1 + x.2 * acc) 0 * U.nU + q,
    (placeL k us n U q idx).2)

/-! ## W3: a factor is the product of its two halves -/

/-- What a factor weighs the index v of its group with, in the verifier's field: for class 'E' the
element for the high part times the equality weight of the factor's point at the low part; for class
'A' the element that is written out. -/
def facE (x : WsFac) (g : WsGrp) (v : ℕ) : E :=
  if g.cls == 'E' then mulE (x.HV.getD (v / 2 ^ g.z) zeroE) ((eqTab x.pt).getD (v % 2 ^ g.z) zeroE)
  else x.AV.getD v zeroE

/-- A made-up factor of the sizes that a group asks. -/
def madeFac (g : WsGrp) (seed : ℕ) : WsFac :=
  if g.cls == 'E' then { HV := elemsR seed g.o, pt := elemsR (seed + 500) g.z }
  else { AV := elemsR seed g.R }

/-- W3. For every group of every unit with a number in ns, a made-up factor and every index v: with
the column part and the row part that the library's split gives v, the factor's value on the columns
at the Boolean point that spells the column part, times entry number (row part) of its table on the
rows, is what the factor weighs v with. -/
def w3 (h : Shape) (lk : ℕ) (ns : List ℕ) : Bool :=
  match layW h lk with
  | none => false
  | some lay =>
    let us := units (parW h)
    ns.all fun n =>
      match lay.U[n]?, us[n]? with
      | some u, some U =>
        ((u.g.zip U.coords).zipIdx).all fun y =>
          let g := y.1.1
          let x := madeFac g (1000 * n + 100 * y.2 + 7)
          let tab := (x.onRows g).table g
          (List.range g.R).all fun v =>
            let s := split y.1.2 g.t v
            let X : ℕ → E := fun b => if s.1.testBit (b - g.cb0) then oneE else zeroE
            mulE (x.onColumns g X) (tab.getD s.2 zeroE) == facE x g v
      | _, _ => false

/-! ## The verifier's own claims -/

/-- What the runs on the verifier's own claims read, in one group of layers. -/
structure RunW where
  /-- the claims' environment -/
  ce : ClaimEnv
  /-- the panels -/
  pans : Panels
  /-- the calls with terms in the second token sumcheck -/
  TS : List ℕ
  /-- the weight claims -/
  cl : List WsClaim

/-- Evaluates f in each group of layers, on the verifier's own panels and weight claims at made-up
challenges, as run2R of Johnson/Road/FormsKeysRun.lean makes them. False if one of the verifier's
functions does not return. -/
def withW (h : Shape) (pc : List (List String)) (lk : ℕ) (f : RunW → Bool) : Bool :=
  let r : Except String Bool := do
    let y ← layout h pc
    let sc ← scalesOf h klR
    let rd ← readsOf y
    let wsLay ← wsLayOf (wsShapeR y) y.h.p3 lk
    let rope ← ropeOf y.h
    pure ((List.range y.NGr).all fun g =>
      let o : Option Bool := do
        let v ← envR y sc rd g
        let pe := panelEnvR v
        let TS ← rd.tscCalls.mapM y.callNo
        let pans ← panelsT pe TS (panelsA pe {})
        let rs := elemsR 400 (ceilLog2 (placePanels pans.bl).2)
        let ce : ClaimEnv := { v, wsLay, rope, rs, rt := elemsR 900 y.h.lt }
        let cl ← ce.weightClaims TS
        pure (f { ce, pans, TS, cl })
      o.getD false)
  match r with
  | .ok b => b
  | .error _ => false

/-- One panel as this file expects it: the segment's name; 0 for a panel of the lookup's join, 1 for
one of the second token sumcheck; whether its rows carry the selector; its rows; its columns; and
the layers of its weight claims, in order (none for a panel whose B side is a form). -/
abbrev DescW : Type := String × ℕ × Bool × ℕ × ℕ × List ℕ

/-- The panels that this file expects, in the order of the calls and their segments. -/
def descW (y : Lay) (TS : List ℕ) : List DescW :=
  let h := y.h
  let segsOf (q : ℕ) : List String := (y.calls.getD q default).segs.map (·.name)
  let odd := (List.range y.LamM).map fun i => 2 * i + 1
  (((callsAC y).flatMap segsOf).flatMap fun sn =>
    if sn == "LR" then [(sn, 0, false, y.LamM, h.d, odd)]
    else if isAcc sn then
      [(sn, 0, false, y.Lam, if sn == "O" then y.dq else if sn == "D" then h.f else h.d,
        List.range y.Lam)]
    else []) ++
  ((TS.flatMap segsOf).flatMap fun sn =>
    if sn == "N1" || sn == "N2" then [(sn, 1, false, y.Lam, 1, [])]
    else if sn == "QK" then [(sn, 1, false, y.Lam, h.d, List.range y.Lam)]
    else if sn == "XR" then [(sn, 1, false, y.LamM, 1, [])]
    else if sn == "DD" || sn == "MR" then [(sn, 1, false, y.LamM, h.NE, [])]
    else if sn == "G" || sn == "U" || sn == "D" then
      odd.map fun lam => (sn, 1, true, h.NE, if sn == "D" then h.fe else h.d, [lam])
    else [])

/-- The place, among the units of its layer in the library's order, of the unit that the library's
layerR reads for the panel of segment sn: for the lookup's join the matrices Wg, Wu, Wv, Wo, Wd, Wr;
for the second token sumcheck the unit of queries and keys, and Eg, Eu, Ed. -/
def offW (sn : String) (loop lam : ℕ) : ℕ :=
  if loop == 0 then
    if sn == "G" then 3 else if sn == "U" then 4 else if sn == "V" then 1 else if sn == "O" then 2
    else if sn == "D" then (if lam % 2 == 1 then 7 else 5) else 9
  else if sn == "QK" then 0 else if sn == "G" then 5 else if sn == "U" then 6 else 8

/-- The claims that this file expects, in order: segment, 0 or 1 as in DescW, layer of the group. -/
def namesW (ds : List DescW) : List (String × ℕ × ℕ) :=
  ds.flatMap fun d => d.2.2.2.2.2.map fun lam => (d.1, d.2.1, lam)

/-- W5. The verifier's list of panels is the expected one: selector, rows, columns, and the number
of the first weight claim, which is the number of claims of the panels before. The verifier's list
of claims has one claim for each expected one, on the unit whose number the library's order gives;
each passes the test of its sizes; no unit is claimed twice; the claims are as many as the units of
the group's layers. -/
def w5 (r : RunW) : Bool :=
  let y := r.ce.v.y
  let P := parW y.h
  let ds := descW y r.TS
  let exp := (ds.foldl (fun (s : List (Bool × Option ℕ × ℕ × ℕ) × ℕ) d =>
    (s.1 ++ [(d.2.2.1, if d.2.2.2.2.2.isEmpty then none else some s.2, d.2.2.2.1, d.2.2.2.2.1)],
      s.2 + d.2.2.2.2.2.length)) ([], 0))
  r.pans.bl.toList.map (fun b => (b.tri, b.v0, b.ni, b.ny)) == exp.1 && r.pans.nextV == exp.2 &&
    r.cl.map (·.ui) ==
      (namesW ds).map (fun x => first P (r.ce.v.lay x.2.2) + offW x.1 x.2.1 x.2.2) &&
    (r.cl.all fun c => (wsClaimShape r.ce.wsLay c).isOk) && (r.cl.map (·.ui)).Nodup &&
    r.cl.length == first P (r.ce.v.lay y.Lam) - first P (r.ce.v.lay 0)

/-! ## W7: the factors of the verifier's claims -/

/-- The sum of f i over i below n, in the verifier's field. -/
def sumW (n : ℕ) (f : ℕ → E) : E := (List.range n).foldl (fun s i => addE s (f i)) zeroE

/-- The weights of the entries of segment sn at the point of its call. -/
def ewSeg (v : Env) (sn : String) : Array E :=
  match v.callOf sn with
  | some (q, cd, s) => Env.ewFrom (eqTab (v.zj q cd.lJ)) s
  | none => #[]

/-- The library's AH and kp (Inst/Model/FF/Objects.lean), written in the verifier's field from the
verifier's point of the call of QK, its columns of QK, its token point rt and its rotary table: the
weight of head hd; and for layer lam of the group the factor on the coordinate x within a head. -/
def headW (c : ClaimEnv) (lam : ℕ) : Array E × Array E :=
  let y := c.v.y
  let h := y.h
  match c.v.callOf "QK" with
  | none => (#[], #[])
  | some (q, cd, s) =>
    let zj := c.v.zj q cd.lJ
    let eh := eqTab (zj.extract 0 (cd.lJ - y.ldh))
    let lf := eqTab (zj.extract (cd.lJ - y.ldh) cd.lJ)
    let et := eqTab c.rt
    let tabAt (j : ℕ) (sine : Bool) : E :=
      sumW y.T fun t =>
        mulE (et.getD t zeroE) (ofInt (ropeC h c.v.sc c.rope (c.v.lay lam) t j sine))
    ((Array.range (h.H + h.Gk)).map fun hd => eh.getD (s.pos.getD (h.dh * hd) 0 / h.dh) zeroE,
     (Array.range h.dh).map fun x =>
      if x % 2 == 0 then
        addE (mulE (tabAt (x / 2) false) (lf.getD x zeroE))
          (mulE (tabAt (x / 2) true) (lf.getD (x + 1) zeroE))
      else
        subE (mulE (tabAt (x / 2) false) (lf.getD x zeroE))
          (mulE (tabAt (x / 2) true) (lf.getD (x - 1) zeroE)))

/-- W7. For every claim and every group of its unit, at every index v of the group, the factor
weighs v: for the group kk with the equality weight of v over the panel's column bits of the place;
for e with that of v over the next bits; for x with the weight of entry x0 + v of the segment at its
call's point, x0 = fe for the routed G and U and 0 otherwise; for hd with the library's AH below
H + Gk and with 0 from there on; for cd with the library's kp. -/
def w7 (r : RunW) : Bool :=
  let c := r.ce
  let y := c.v.y
  let h := y.h
  ((namesW (descW y r.TS)).zip r.cl).all fun z =>
    let sn := z.1.1
    let loop := z.1.2.1
    let lam := z.1.2.2
    let wy := ceilLog2
      (if loop == 0 then (if sn == "O" then y.dq else if sn == "D" then h.f else h.d)
       else if sn == "D" then h.fe else h.d)
    let ec := eqLow c.rs 0 wy
    let er := eqLow c.rs wy (wy + ceilLog2 h.NE)
    let ew := ewSeg c.v sn
    let x0 := if loop == 1 && (sn == "G" || sn == "U") then h.fe else 0
    let hk := headW c lam
    match c.wsLay.U[z.2.ui]? with
    | none => false
    | some u =>
      (z.2.f.zip u.g).all fun fg =>
        let g := fg.2
        (List.range g.R).all fun v =>
          facE fg.1 g v ==
            (if g.name == "kk" then ec.getD v zeroE
             else if g.name == "e" then er.getD v zeroE
             else if g.name == "hd" then hk.1.getD v zeroE
             else if g.name == "cd" then hk.2.getD v zeroE
             else ew.getD (x0 + v) zeroE)

/-! ## W4 and W6: a claim's value, settled by the verifier, against the library's tensor claim -/

/-- A made-up matrix W. -/
def madeW (y c : ℕ) : E := Model.ofNat (3 + 17 * y + 1009 * c)

/-- The weight with the index tuple idx of unit number n that the rule pl reads in madeW. -/
def wgtW (pl : PlaceW) (k : ℕ) (us : List UnitS) (n : ℕ) (U : UnitS) (idx : List ℕ) : E :=
  sumW U.nU fun q =>
    let p := pl k us n U q idx
    mulE (Model.ofNat (256 ^ q)) (madeW p.1 p.2)

/-- A claim's value as the verifier settles it: the sum over the Boolean columns C and the unit's
rows y of the factor on the columns at C, the coefficient on row y and the entry of madeW. -/
def settledW (lay : WsLay) (c : WsClaim) : E :=
  match lay.U[c.ui]? with
  | none => zeroE
  | some u =>
    let gam := wsGamma u (wsRowPart lay c oneE) oneE
    sumW (2 ^ lay.lk) fun C =>
      let e := wsEpsT lay c (bitsW lay.lk C)
      if isZeroE e then zeroE
      else mulE e (sumW u.rows fun y => mulE (gam.getD y zeroE) (madeW (u.off + y) C))

/-- The library's value of the tensor claim of a panel's row (Pan.TnRow; for a panel with the
selector Pan.TnPan; Inst/Model/FF/Objects.lean), written in the verifier's field: the weights are
read in madeW at the tuples of the library's layerR, by the rule pl; the sums run over the library's
ranges, with its cuts at the hidden units that are not routed. swap: a false variant that swaps the
two indices of a matrix; x0r: the first entry of the routed G and U in their segments. -/
def tnW (pl : PlaceW) (swap : Bool) (x0r : ℕ) (c : ClaimEnv) (sn : String) (loop lam : ℕ) : E :=
  let y := c.v.y
  let h := y.h
  let P := parW h
  let us := units P
  let k := c.wsLay.lk
  let n := first P (c.v.lay lam) + offW sn loop lam
  match us[n]? with
  | none => zeroE
  | some U =>
    let w := wgtW pl k us n U
    let fSh := if lam % 2 == 1 then h.fe else h.f
    let ew := ewSeg c.v sn
    let two (nc cutIn nx : ℕ) : E :=
      let ec := eqLow c.rs 0 (ceilLog2 nc)
      sumW nc fun j =>
        if j < cutIn then
          mulE (ec.getD j zeroE)
            (sumW nx fun x => mulE (ew.getD x zeroE) (w (if swap then [x, j] else [j, x])))
        else zeroE
    let three (nc nx x0 : ℕ) : E :=
      let ec := eqLow c.rs 0 (ceilLog2 nc)
      let er := eqLow c.rs (ceilLog2 nc) (ceilLog2 nc + ceilLog2 h.NE)
      sumW h.NE fun e => mulE (er.getD e zeroE) (sumW nc fun j => mulE (ec.getD j zeroE)
        (sumW nx fun x => mulE (ew.getD (x0 + x) zeroE) (w [j, e, x])))
    if loop == 0 then
      if sn == "G" || sn == "U" then two h.d h.d fSh
      else if sn == "V" then two h.d h.d y.dkv
      else if sn == "O" then two y.dq y.dq h.d
      else if sn == "D" then two h.f fSh h.d
      else two h.d h.d h.NE
    else if sn == "QK" then
      let hk := headW c lam
      let ec := eqLow c.rs 0 (ceilLog2 h.d)
      sumW h.d fun j => mulE (ec.getD j zeroE) (sumW (h.H + h.Gk) fun hd => sumW h.dh fun x =>
        mulE (mulE (hk.1.getD hd zeroE) (hk.2.getD x zeroE)) (w [hd, x, j]))
    else if sn == "D" then three h.fe h.d 0
    else three h.d h.fe x0r

/-- W4. Every claim's value as the verifier settles it on madeW is the library's value of the tensor
claim, with the weights read by the rule pl. only: which segments are looked at. -/
def w4 (pl : PlaceW) (swap : Bool) (x0 : Shape → ℕ) (only : String → ℕ → Bool) (r : RunW) : Bool :=
  let y := r.ce.v.y
  ((namesW (descW y r.TS)).zip r.cl).all fun z =>
    !only z.1.1 z.1.2.1 ||
      settledW r.ce.wsLay z.2 == tnW pl swap (x0 y.h) r.ce z.1.1 z.1.2.1 z.1.2.2

/-- W6. The panel of the down product. On a layer with routed experts the claim's group kk has fe
indices, on another layer f, while the panel has f columns on every row; and the claim's unit is the
one whose first coordinate has that size in the library's list. -/
def w6 (r : RunW) : Bool :=
  let y := r.ce.v.y
  let us := units (parW y.h)
  ((namesW (descW y r.TS)).zip r.cl).all fun z =>
    !(z.1.1 == "D" && z.1.2.1 == 0) ||
      match r.ce.wsLay.U[z.2.ui]?, us[z.2.ui]? with
      | some u, some U =>
        let R := if z.1.2.2 % 2 == 1 then y.h.fe else y.h.f
        (u.g.head?.map fun g => (g.name, g.R)) == some ("kk", R) &&
          (U.coords.head?.map (·.R)) == some R &&
          (z.2.f.head?.map fun x => x.HV.size * 2 ^ x.pt.size) == some R
      | _, _ => false

/-! ## W8: the merge's identities -/

/-- W8. At a made-up point rm that is not Boolean and made-up coefficients rho: each claim's factor
on the columns at rm is the sum over the Boolean columns C of the equality weight of C at rm times
the factor at C; and the sum over the claims of rho, the factor at rm and the claim's rows of madeW
read at rm is the sum over the rows of W of the coefficients that wsGammaAdd adds up, as the pending
row has them, times the row read at rm. -/
def w8 (r : RunW) : Bool :=
  let lay := r.ce.wsLay
  let rm := elemsR 1300 lay.lk
  let rho := elemsR 1400 r.cl.length
  let eqs := (Array.range (2 ^ lay.lk)).map fun C => eqAtW lay.lk rm C
  let rowAt (y : ℕ) : E := sumW (2 ^ lay.lk) fun C => mulE (eqs.getD C zeroE) (madeW y C)
  let rows := (Array.range lay.m0).map rowAt
  (r.cl.all fun c =>
    wsEpsT lay c rm == sumW (2 ^ lay.lk) fun C =>
      mulE (eqs.getD C zeroE) (wsEpsT lay c (bitsW lay.lk C))) &&
  (let recs := r.cl.zipIdx.map fun x =>
      wsRowPart lay x.1 (mulE (rho.getD x.2 zeroE) (wsEpsT lay x.1 rm))
   match recs.foldlM (fun G c => wsGammaAdd G lay c oneE) (Array.replicate lay.m0 zeroE) with
   | .error _ => false
   | .ok Gam =>
     (sumW lay.m0 fun y => mulE (Gam.getD y zeroE) (rows.getD y zeroE)) ==
       (r.cl.zipIdx.foldl (fun s x =>
         match lay.U[x.1.ui]? with
         | none => s
         | some u =>
           let g1 := wsGamma u (wsRowPart lay x.1 oneE) oneE
           addE s (mulE (mulE (rho.getD x.2 zeroE) (wsEpsT lay x.1 rm))
             (sumW u.rows fun y => mulE (g1.getD y zeroE) (rows.getD (u.off + y) zeroE)))) zeroE))

/-! ## The run -/

/- the numbers: shapeW is wsShapeR of the layout, and agrees with the library's parameters -/
#guard (match layout hR pcR with
  | .ok y => sameW (shapeW hR) (wsShapeR y) && sizedW (shapeW hR) (parW hR) && hR.p3
  | .error _ => false)

/- W1 -/
#guard [4, 6, 9, 11].all fun lk => w1 hR lk
#guard ([4, 6, 9, 11].map fun lk => (layW hR lk).map fun lay => (lay.U.size, lay.m0)) ==
  [some (66, 3552), some (66, 928), some (66, 192), some (66, 160)]

/- W2 -/
#guard w2 placeL 1 hR 6 [1, 2, 3, 5, 9, 11, 13, 14, 15, 64, 65] && w2 placeL 37 hR 6 [0, 6]
#guard w2 placeL 1 hR 4 [3, 5, 11, 14, 64, 65] && w2 placeL 41 hR 4 [0]
#guard w2 placeL 1 hR 9 [3, 11, 14] && w2 placeL 1 hR 11 [11, 64]

/- W3 -/
#guard [4, 6, 9].all fun lk => w3 hR lk (List.range 16 ++ [64, 65])

/- controls: three false rules for the place of a digit -/
#guard !w2 placeBadA 1 hR 4 [11] && !w2 placeBadB 1 hR 6 [3] && !w2 placeBadC 1 hR 6 [3]

/- with 6 column bits unit 11 leaves 1, 1 and 8 values to the rows: there the order of the groups
cannot show, and the first false rule is the true one -/
#guard w2 placeBadA 1 hR 6 [11] &&
  ((layW hR 6).bind fun lay => lay.U[11]?.map fun u => u.g.map (·.left)) == some [1, 1, 8] &&
  ((layW hR 4).bind fun lay => lay.U[11]?.map fun u => u.g.map (·.left)) == some [1, 2, 16]

/- controls: the two indices of a matrix swapped; the routed gate read from entry 0 on -/
#guard !withW hR pcR 6 (w4 placeL true (·.fe) fun sn l => sn == "V" && l == 0)
#guard !withW hR pcR 6 (w4 placeL false (fun _ => 0) fun sn l => sn == "G" && l == 1)

end OnBytes.Road
