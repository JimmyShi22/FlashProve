-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysRunP.lean: the panels of a layer sub-proof's batched sumcheck, the verifier's
against the library's, evaluated on made-up numbers.

A key of the lookup holds products of two hidden values and matrix products with weights. The
verifier's form for a call's factor in the lookup's join leaves them out. They are proved by a
batched sumcheck whose summand is a product of two long vectors, made of panels
(OnBytes/Model/LayerPanels.lean). The library has its own list of panels, with each panel's share in
the sum (pans, Pan.share, Sig0, Sig1 in Inst/Model/FF/Objects.lean). This file runs the two against
each other.

Every line "#guard" is evaluated when this file is compiled, by Lean's interpreter, and the
compilation fails if the value is not true. It is a run. It is no theorem: nothing that only a guard
shows can be used in a proof. This file holds no theorem.

How the library's side is computed. The library's definitions are written over any field. Here they
are evaluated as they stand, over the integers modulo the verifier's prime (KP := Code.FGold): no
formula of the library is copied. The verifier's side is computed in the verifier's field, with all
made-up elements in its base field; valF reads such an element in KP, and inBase tests that a result
lies in the base field. On that side shareRun, rP and wvP are copies, written in the verifier's
field, of shareP and rPort (Johnson/Road/FormsKeysPort.lean) and of wvOf
(Johnson/Road/FormsKeysWv.lean): these three definitions themselves are not evaluated.

The numbers. The shape hR8 and the calls pcR8 of Johnson/Road/FormsKeysRun8.lean, whose eight lines
of calls are the library's; for one comparison the shape hR and the five calls pcR of
Johnson/Road/FormsKeysRun.lean. Both groups of layers. The points of heardR8, tied as the lookup
ties them; the library's point z is the lookup's point inside a tree followed by its point over the
trees' numbers, and zh is the end point of the second token sumcheck. dimP h: the sizes dimV h 16 of
Johnson/Road/FormsKeysAimV.lean: they agree with the shape and have the verifier's cap on a tree's
depth and the made-up vocabulary of 16 tokens. The table of scales sclOf of the made-up words klR.
Made-up cells (cellN), which the library reads by its own names (cellsOf) and the verifier through
the reads: entry e of the reads holds what a true table holds for these cells (entryP). A made-up
matrix of weights with 6 column bits, which the library reads by layerR. The rotary tables are the
verifier's (ropeC) on both sides.

What is run, and what is compared with what.
 P1  the verifier's list of panels against the library's list pans, in order: selector, claim, rows,
     columns, bits, whether the B side is a weight matrix, the never-sent vector. The numbers do not
     tell G, U and V apart, nor Gr and Ur, N1 and N2, DD and MR: P3 and P4 do.
 P2  the first places that placePanels gives against the library's offP; panTotal; lamS.
 P3  which sent values of the second token sumcheck stand as constants in which panel. The numbers
     are compared with this file's reading of claimsTerms (OnBytes/Model/Layer.lean), which is not
     run.
 P4  the depth of a tree and the bits of a tree's number; each panel's call's weight, computed as
     the lookup computes it (callWeight), against the library's wc; each row's weight against
     Pan.wt.
 P5  each panel's share, as the third clause of stack_slots (Johnson/Road/FormsKeysEnd.lean) writes
     it without the claim's weight, against the library's Pan.share at the record rP: the true
     contractions of the made-up cells, but the SENT values of the second token sumcheck for R2,
     sc2 and sel2, and the run's never-sent vectors for hh1 and hh2. Sent values and vectors are
     made up.
     The vector of a weight claim is read in the made-up W from the verifier's own claim, with the
     factors on the groups kk and e taken out (wvAt). wvAt takes the claim's unit, groups and
     factors from the verifier, and the address of a weight in W from the library's place. So both
     sides read W by the library's rule: P5 says nothing on the verifier's layout of W.
 P6  with honest sent values and never-sent vectors (sentP): the sum of the shares of the verifier's
     panels of the second token sumcheck against the library's Gpos at that sumcheck's end point;
     the shares of the panels O, V and LR against the library's ACC under the weights wc and el.
 Controls, each of which must fail: XR's sent value off by one; the selector's two indices swapped;
 in the library's list Gr and Ur swapped, G and U, G and V, DD and MR (P4); the rows' weights left
 out of the down product's panel; the two rotary tables swapped in the library's share of QK.
 At hR and pcR, where the segments stand in another order in five calls, the verifier's list holds
 the same numbers in another order, and other places.

The library's Sig0 and Sig1 are by their definitions the sums of Pan.share over the early and the
late panels; they are not evaluated here.

What stands between the two sides and is this file's own: valF, toE, zP, zhP, rP, entryP, evalP,
wvP, wvAt, shareRun, the numbers in descL and p3.

What is made up: all numbers of the shapes, the calls of pcR, the scales, every element that stands
for a challenge, a point, a sent value or a never-sent vector, the cells, the weights. None is taken
from a parameter file.

What is not claimed. Nothing is said of any other shape. No proof is made or checked. Not run: the
verifier's routines that read messages (hearTerms, hearStack, joinStart, claimsTerms, stackEnd), so
nothing on masks, on slots, or on the start form of the batched sumcheck; the library's ACC for G, U
and D, for its cost; that the reads are true; the rotary tables against the library's. The program
does not import this file.

Where the guards stand. All here, but the guard on P6, which is not here.
-/
import Johnson.Road.FormsKeysRunW
import Johnson.Road.FormsKeysAimV

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Aff eqTab eqLow WsFac WsGrp WsClaim WsLay wsLayOf)
open OnBytes.Model.Layer (Lay Shape Env Reads Scales Heard TableAt TableAsk layout scalesOf readsOf
  tableAsks layTables PanelEnv Panels SBlk panelsA panelsT placePanels nEndT stubO pointsOf ropeOf
  ropeC ClaimEnv)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Pan Rd Cell offP panTotal lamS rdTrue valU hhU layerR call wc Sig0 Sig1
  ACC Gpos famsIn el Dk sg eC led)

/-! ## The field in which the library's definitions are evaluated -/

/-- The integers modulo the verifier's prime, as the library has them. The library's definitions are
written over any field; over this one Lean can evaluate them. -/
abbrev KP : Type := Code.FGold

/-- An element of the verifier's field that lies in the base field, read in KP. -/
def valF (x : E) : KP := ((x.c0.toNat : ℕ) : KP)

/-- True if the element lies in the base field. -/
def inBase (x : E) : Bool := x.c1 == 0 && x.c2 == 0

/-- An element of KP as an element of the verifier's field. -/
def toE (x : KP) : E := Model.ofNat x.val

/-! ## The made-up world -/

/-- The made-up cell of matrix mat at feature φ and position i, as a number. -/
def cellN (mat φ i : ℕ) : ℕ := 11 + 3 * mat + 5 * φ + 7 * i + φ * i

/-- The kit's number of the matrix of a family of tables, from the family's name. -/
def matP (n : String) : ℕ :=
  let m := (n.splitOn "@").headD ""
  if m == "af" then 0 else if m == "ad" then 1 else if m == "ar" then 2 else if m == "qa" then 3
  else if m == "xbI" then 4 else 5

/-- A family of tables with what its entries are computed from: first entry, length, matrix, whether
its tables are long, the equality table of the block's coordinates and that of the token's. -/
abbrev FamP : Type := ℕ × ℕ × ℕ × Bool × Array E × Array E

/-- What entry e of the reads holds if every table is true of the made-up cells: for a short table
the sum over the positions under the token point's weights; for a long one also over the features of
the block. 0 outside all families. -/
def entryP (S2 T : ℕ) (fs : List FamP) (e : ℕ) : E :=
  match fs.find? fun f => decide (f.1 ≤ e) && decide (e < f.1 + f.2.1) with
  | none => zeroE
  | some (first, _, mat, lng, lo, tk) =>
    let φ := e - first
    if lng then
      sumW S2 fun r => mulE (lo.getD r zeroE)
        (sumW T fun i => mulE (tk.getD i zeroE) (Model.ofNat (cellN mat (φ * S2 + r) i)))
    else sumW T fun i => mulE (tk.getD i zeroE) (Model.ofNat (cellN mat φ i))

/-! ## What is evaluated -/

/-- What the runs read, in one group of layers. -/
structure RunP where
  /-- the tables and the calls' points -/
  v : Env
  /-- the points, as heardR8 makes them -/
  H : Heard
  /-- what the lists of panels read -/
  pe : PanelEnv
  /-- the calls with terms in the second token sumcheck -/
  TS : List ℕ
  /-- the verifier's list of panels -/
  pans : Panels
  /-- the families of tables, for entryP -/
  fs : List FamP
  /-- the weight claims' environment -/
  ce : ClaimEnv
  /-- the weight claims -/
  cl : List WsClaim
  /-- the never-sent vectors -/
  hv : ℕ → ℕ → E

/-- The library's sizes for a shape, with the verifier's cap on a tree's depth and the made-up
vocabulary of 16 tokens that shapeW and parW have. -/
def dimP (h : Model.Layer.Shape) : Dim := dimV h 16

/-- The library's point z for the lookup's two points: the point inside a tree, then the point over
the trees' numbers. -/
def zP (H : Heard) : ℕ → KP := fun t =>
  if t < H.fo.zx.size then valF (H.fo.zx.getD t zeroE)
  else valF (H.fo.zy.getD (t - H.fo.zx.size) zeroE)

/-- The end point of the second token sumcheck. -/
def zhP (H : Heard) : ℕ → KP := fun t => valF (((H.tT.map (·.r)).getD #[]).getD t zeroE)

/-- The made-up cells, by the library's names. -/
def cellsP (D : Dim) : Cell → KP := cellsOf D fun mat φ i => ((cellN mat φ i : ℕ) : KP)

/-- The library's table functions with the verifier's rotary table. The three others are not read
here. -/
def tbP (h : Model.Layer.Shape) (sc : Scales) (rope : Array ℕ) : Tables :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun L i j => ropeC h sc rope L i j false,
    fun L i j => ropeC h sc rope L i j true⟩

/-- The made-up matrix of weights of Johnson/Road/FormsKeysRunW.lean, in KP. -/
def wP (y c : ℕ) : KP := ((3 + 17 * y + 1009 * c : ℕ) : KP)

/-- The sent values of the second token sumcheck and the never-sent vectors. honest = false: made-up
elements, all different. honest = true: the true ones for the made-up cells, by the library's own
definitions: the reciprocals, the scores and the selectors' entries at the sumcheck's end point; the
gated products at the lookup's token point and at that end point. -/
def sentP (honest : Bool) (y : Lay) (S : Scl) (H : Heard) : Array E × (ℕ → ℕ → E) :=
  letI : Scl := S
  let D := dimP y.h
  let t := cellsP D
  let n := y.NN * y.Lam
  let NE := y.h.NE
  if honest then
    ((Array.range (nEndT y)).map fun i =>
      toE (if i < n then Blocks.ext D.lT (fun p => Inst.Model.Ledger.R (led t i p)) (zhP H)
        else if i < n + y.LamM then valU D t .sc (i - n) 0 (zhP H)
        else valU D t .sel ((i - n - y.LamM) / NE) ((i - n - y.LamM) % NE) (zhP H)),
     fun k j =>
      if k == 0 then toE (hhU D t (j / 2 ^ ceilLog2 y.h.f) (j % 2 ^ ceilLog2 y.h.f)
        (Inst.Model.FFSeg.zpos D (zP H)))
      else toE (hhU D t (2 * (k - 1) + 1) (y.h.fe + j) (zhP H)))
  else (elemsR 200 (nEndT y), fun k j => Model.ofNat (5 + 31 * k + 3 * j))

/-- Evaluates f in each group of layers, on the verifier's own list of panels and weight claims, at
made-up points that are tied as the lookup ties them (heardR8), with the calls' weights that the
lookup computes from its point (callWeight). The array of the reads has as many columns as entries,
as in a plan. Returns f's list for each group; an empty list where one of the verifier's functions
does not return. -/
def withP (honest : Bool) (h : Model.Layer.Shape) (pc : List (List String))
    (f : RunP → List Bool) : List (List Bool) :=
  let r : Except String (List (List Bool)) := do
    let y ← layout h pc
    let sc ← scalesOf h klR
    let rd ← readsOf y
    let wsLay ← wsLayOf (shapeW h) h.p3 6
    let rope ← ropeOf h
    pure ((List.range y.NGr).map fun g =>
      let o : Option (List Bool) := do
        let t ← layTables (matsR y g) (tableAsks y rd g) 0
        let H := heardR8 y rd g
        let v : Env := { y, sc, g, iU3 := 0, K3 := t.2.2, tab := t.1, zk := H.fo.zk }
        let sent := sentP honest y (sclOf h sc g y.Lam) H
        let pe : PanelEnv :=
          { v, e := (Array.range y.fo.NC).map (Model.Forest.callWeight y.fo H.fo.zy),
            shownT := sent.1, zt := H.ztF, stubO := stubO y }
        let TS ← rd.tscCalls.mapM y.callNo
        let pans ← panelsT pe TS (panelsA pe {})
        let pts ← pointsOf y H { r := elemsR 3100 rd.muH } (some { r := elemsR 3200 rd.muH2 })
        let fs : List FamP := (t.1.zip t.2.1).map fun x =>
          let P := ((pts.find? fun p => p.1 == x.2.1.point).map (·.2)).getD #[]
          (x.1.first, x.1.len, matP x.1.name, x.2.1.lng,
            eqTab (P.extract 0 y.ls), eqTab (if x.2.1.lng then P.extract y.ls P.size else P))
        let ce : ClaimEnv :=
          { v, wsLay, rope, rs := elemsR 400 (ceilLog2 (placePanels pans.bl).2),
            rt := (H.tT.map (·.r)).getD #[] }
        let cl ← ce.weightClaims TS
        pure (f { v, H, pe, TS, pans, fs, ce, cl, hv := sent.2 })
      o.getD [])
  match r with
  | .ok b => b
  | .error _ => []

/-! ## P1, P2: the list and the places -/

/-- A panel's numbers: whether its rows carry the selector; 0 for a panel of the lookup's join, 1
for one of the second token sumcheck; rows; columns; the bits of a column's number; the bits of a
place; whether its B side is a weight matrix; the number of its never-sent vector. -/
abbrev DescP : Type := Bool × ℕ × ℕ × ℕ × ℕ × ℕ × Bool × Option ℕ

/-- The numbers of a panel of the verifier's. -/
def descP (b : SBlk) : DescP := (b.tri, b.claim, b.ni, b.ny, b.wy, b.w, b.v0.isSome, b.virt)

/-- The numbers of a panel of the library's. The never-sent vectors: number 0 for the panel of the
down product, 1 + l' for that of the routed experts' down product in layer 2 l' + 1: the library has
Hh1 and one vector Hh2 over all l'. -/
def descL (D : Dim) (p : Pan) : DescP :=
  (p.three, if p.late then 1 else 0, p.nr D, p.nc D, p.wcol D, p.wid D, p.weight,
    match p with
    | .D => some 0
    | .Dr l' => some (1 + l')
    | _ => none)

/-- P1. The verifier's list of panels is the library's list pans, in its order. -/
def p1 (r : RunP) : Bool :=
  r.pans.bl.toList.map descP == (Inst.Model.FFSeg.pans (dimOf r.v.y.h)).map (descL (dimOf r.v.y.h))

/-- P1, weaker: the two lists hold the same numbers, in some order. -/
def p1Perm (r : RunP) : Bool :=
  (r.pans.bl.toList.map descP).isPerm
    ((Inst.Model.FFSeg.pans (dimOf r.v.y.h)).map (descL (dimOf r.v.y.h)))

/-- P2. The first places that placePanels gives are the library's offP; the number of all places is
panTotal; its logarithm, rounded up, is lamS. -/
def p2 (r : RunP) : Bool :=
  let D := dimOf r.v.y.h
  let pl := placePanels r.pans.bl
  pl.1.toList.map (·.off) == (Inst.Model.FFSeg.pans D).map (offP D) && pl.2 == panTotal D &&
    ceilLog2 pl.2 == lamS D

/-! ## P3: which sent values stand in which panel -/

/-- The A side of a panel at (row, column) if it is a constant form. -/
def constA (b : SBlk) (i yv : ℕ) : Option E :=
  ((b.A.bind fun A => A i yv).bind fun a =>
    if a.ents.isEmpty && a.slots.isEmpty then some a.const else none)

/-- P3. Panel by panel, along the library's list: the constants of the A side are these sent values
of the second token sumcheck, counted from its first end value: in N1 and N2, row l: number 2 l and
2 l + 1; in XR, row l': number n + l', n = NN Lam; in DD and MR, row l', column e: number
n + LamM + l' NE + e; the selector's factors of Gr l', Ur l', Dr l': the same numbers. By the text
of claimsTerms (OnBytes/Model/Layer.lean) the hidden values under these numbers are claimed to be
the reciprocal of norm number i (i below n), the score of layer l' and entry e of the selector of
layer l'. The A sides of the other panels are no constants. off: added to XR's number, for a
control; tr: the selector's two indices swapped, for a control. -/
def p3 (off : ℕ) (tr : Bool) (r : RunP) : Bool :=
  let y := r.v.y
  let NE := y.h.NE
  let n := y.NN * y.Lam
  let sh (i : ℕ) : Option E := r.pe.shownT[i]?
  let sel (l' e : ℕ) : ℕ := n + y.LamM + (if tr then e * y.LamM + l' else l' * NE + e)
  (r.pans.bl.toList.zip (Inst.Model.FFSeg.pans (dimOf y.h))).all fun x =>
    let b := x.1
    match x.2 with
    | .N1 => (List.range y.Lam).all fun l => constA b l 0 == sh (2 * l)
    | .N2 => (List.range y.Lam).all fun l => constA b l 0 == sh (2 * l + 1)
    | .XR => (List.range y.LamM).all fun l' => constA b l' 0 == sh (n + l' + off)
    | .DD | .MR =>
      (List.range y.LamM).all fun l' => (List.range NE).all fun e => constA b l' e == sh (sel l' e)
    | .Gr l' | .Ur l' | .Dr l' =>
      b.sl.size == NE && (List.range NE).all fun e => b.sl[e]? == sh (sel l' e)
    | .D => b.A.isNone
    | _ => (constA b 0 0).isNone && (b.A.bind fun A => A 0 0).isSome

/-! ## P4: the weights -/

/-- The library's record of what the panels read, for a run: the true contractions of the made-up
cells (rdTrue), but the run's never-sent vectors for hh1 and hh2, and for R2, sc2 and sel2 the sent
values of the second token sumcheck. -/
def rP (r : RunP) (S : Scl) : Rd KP :=
  letI : Scl := S
  let y := r.v.y
  let D := dimP y.h
  let n := y.NN * y.Lam
  let sh (i : ℕ) : KP := valF (r.pe.shownT.getD i zeroE)
  { rdTrue D (cellsP D) (zP r.H) (zhP r.H)
      (fun l j => valF (r.hv 0 (l * 2 ^ ceilLog2 y.h.f + j)))
      (fun l' j => valF (r.hv (1 + l') j)) with
    R2 := fun ν => sh ν
    sc2 := fun l' => sh (n + l')
    sel2 := fun l' e => sh (n + y.LamM + l' * y.h.NE + e) }

/-- The table of scales of the run's group. -/
@[reducible] def sclP (r : RunP) : Scl := sclOf r.v.y.h r.v.sc r.v.g r.v.y.Lam

/-- P4. The library's depth of a tree and number of bits of a tree's number are the verifier's.
Panel by panel, along the list ps of the library's panels: the call's weight is the library's wc at
the panel's call; the weight of each row is the library's Pan.wt. -/
def p4 (ps : Dim → List Pan) (r : RunP) : Bool :=
  letI : Scl := sclP r
  let y := r.v.y
  let D := dimP y.h
  let z := zP r.H
  Dk D == y.fo.dT && sg D == y.fo.rK &&
  (r.pans.bl.toList.zip (ps D)).all fun x =>
    let b := x.1
    let p := x.2
    valF b.ec == wc D z (call p.fam) && inBase b.ec &&
      (List.range (if b.tri then 1 else b.ni)).all fun i =>
        valF (b.wt.getD i zeroE) == p.wt D z i && inBase (b.wt.getD i zeroE)

/-- The library's list with two kinds of panels swapped, for a control: 0: Gr and Ur; 1: G and U;
2: G and V; 3: DD and MR. These are the kinds that P1's numbers do not tell apart, but for N1 and
N2, which have one weight and are told apart by P3. -/
def pansSwap (mode : ℕ) (D : Dim) : List Pan :=
  (Inst.Model.FFSeg.pans D).map fun p =>
    match mode, p with
    | 0, .Gr l' => .Ur l'
    | 0, .Ur l' => .Gr l'
    | 1, .G => .U
    | 1, .U => .G
    | 2, .G => .V
    | 2, .V => .G
    | 3, .DD => .MR
    | 3, .MR => .DD
    | _, q => q

/-! ## P5, P6: the sums -/

/-- The value of a form in the made-up world. The panels' forms name no slot; a form that does is
valued without its slots, and noSlots tells. -/
def evalP (r : RunP) (a : Aff) : E :=
  a.ents.foldl
    (fun s x => addE s (mulE x.coef (entryP r.v.y.S2 r.v.y.T r.fs (x.row * r.v.K3 + x.idx))))
    a.const

/-- The vector of a weight claim at a place: the sum that the claim speaks of, in the made-up W,
with the groups for which fix gives an index held at that index and their factors left out. 0 if the
index is not below the group's size. -/
def wvP : List (WsFac × WsGrp) → (String → Option ℕ) → (List ℕ → E) → E
  | [], _, F => F []
  | (x, g) :: rest, fix, F =>
    match fix g.name with
    | some v => if v < g.R then wvP rest fix (fun idx => F (v :: idx)) else zeroE
    | none => sumW g.R fun v => mulE (facE x g v) (wvP rest fix fun idx => F (v :: idx))

/-- The vector of weight claim number n at column yv, and for a panel with the selector at row e. -/
def wvAt (r : RunP) (n : ℕ) (e : Option ℕ) (yv : ℕ) : E :=
  let lay := r.ce.wsLay
  let us := Inst.Model.Layout.units (parW r.v.y.h)
  match r.cl[n]? with
  | none => zeroE
  | some c =>
    match lay.U[c.ui]?, us[c.ui]? with
    | some u, some U =>
      wvP (c.f.zip u.g) (fun nm => if nm == "kk" then some yv else if nm == "e" then e else none)
        (wgtW placeL lay.lk us c.ui U)
    | _, _ => zeroE

/-- The share of one panel of the verifier's, without the weight of its claim, as the third clause
of stack_slots (Johnson/Road/FormsKeysEnd.lean) writes it: the call's weight times the sum over the
rows of the row's weight times the inner product of what is left of the two sides. noWt: the rows'
weights of the down product's panel left out, for a control. -/
def shareRun (noWt : Bool) (r : RunP) (b : SBlk) : E :=
  let NE := r.v.y.h.NE
  let side (S : Option (ℕ → ℕ → Option Aff)) (i yv : ℕ) : E :=
    ((S.bind fun A => A i yv).map (evalP r)).getD zeroE
  mulE b.ec (sumW (if b.tri then NE else b.ni) fun i =>
    let rowW := if b.tri then mulE (b.wt.getD 0 zeroE) (b.sl.getD i zeroE)
      else if noWt && b.virt.isSome then oneE else b.wt.getD i zeroE
    mulE rowW (sumW (2 ^ b.wy) fun yv =>
      let a := match b.tri, b.virt with
        | true, some k => r.hv k yv
        | true, none => if yv < b.ny then evalP r (b.xx.getD yv {}) else zeroE
        | false, some k => r.hv k (i * 2 ^ b.wy + yv)
        | false, none => if yv < b.ny then side b.A i yv else zeroE
      let bb := match b.tri, b.v0 with
        | true, some v0 => wvAt r v0 (some i) yv
        | false, some v0 => wvAt r (v0 + i) none yv
        | false, none => if yv < b.ny then side b.B i yv else zeroE
        | true, none => zeroE
      mulE a bb))

/-- The sum of the shares of the verifier's panels with the given number of their claim. -/
def sumP (noWt : Bool) (r : RunP) (claim : ℕ) : E :=
  (r.pans.bl.toList.filter fun b => b.claim == claim).foldl
    (fun s b => addE s (shareRun noWt r b)) zeroE

/-- The weights of the run's layers, read by the library's layerR in the made-up W. -/
def lwP (r : RunP) : ℕ → Inst.Model.FFSeg.LW KP := fun l =>
  layerR (dimP r.v.y.h).P r.ce.wsLay.lk wP (r.v.g * r.v.y.Lam + l)

/-- The light runs: P1; P2; P3; its two controls fail; P4; its four controls fail. -/
def runA (r : RunP) : List Bool :=
  [p1 r, p2 r, p3 0 false r, !p3 1 false r, !p3 0 true r, p4 Inst.Model.FFSeg.pans r,
    !p4 (pansSwap 0) r, !p4 (pansSwap 1) r, !p4 (pansSwap 2) r, !p4 (pansSwap 3) r]

/-- P5, panel by panel along the library's list. The share of each of the verifier's panels lies in
the base field; it is the library's Pan.share of the panel, evaluated by the library's own
definition at the record rP; no share is 0. The library's Sig0 and Sig1 are by their definitions the
sums of these shares over the early and the late panels. Two controls: without the rows' weights the
share of the down product's panel (number 3) is not the library's; with the two rotary tables
swapped the library's share of the panel QK (number 14) is not the verifier's. -/
def runB (r : RunP) : List Bool :=
  letI : Scl := sclP r
  let y := r.v.y
  let D := dimP y.h
  let tb := tbP y.h r.v.sc r.ce.rope
  let L0 := r.v.g * y.Lam
  let rr := rP r (sclP r)
  let sh := (r.pans.bl.toList.zip (Inst.Model.FFSeg.pans D)).map fun x =>
    (shareRun false r x.1, x.2.share D rr tb L0 (lwP r) (zP r.H) (zhP r.H))
  [sh.length == 18, sh.all fun x => inBase x.1, sh.all fun x => valF x.1 == x.2,
    sh.all fun x => x.2 != 0,
    valF (shareRun true r (r.pans.bl.getD 3 {})) != (sh.getD 3 (zeroE, 0)).2,
    Pan.QK.share D rr ⟨tb.SILU, tb.SIGM, tb.Exp, tb.S, tb.C⟩ L0 (lwP r) (zP r.H) (zhP r.H) !=
      valF (sh.getD 14 (zeroE, 0)).1]

/-- P6, for a run with honest sent values and never-sent vectors. The sum of the shares of the
verifier's panels of the second token sumcheck is the library's Gpos at the sumcheck's end point.
The shares of the verifier's panels number 2, 4 and 5 (O, V and LR in the library's order) are the
sums over the layers of the library's ACC of these families under the weights wc and el. -/
def runC (r : RunP) : List Bool :=
  letI : Scl := sclP r
  let y := r.v.y
  let D := dimP y.h
  let t := cellsP D
  let tb := tbP y.h r.v.sc r.ce.rope
  let L0 := r.v.g * y.Lam
  let z := zP r.H
  let acc (n : ℕ) (s : Inst.Model.FFSeg.Fam) : Bool :=
    valF (shareRun false r (r.pans.bl.getD n {})) ==
      wc D z (call s) * ∑ l ∈ range D.nl,
        if Inst.Model.FFSeg.present s l then el D z (call s) l * ACC D t (lwP r) z s l else 0
  [valF (sumP false r 1) == Gpos D t tb L0 (lwP r) z (zhP r.H), acc 2 .O, acc 4 .V, acc 5 .LR]

/-! ## The run -/

/- P1, P2, P3 with two controls, P4 with four -/
#guard withP false hR8 pcR8 runA == List.replicate 2 (List.replicate 10 true)

/- with five calls in another order: not the library's order, the same numbers, other places -/
#guard (withP false hR pcR fun r => [p1 r, p1Perm r, p2 r]) == List.replicate 2 [false, true, false]

/- P5 with two controls -/
#guard withP false hR8 pcR8 runB == List.replicate 2 (List.replicate 6 true)

end OnBytes.Road
