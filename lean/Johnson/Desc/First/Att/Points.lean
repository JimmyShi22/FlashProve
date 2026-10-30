-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Points.lean: kind K5: what the kind's claims and tables read of what was heard:
the points, the pieces' weights, the numbers of the named scalars and the row that each sumcheck
leaves, as one record. Pure.

Main names:
  `W1`: a piece's layer, head and weight. `SumP`: of a sumcheck: the challenges, the first end
    value's number, the row.
  `RemP`, `ScoreP`, `DivP`, `MaxP`, `Pts`: a unit of which plane values are claimed; a softmax-table
    unit; the division and the value product; the maximum and its index; all four.
  `pointsOf`: the record, from the place's numbers, each call's key point, what was heard and the rows
    (Att/LeftP.lean).
The fields are those that the claims and the tables read of the four records that OnBytes/Model's
routines fill (AttentionHeard.lean); the cuts of the key points follow these routines, and the
accessors follow AttentionHeard.lean:232-302 and AttentionSums.lean:85-88.
The tests are on lengths alone.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.LeftP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes
open OnBytes.Model (Aff)

/-- A piece: its layer, its head in the group, its weight at the call's key point. -/
structure W1 where
  lam : Nat
  a : Nat
  wp : E

/-- The pieces of a unit with their weights, by layer, then by head. After AttentionHeard.lean:92-103. -/
def piecesOf (u : UnitG) (zk : Array E) : Array W1 :=
  ((u.pcs.map fun pc => ({ lam := pc.lam, a := pc.a, wp := eqAt (zk.extract 0 (u.n - pc.b)) (pc.off >>> pc.b) } : W1)).mergeSort
    fun x y => x.lam < y.lam || (x.lam == y.lam && x.a ≤ y.a)).toArray

/-- What the claims read of a masked sumcheck. -/
structure SumP where
  /-- the challenges of its variables' rounds -/
  r : Array E
  /-- the number of its first end value -/
  ends : Nat
  /-- the claim that it leaves -/
  row : Aff

/-- The two end values of member b of a sumcheck of products. -/
def SumP.a (s : SumP) (b : Nat) : Aff := Aff.slot (s.ends + 2 * b)
def SumP.b (s : SumP) (b : Nat) : Aff := Aff.slot (s.ends + (2 * b + 1))

/-- A unit of which plane values are claimed. -/
structure RemP where
  call : Nat
  /-- the unit's inner point -/
  z : Array E
  /-- its list lies on the diagonal -/
  isD : Bool
  pw : Array W1
  /-- the number of the first of its scalars; how many of them are plane values -/
  s0 : Nat
  np : Nat

/-- A unit of a softmax-table call. -/
structure ScoreP where
  call : Nat
  /-- the number of its plane claim in the list -/
  claim : Nat
  below : Bool
  pw : Array W1
  /-- cuts of the inner point: head · tile slot · the query's, the key's place in its tile -/
  zg : Array E
  zs : Array E
  zi : Array E
  zj : Array E
  /-- the tile rows' weights -/
  wI : Array E
  s0 : Nat
  sc : SumP

/-- The division and the value product. -/
structure DivP where
  pwW : Array W1
  pwX : Array W1
  pwH : Array W1
  /-- the call that holds the list wh -/
  qWH : Nat
  zsl : E
  zgW : Array E
  ziW : Array E
  zcW : Array E
  zgX : Array E
  ziX : Array E
  zgH : Array E
  ziH : Array E
  zcH : Array E
  s5 : Nat
  sIB : Nat
  s5h : Nat
  scE : SumP
  gam : E
  sCl : Nat
  vpm : SumP
  /-- the tile columns' weights of the value product below the diagonal -/
  wJv : Array E
  vpd : SumP

def DivP.sACC (d : DivP) : Nat := d.s5
def DivP.sZO (d : DivP) : Nat := d.s5 + 1
def DivP.sZC (d : DivP) : Nat := d.s5 + 2
def DivP.sRH (d : DivP) : Nat := d.s5 + 3
def DivP.sRHP (d : DivP) : Nat := d.s5 + 4
def DivP.zilo (d : DivP) (g : Geo) : Array E := d.ziW.extract g.lnT (g.lnT + g.lB)

/-- The maximum and its index. -/
structure MaxP where
  tg : Array E
  ti : Array E
  sM6 : Nat
  scF : SumP
  scd : SumP
  scH : SumP

def MaxP.ri (x : MaxP) (g : Geo) : Array E := x.scF.r.extract 0 g.lt
def MaxP.rg (x : MaxP) (g : Geo) : Array E := x.scF.r.extract g.lt (g.lt + g.lgk)
def MaxP.rc (x : MaxP) (g : Geo) : Array E := x.scF.r.extract (g.lt + g.lgk) x.scF.r.size
def MaxP.pj (x : MaxP) (g : Geo) : Array E := x.scd.r.extract 0 g.lt
def MaxP.pg (x : MaxP) (g : Geo) : Array E := x.scd.r.extract g.lt (g.lt + g.lgk)
def MaxP.pi (x : MaxP) (g : Geo) : Array E := x.scd.r.extract (g.lt + g.lgk) (2 * g.lt + g.lgk)
def MaxP.sKC (x : MaxP) : Nat := x.scd.ends
def MaxP.sIb (x : MaxP) (g : Geo) (b k : Nat) : Nat := x.scd.ends + (g.Lam + b * g.lt + k)
def MaxP.ri2 (x : MaxP) (g : Geo) : Array E := x.scH.r.extract 0 g.lt
def MaxP.rg2 (x : MaxP) (g : Geo) : Array E := x.scH.r.extract g.lt (g.lt + g.lgk)
def MaxP.rk (x : MaxP) (g : Geo) : Array E := x.scH.r.extract (g.lt + g.lgk) (g.lt + g.lgk + 4)

structure Pts where
  planes : Array RemP
  scores : Array ScoreP
  d : DivP
  x : MaxP

def sumOfP (h : VerifiableInference.Desc.Part.MaskedSum.Heard) (row : Aff) : SumP := { r := chal h, ends := h.sEnd, row := row }

/-- **What the claims and the tables read of what was heard.** zk: each call's key point. L: the rows. -/
def pointsOf (g : Geo) (zk : Array (Array E)) (h : Heard) (L : Left) : Option Pts := do
  let (lgk, lt, ldh, lB) := (g.lgk, g.lt, g.ldh, g.lB)
  let kr := (g.units .kr [.rm, .rd]).toArray
  guard (kr.size == h.remainders.size)
  let planes0 : Array RemP := (kr.zip h.remainders).map fun (u, s0) =>
    let key := zk.getD u.1 #[]
    let un := g.unitAt u.1 u.2.1 u.2.2
    { call := u.1, z := inner un key, isD := u.2.2 == .rd, pw := piecesOf un key, s0 := s0, np := 3 }
  let kfd := g.scores.toArray
  guard (kfd.size == h.scores.size && kfd.size == L.scores.size)
  let (planes, scores) ← ((kfd.zip h.scores).zip L.scores).foldlM (fun (acc : Array RemP × Array ScoreP) ((u, s0, sc), row) => do
    let key := zk.getD u.call #[]
    let pw := piecesOf u key
    let z := inner u key
    let a := lgk + (g.lnT - 1)
    let b := if u.below then a + g.lnT else lgk + g.lnT
    guard (z.size == b + 2 * lB)
    let zP := if u.below then z.extract lgk a else #[]
    let zs := if u.below then z.extract a b else #[]
    let zI := if u.below then #[] else z.extract lgk b
    let wI := if u.below then (tileSums g (eqTab zP) (eqTab zs)).1 else eqTab zI
    pure (acc.1.push { call := u.call, z := z, isD := !u.below, pw := pw, s0 := s0, np := 5 },
      acc.2.push { call := u.call, claim := acc.1.size, below := u.below, pw := pw, zg := z.extract 0 lgk, zs := zs, zi := z.extract b (b + lB),
                   zj := z.extract (b + lB) (b + 2 * lB), wI := wI, s0 := s0, sc := sumOfP sc row })) (planes0, #[])
  let uW ← g.single .wl
  let uX ← g.single .ix
  let uH ← g.single .wh
  let (kW, kX, kH) := (zk.getD uW.call #[], zk.getD uX.call #[], zk.getD uH.call #[])
  let (pwW, pwX, pwH) := (piecesOf uW kW, piecesOf uX kX, piecesOf uH kH)
  let (zW, zX, zH) := (inner uW kW, inner uX kX, inner uH kH)
  guard (pwW.size == g.NP && pwX.size == g.NP && pwH.size == g.NP)
  guard (zW.size == 1 + lgk + lt + ldh && zX.size == lgk + lt && zH.size == lgk + lt + ldh)
  let r := chal h.below
  let atS := lgk + (g.lnT - 1)
  let w := tileSums g (eqTab (r.extract lgk atS)) (eqTab (r.extract atS (atS + g.lnT)))
  let d : DivP :=
    { pwW, pwX, pwH, qWH := uH.call, zsl := zW.getD 0 zeroE, zgW := zW.extract 1 (1 + lgk), ziW := zW.extract (1 + lgk) (1 + lgk + lt)
      zcW := zW.extract (1 + lgk + lt) (1 + lgk + lt + ldh), zgX := zX.extract 0 lgk, ziX := zX.extract lgk (lgk + lt), zgH := zH.extract 0 lgk
      ziH := zH.extract lgk (lgk + lt), zcH := zH.extract (lgk + lt) (lgk + lt + ldh), s5 := h.five, sIB := h.bits, s5h := h.two
      scE := sumOfP h.division L.division, gam := h.gam.getD 1 zeroE, sCl := h.values, vpm := sumOfP h.below L.below, wJv := w.2
      vpd := sumOfP h.on L.on }
  pure { planes, scores, d
         x := { tg := h.point.extract 0 lgk, ti := h.point.extract lgk (lgk + lt), sM6 := h.maxima, scF := sumOfP h.atIndex L.atIndex
                scd := sumOfP h.key L.key, scH := sumOfP h.cells L.cells } }

end VerifiableInference.Desc.First.Att.P
