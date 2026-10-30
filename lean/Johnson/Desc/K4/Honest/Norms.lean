-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Norms.lean: the norms' stretch of the layers' own rounds, the prover's side.

WHAT IT DOES NOT SHOW. No law and no test here: that the values made here meet the verifier's claims
on the norms (groups 2 to 6 of docs/format/11-2-feed-forward-segment.md) is not shown here. Nothing
here masks a value or plays a round: these are the TRUE values, which the prover's part takes into
its row (Johnson/Desc/ProofFile/Honest/K4/Part.lean); what it sends of them is that file's text.
Nothing says that the cells are a model's run: the functions take any cells. THE PLAN IS TAKEN TO BE
ONE THAT THE VERIFIER's TEXT COVERS (five limbs: seven products of four fields a norm); at another
plan the lists have other lengths than its rounds ask.

WHAT IT DEFINES. Between the lookup and the second sumcheck over the tokens the prover sends, in
this order (OnBytes/Desc/First/K4/Rounds.lean, items 2 and 3; Hear.lean: hearNorms):
  wSums        the sums of limb products W(i, s) of all norms at the norms' token point
  jobSquares   a masked sumcheck over a product layer: the squares of the streams' limbs, batched
  rowProducts  the row products P(i, r) of all norms at the same point
  jobRows      a masked sumcheck over the tokens on these products
Definitions with code. No theorem.

Where the numbers come from. The streams' limbs are read straight from the cells (Cells.lean,
item 6). The four fields a, b, Rlo, Rhi of a norm's row at a token are THE VERIFIER's OWN FORMS
(digitsAt, OnBytes/Desc/First/K4/Claims.lean; Row.ofDigits, OnBytes/Desc/First/P6/NormRow.lean),
valued on the reads at the corner of that token. The product layer's point is the verifier's
(normsStart), which products are formed is the verifier's list (P6.rowProducts), and the second
sumcheck's summand on end values is the verifier's function (rowsSummand).

Limits. A value that has not been sampled yet is an empty array in Pts, and nothing here asks
whether a value has been sampled. Called before the norms' token point PV is sampled, wSums and
rowProducts return token 0's own sums and products (the equality table of the empty point is the one
weight 1); powers that lack count as 0; jobSquares and jobRows yield nothing while their points
together have not the length that the plan asks. In the prover's row each of the four stands behind
the rounds in which what it reads is sampled. No function divides by a sampled value. rowMaps, and
so jobRows, yields nothing, and rowProducts the empty list, where a public thing lacks: the number
of the array of the reads in the plan, the tensor of the rows, a table's name, the laying of the
tables; and where an entry that a row's form names is refused, by the verifier's U3at
(OnBytes/Model/LayerForms.lean: the entry lies beyond its family; the array of the reads has no
column; the entry's row does not fit 32 bits) or by valAff? (no family holds the entry, or its
family has not its weights: wtsFit, Cells.lean). These read public numbers alone. Each call makes
its tables anew.
Nothing on any property.
No property is claimed.
-/
import Johnson.Desc.K4.Honest.Cells
import Johnson.Desc.K4.Honest.Cube
import OnBytes.Desc.First.K4.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest
open OnBytes
open OnBytes.Model (Aff eqTab ledNS orderDefault)
open OnBytes.Model.Layer (Env Heard normsStart)

/-! ## The sums of limb products, and their squares' layer -/

/-- The sums of limb products of norm i at token t, in the field: member s is the sum, over the
features j < d and the ordered pairs (lb, lc) with lb + lc = s, of limb lb times limb lc of the
stream that the norm reads. Norm i reads stream i. -/
def limbSumsAt (Q : K4Pub) (w : K4In) (i t : Nat) : Array F :=
  let y := Q.P.y
  let xl := y.h.xl
  let xs := tensorOf y "xs"
  (List.range y.h.d).foldl
    (fun acc j =>
      let L := (Array.range xl).map fun lb => streamLimb y w.cell xs i lb j t
      (List.range xl).foldl
        (fun acc lb =>
          (List.range xl).foldl
            (fun (acc : Array F) lc =>
              acc.modify (lb + lc) fun v => addF v (mulF (L.getD lb 0) (L.getD lc 0)))
            acc)
        acc)
    (Array.replicate (ledNS xl) 0)

/-- **The sums of limb products**: W(i, s) is the sum over the tokens t of eq(PV, t) times member s
of limbSumsAt at (i, t). By norm, within a norm by s. -/
def wSums (Q : K4Pub) (w : K4In) (p : Pts) : List E :=
  let y := Q.P.y
  let n := ledNS y.h.xl
  let e := eqTab p.PV
  (List.range y.NI).flatMap fun i =>
    ((List.range y.T).foldl
      (fun (acc : Array E) t =>
        let c := limbSumsAt Q w i t
        let k := e.getD t zeroE
        (Array.range n).map fun s => maddS (acc.getD s zeroE) (c.getD s 0) k)
      (Array.replicate n zeroE)).toList

/-- The table of the squares' layer: at the index (i Pd + j) T + t the sum over the limbs lb of
gp[lb] times limb lb of stream i at feature j and token t; 0 for d ≤ j and for NI ≤ i. -/
def squaresTab (Q : K4Pub) (w : K4In) (gp : Array E) : Tab :=
  let y := Q.P.y
  let xs := tensorOf y "xs"
  (Array.range (2 ^ Q.P.rd.muV)).map fun x =>
    let t := x % y.T
    let j := x / y.T % y.Pd
    let i := x / y.T / y.Pd
    if j < y.h.d && i < y.NI then
      (List.range y.h.xl).foldl
        (fun s lb => maddS s (streamLimb y w.cell xs i lb j t) (gp.getD lb zeroE)) zeroE
    else zeroE

/-- **The masked sumcheck over the squares' product layer.** One table, multiplied by itself, summed
at the verifier's point (rhoI, then 1/2 for each bit of a feature, then PV), the highest bit first.
Its two end values are that one table's value at the challenges, and its summand on two end values
is their product, as the verifier's levelIn forms it (OnBytes/Model/Psc.lean). Nothing unless rhoI
and PV together have the length that the plan asks; the number of the powers gp is not asked. -/
def jobSquares (Q : K4Pub) (w : K4In) (p : Pts) : Option Job :=
  let mu := Q.P.rd.muV
  let cube : Cube :=
    { n := mu, order := orderDefault mu, way := .point (normsStart Q.P.y 0 p.gp p.rhoI p.PV).2
      maps := #[squaresTab Q w p.gp], pairs := [(oneE, 0, 0)] }
  if cube.fits then
    some
      { lead := [], cube, dY := 2
        ends := fun rs => let v := (cube.valuesAt rs).getD 0 zeroE; [v, v]
        atEnds := fun _ e => mulE (e.getD 0 zeroE) (e.getD 1 zeroE) }
  else none

/-! ## The row products, and their sumcheck over the tokens -/

/-- The verifier's forms of the fields a, b, Rlo, Rhi of each norm's row, in the reads at the point
named r_tV: four a norm, by norm. -/
def rowForms (v : Env) : Option (Array Aff) :=
  ((List.range v.y.NI).mapM fun i =>
    (digitsAt v "r_tV" i).map fun D =>
      let f := P6.Row.ofDigits D
      [f.a, f.b, f.Rlo, f.Rhi]).map fun l => l.flatten.toArray

/-- **The rows' fields as tables on the tokens**: table 4 i + k holds field k of norm i's row: the
verifier's form, valued on the reads with the point r_tV laid at the token's bits. -/
def rowMaps (Q : K4Pub) (w : K4In) (p : Pts) : Option (Array Tab) := do
  let v ← envOf Q p
  let fs ← rowForms v
  let lt := Q.P.y.h.lt
  let Rs ← (Array.range (2 ^ lt)).mapM fun t => readsAt Q w p.fo [("r_tV", bitsOf lt t)]
  fs.mapM fun f => Rs.mapM fun R => valAff? v R (fun _ => zeroE) f

/-- **The row products**: P(i, r) is the sum over the tokens t of eq(PV, t) times product r of norm
i's row at t. By norm, within a norm by r. -/
def rowProducts (Q : K4Pub) (w : K4In) (p : Pts) : List E :=
  match rowMaps Q w p with
  | none => []
  | some ms =>
    let e := eqTab p.PV
    (List.range Q.P.y.NI).flatMap fun i =>
      P6.rowProducts.map fun x =>
        let ta := ms.getD (4 * i + x.1) #[]
        let tb := ms.getD (4 * i + x.2) #[]
        (List.range Q.P.y.T).foldl
          (fun s t => maddE s (e.getD t zeroE) (mulE (ta.getD t zeroE) (tb.getD t zeroE))) zeroE

/-- The verifier's structure for what it has heard, with the fields laid that its public functions
on the norms read: the sampled values. The two first slots' numbers (sW, sPv), which have no
default, are laid as 0; of the two sumchecks' states the challenges alone are laid; every other
field keeps its default. -/
def heardOf (Q : K4Pub) (p : Pts) : Heard :=
  { fo := p.fo, PV := p.PV, ZE := p.ZE, tkh := p.tkh, ztF := ztOf Q p, sW := 0, gp := p.gp
    wpl := { r := p.r6 }, sPv := 0, omV := p.omV, tV := { r := p.rtV } }

/-- **The masked sumcheck over the tokens on the row products.** The summand is the sum over the
norms i and the products r of omV[7 i + r] times product r of norm i's row; it is summed at PV, the
highest bit first. The lead is the claimed sum. The end values are all rows' four fields at the
challenges. -/
def jobRows (Q : K4Pub) (w : K4In) (p : Pts) : Option Job := do
  let y := Q.P.y
  let ms ← rowMaps Q w p
  let pairs := (List.range y.NI).flatMap fun i =>
    P6.rowProducts.zipIdx.map fun x =>
      (p.omV.getD (7 * i + x.2) zeroE, 4 * i + x.1.1, 4 * i + x.1.2)
  let cube : Cube :=
    { n := y.h.lt, order := orderDefault y.h.lt, way := .point p.PV, maps := ms, pairs }
  if cube.fits then
    pure
      { lead := [cube.total], cube, dY := 2
        ends := fun rs => (cube.valuesAt rs).toList
        atEnds := fun _ e => rowsSummand y (heardOf Q p) e.toArray }
  else none

end OnBytes.Desc.First.K4.Honest
