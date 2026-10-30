-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/K4/Claims.lean: the layers' own rounds, second half: the claims, as lists of
linear forms.

Each claim is a linear form, in the sub-proof's hidden values and in entries of the reads, that must
be 0. The claims are made behind the draw of the element that batches them; claim number c gets its
c-th power, so THEIR ORDER IS PROTOCOL. The groups are those of the format's reference
(docs/format/11-2-feed-forward-segment.md).

EVERY GROUP IS A PLAIN FUNCTION, FROM WHAT WAS HEARD TO A LIST OF FORMS, OR NOTHING WHERE A PUBLIC
VALUE LACKS OR A PUBLIC CONDITION FAILS. No ledger is read or written here, but for three letters
that `front` and `back` take: the values shown for the rows' end values, and the own claims of the
three sumchecks whose claim is made only now (OnBytes/Desc/First/K4/Plain.lean lays these).

  `front`: groups 1 to 12.
      1  the lookup's own (another kind's; listed here, unless rows := false)
      2  `normsForms`: the squares' product layer
      3 to 6  `rowBatchForm`, `rowsForms`: the row products; each norm's shown values, carries and
              lines
      7  `termsForms`: the second token sumcheck's shown values
      8, 9  `gatedForms`: the two product layers of the gated products
      10  `oneHotForms`: a selector's entries sum to 1
      11  `planesParts`: the lookup's three on its planes (typed by the caller, on its own columns)
      12  `embeddingForm`: in the first group, the embedding's value
  (13: the smallness test's, another kind's, stand between the two lists.)
  `back`: groups 14 and 15: the batched sumcheck's three; the merge's one.

The lookup's join and the second token sumcheck's own claim are no claims of their own: both stand
inside the batched sumcheck's start form (`joinStart`, Hear.lean) and are decided by the first claim
of group 14.
LETTERS IN THE DOCSTRINGS BELOW (the format's): NI norms in the group; Lam layers, LamM of them with
routed experts; d, f, fe the widths of the stream, the hidden layer, an expert's hidden layer; Pd,
Pf the next powers of two; S2 features in a block of a long table; la the coordinates of a point at
which a long table is read. eq(z, i): the equality weight of index i at point z. z↑: the point z
without its last la coordinates. x′: what was shown for the hidden value x. "X @ Z": the table of
tensor X read at the point Z. own(n; S0): the one claim that sumcheck n leaves, S0 its summand on
the end values as shown.
NOT HERE. That as many claims were made as the plan says: `claimsCounted` (K4/Steps.lean), called at
the smallness test's quiet step, and asked again at the door. What adding a form to the one equation
asks (the entry that it names exists; the batching element was drawn): the ledger's.
Limits. After OnBytes/Model/Layer.lean's own lines, cut behind `covers`. No law here.
-/
import OnBytes.Model.Layer
import OnBytes.Desc.First.P6.NormRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest

/-- A public condition: nothing where it fails. -/
def need (b : Bool) : Option Unit := if b then some () else none

/-- Group 2, the sums of squares. Three claims:
  own(6; vL′ vR′), on the start form 2^(-lPd) Σ_i Σ_s eq(rhoI, i) gam^s W(i, s);
  vL = vR;
  vL = Σ_i Σ_k Σ_l eq(r6↑, i Pd/S2 + k) gam^l limb_l(i, k),   i < NI, k < d/S2, l < 5,
with the limbs of norm 0 from xbI @ Z_V and those of norm i > 0 from af @ Z_V. It refuses unless
three numbers of the layout's tensors agree. -/
def normsForms (P : Pub) (v : Env) (H : Heard) : Option (List Aff) := do
  let y := P.y
  let wpl := H.wpl
  let txs ← y.T_ "xs"
  need (txs.nl == y.xb.nl && y.xb.nl == y.h.xl && ledNS y.h.xl == 2 * y.xb.nl - 1)
  let tI ← v.tabAt "xbI@Z_V"
  let tA ← v.tabAt "af@Z_V"
  let e ← (hiTab wpl.r y.h.la (P.rd.lNI + y.lPd - y.ls)).toOption
  let blocks := y.h.d / y.S2
  let sum ← sumForms (y.NI * blocks * y.xb.nl) fun x =>
    let l := x % y.xb.nl
    let kh := x / y.xb.nl % blocks
    let i := x / y.xb.nl / blocks
    (if i == 0 then v.U3at tI (tenCell y.xb l 0 0 / y.S2 + kh)
     else v.U3at tA (tenCell txs.place l (i - 1) 0 / y.S2 + kh)).map fun a =>
      (a, negE (mulE (e.getD (i * y.Pd / y.S2 + kh) zeroE) (H.gp.getD l zeroE)))
  pure [wpl.row, Aff.slot wpl.sL - Aff.slot wpl.sR, Aff.slot wpl.sL + sum]

/-- Group 3, first claim: Cl8 = Σ_i Σ_r omV^(7 i + r) P(i, r): the token sumcheck of the row
products starts from their batch. -/
def rowBatchForm (y : Lay) (H : Heard) : Aff :=
  (List.range (ledNP y.h.xl * y.NI)).foldl
    (fun (a : Aff) i => a.addMul (Aff.slot (H.sPv + i)) (negE (H.omV.getD i zeroE)))
    (Aff.slot H.tV.sCl)

/-- The digits of norm i's row at the token point P, as forms: a cell holds its digit less 128. -/
def digitsAt (v : Env) (P : String) (i : Nat) : Option (Nat → Aff) :=
  (v.rowCells P i 99).map fun cells j => cells.getD j aff0 + Aff.ofConst (ofNat 128)

/-- The summand of the row products' token sumcheck on the end values as shown: sh holds a′, b′,
Rlo′, Rhi′ of norm 0, then of norm 1, and so on. -/
def rowsSummand (y : Lay) (H : Heard) (sh : Array E) : E :=
  (List.range y.NI).foldl
    (fun s i => addE s (P6.summand (fun r => H.omV.getD (7 * i + r) zeroE)
      fun k => sh.getD (4 * i + k) zeroE)) zeroE

/-- Groups 4 to 6: that the four shown values of each norm are the fields a, b, Rlo, Rhi of its row
at the sumcheck's end point; the nine carries of each norm; the eight lines of each norm's row. The
row's formulas: OnBytes/Desc/First/P6. -/
def rowsForms (v : Env) (H : Heard) : Option (List Aff) := do
  let y := v.y
  let ends ← (List.range y.NI).mapM fun i =>
    (digitsAt v "r_tV" i).map fun D =>
      let f := P6.Row.ofDigits D
      [f.a, f.b, f.Rlo, f.Rhi].zipIdx.map fun x => Aff.slot (H.tV.sEnd + 4 * i + x.2) - x.1
  let Ds ← (List.range y.NI).mapM fun i => digitsAt v "P_V" i
  let carries := Ds.zipIdx.map fun x =>
    P6.carries (P6.Row.ofDigits x.1) x.1 fun s => Aff.slot (H.sW + 9 * x.2 + s)
  let lines := Ds.zipIdx.map fun x =>
    P6.lines (P6.Row.ofDigits x.1) (fun j => Aff.slot (H.sPv + 7 * x.2 + j)) (epsOf y x.2)
      (twoM v x.2)
  pure (ends.flatten ++ carries.flatten ++ lines.flatten)

/-- Group 7: Rt(i) = R of row i @ rt, i < 2 Lam; sct(m) = sc(m) @ rt, m < LamM; selt(m, e) =
sel(m, e) @ rt, e < NE: the values which the second token sumcheck has shown equal their forms in
the reads at its end point. Its own claim is inside the start form of the batched sumcheck. -/
def termsForms (v : Env) (H : Heard) : Option (List Aff) := do
  let y := v.y
  let tT ← H.tT
  let n := y.NN * y.Lam
  let a ← (List.range n).mapM fun i => (v.rowR "rt" i).map fun x => Aff.slot (tT.sEnd + i) - x
  let b ← (List.range y.LamM).mapM fun lm =>
    (v.shA "sc" "rt" lm 0).map fun x => Aff.slot (tT.sEnd + n + lm) - x
  let c ← (List.range (y.LamM * y.h.NE)).mapM fun x =>
    (v.shA "sel" "rt" (x / y.h.NE) (x % y.h.NE)).map fun z =>
      Aff.slot (tT.sEnd + n + y.LamM + x) - z
  pure (a ++ b ++ c)

/-- The two claims on the end values of a product layer o of the gated products: the left one plus
the tensor s at the layer's point is 0, and so is the right one plus the tensor u. So each end value
is the negative of its tensor's value, and their product is the product of the two tensors' values.
e: the weights of the blocks at the layer's point; t: the first entry of the tables of af at that
point; rows: the layers; blocks: the blocks of features of a layer; stride: the distance of two
layers in e; lamOf and first give a row's layer and its first block. -/
def endsForms (v : Env) (o : Level) (e : Array E) (t rows blocks stride : Nat)
    (lamOf : Nat → Nat) (first : Nat) : Option (List Aff) := do
  let ts ← v.y.T_ "s"
  let tu ← v.y.T_ "u"
  let sumOf (X : Ten) : Option Aff :=
    sumForms (rows * blocks) fun x =>
      (v.longA t X (lamOf (x / blocks)) (first + x % blocks)).map fun a =>
        (a, e.getD (x / blocks * stride + x % blocks) zeroE)
  pure [Aff.slot o.sL + (← sumOf ts), Aff.slot o.sR + (← sumOf tu)]

/-- Groups 8 and 9, the gated products. For the dense layers:
  own(12; vL′ vR′), on the start form H1;
  vL + Σ_lam Σ_x eq(r12↑, lam Pf/S2 + x) s(lam, x) @ Z_a = 0;   the same for vR and u;
lam < Lam, x < f/S2. For the routed ones the same three, on the start form Σ_m eq(rhoM, m) H2(m),
with the weights eq(r14↑, m fe/S2 + x) on s and u of layer 2 m + 1, block fe/S2 + x, @ Z_b;
m < LamM, x < fe/S2. -/
def gatedForms (P : Pub) (v : Env) (hd : Level) (hd2 : Option Level) : Option (List Aff) := do
  let y := P.y
  let h := y.h
  let e ← (hiTab hd.r h.la (h.ll + y.lPf - y.ls)).toOption
  let a ← endsForms v hd e (← v.tabAt "af@Z_a") y.Lam (h.f / y.S2) (y.Pf / y.S2) id 0
  let o ← hd2
  let e2 ← (hiTab o.r h.la (h.ll - 1 + y.lfe - y.ls)).toOption
  let b ← endsForms v o e2 (← v.tabAt "af@Z_b") y.LamM (h.fe / y.S2) (h.fe / y.S2)
    (fun lm => 2 * lm + 1) (h.fe / y.S2)
  pure (hd.row :: a ++ o.row :: b)

/-- Group 10: Σ_e sel(m, e) @ zt = 1 for each m < LamM: at the token point zt the selector's entries
of each layer sum to 1. -/
def oneHotForms (v : Env) : Option (List Aff) :=
  (List.range v.y.LamM).mapM fun lm =>
    (sumForms v.y.h.NE fun e => (v.shA "sel" "zt" lm e).map fun a => (a, oneE)).map fun s =>
      Aff.ofConst (negE oneE) + s

/-- After Forest.planesAt (OnBytes/Model/Look.lean:474-483). -/
def planesAt (g : Forest.Heard) (lm e : Nat) (bit : Nat → Nat → Option Aff) : Option Aff :=
  let h := g.shape
  let w := h.kT + 5 - lm
  let ec := eqTab ((g.zb e).extract h.kT (h.kT + h.cK))
  let et := eqTab ((g.zb e).extract 0 w)
  (List.range (h.NC * 2 ^ w)).foldlM
    (fun (f : Aff) col => (bit e col).map fun x =>
      Aff.addMul f x (mulE (ec.getD (col / 2 ^ w) zeroE) (et.getD (col % 2 ^ w) zeroE)))
    (Aff.ofConst zeroE)

/-- Group 11, the lookup's three claims that read the planes, on the three tables of matrix b: what
is kept in the leaves' sumcheck's own claim; and the second and the third claim. After
Forest.planeClaims (OnBytes/Model/Look.lean:496-506). -/
def planesParts (v : Env) (fo : Forest.Heard) : Option (Aff × List Aff) := do
  let y := v.y
  let h := fo.shape
  let lm := y.h.lmb
  let tB0 ← v.tabAt "b-bits-0"
  let tB1 ← v.tabAt "b-bits-1"
  let tP ← v.tabAt "b-pin"
  let col (t x : Nat) : Option Aff := if x < y.kbm then v.U3at t x else none
  let bit (e x : Nat) : Option Aff := col (if e == 0 then tB0 else tB1) x
  need (Forest.planeCols h lm).toBool
  let at0 ← planesAt fo lm 0 bit
  let at1 ← planesAt fo lm 1 bit
  let count ← (List.range (h.NC * 2 ^ (h.kT + 5 - lm))).foldlM
    (fun (f : Aff) c => (col tP c).map fun x => f + x)
    (Aff.ofConst (negE (ofF (2 ^ h.v - h.padding).toUInt64)))
  pure (Aff.scale at0 fo.leavesA, [Aff.slot fo.sBit - at1, count])

/-- Group 12, in the first group: vE = Σ_k eq(tkh, k) xbI(k) @ Z_E, k < d/S2: the embedding's value
equals its form in the table at the point Z_E of the stream that comes in. -/
def embeddingForm (v : Env) (H : Heard) (sVE : Nat) : Option Aff := do
  let y := v.y
  let e := eqTab H.tkh
  let t ← v.tabAt "xbI@Z_E"
  let s ← sumForms (y.h.d / y.S2) fun kh => (v.xbA t kh).map fun a => (a, e.getD kh zeroE)
  pure ((Aff.slot sVE).scale (negE oneE) + s)

/-- The claims in front of the smallness test's, in the protocol's order. rowV: the own claim of the
row products' token sumcheck, own(8; ·). rowL: the own claim of the lookup's leaves' sumcheck.
rows: whether the lookup's own claims (group 1) are listed here. -/
def front (rows : Bool) (P : Pub) (g : Nat) (o : Own) (rowV rowL : Aff) : Option (List Aff) := do
  let g2 ← normsForms P o.v o.H
  let g46 ← rowsForms o.v o.H
  let g7 ← termsForms o.v o.H
  let g89 ← gatedForms P o.v o.hd o.hd2
  let g10 ← oneHotForms o.v
  let g11 ← planesParts o.v o.H.fo
  let g12 ← if g == 0 then (embeddingForm o.v o.H o.sVE).map ([·]) else some []
  pure ((if rows then o.H.fo.rows.toList else []) ++ g2 ++ [rowBatchForm P.y o.H, rowV] ++ g46 ++
    g7 ++ g89 ++ g10 ++ rowL :: g11.2 ++ g12)

/-- Groups 14 and 15: own(11; As Bs); A0 = Alin; B0 = Blin, with As, Bs, Alin, Blin the two sides of
the stacked panels at the end point rs (`stackEnd`); and rowM, the merge's own(16; fv′). -/
def back (o : Own) (rowM : Aff) : List Aff :=
  [o.K.rowS, Aff.slot o.K.sA0 - o.K.fin.Alin, Aff.slot o.K.sB0 - o.K.fin.Blin, rowM]

end OnBytes.Desc.First.K4
