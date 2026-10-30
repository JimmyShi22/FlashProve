-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Alone.lean: the honest prover's side of an attention segment's own rounds:
the hidden values that are sent by themselves and are read off the cells. Definitions with code; no
theorem.

Each of these values but ACC is a sum of cells under public weights: the weights of a lookup call's
pieces and tables of the equality polynomial at cuts of that call's key point. ACC is such a sum of
products of two values of cells. The points and the pieces' weights are what the verifier's own
function makes of the key points (`ptsOf`, Johnson/Desc/K5/Honest/Points.lean); no cut of a point is
typed here. What each value is stands in docs/format/11-3-attention-segment.md, "The scalars by
name", last column; the verifier's claim on each is in Johnson/Desc/First/Att/RunsP.lean.

  `pairNo`, `overPieces`   a piece's pair number; a sum over a unit's pieces under their weights
  `planeOf`                one of the five cells of a pair of positions, at a unit's inner point
  `maxAt`                  the row's maximum at a softmax-table unit's inner point
  `atRow`, `atChan`        a value of (pair, head, token), or with a channel too, at a point
  `idxM`, `idxD`           the index of a pair of positions in its region
  `tileSum`, `accAt`       the weighted sum of the values, tile by tile, at a point
  `aloneKR`                R_(u,0), R_(u,1), R_(u,2) for each remainder-table unit u, in order
  `aloneK`                 PV_(u,0) .. PV_(u,4), MV_u for softmax-table unit number i
  `accV`, `zcV`, `rhV`, `rhpV`, `ibV`, `rh2V`, `rhp2V`
                           ACC, ZC, RH, RHP, IB_0 .. IB_(lt - 1), RH2, RHP2
  `leadK`, `leadSE`        the scalars in front of a softmax-table unit's sumcheck and of the
                           division's, in the order sent, with the sumcheck's total handed in
  `aloneOk`                the points are there and every list has its length

Not here: SV_u, ZO, CL0 and CL1, which are their sumchecks' totals, and M6.

A plane's value runs over all indices of the region, those of the empty address and those above the
diagonal too. MV_u leaves the empty address out, through the verifier's tile weights.

RH, RHP, RH2 and RHP2 are values of the cells, and such a cell holds the high part of a remainder
less 128. The verifier adds the 128 in its key forms.

ACC. The verifier has no claim that ties ACC to cells by itself. It is typed as the sum, over the
pieces, heads, tiles with an address and tiles on the diagonal, of
  eq(zgW, head) eq(ziW, query's token) weight(pair of positions) value(key's token, at zcW):
all cells of the query's row in both regions, the empty address left out, the places above the
diagonal in. That is the sum of the two value products' totals without the batching element.

Where these are the values that the verifier's claims read. The verifier reads two families through
tables whose weights come from another point than the one that is used here.
  * The planes (R, PV): its table's weights are eq at the last lmS coordinates of the lookup's
    point; here the unit's own inner point is used whole.
  * RH2, RHP2: its table's weights are made of (ziW, zcW); here (ziH, zcH) is used, as the format
    says.
The two readings are one where every unit's inner point ends in the lookup's point's last lmS
coordinates and (ziW, zcW) = (ziH, zcH) = its last lt + ldh coordinates. The verifier's function for
the tables tests both (`mergedPlanes`, `mergedTokens`, Johnson/Desc/First/Att/TablesP.lean) and
refuses otherwise; by the format the lookup makes its calls' key points so. Nothing here tests it.

Limits. Where the verifier's function for the points refuses (its tests are on lengths alone) or a
unit's number is too large, a list is empty and a single value is 0: `aloneOk` tells. No value
depends on the challenges of the place's own rounds. Nothing here holds these values against the
verifier's claims. Tests: Johnson/Desc/K5/Honest/AloneToy.lean; against the claims:
Johnson/Desc/K5/Honest/U3Toy.lean.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Faces
import Johnson.Desc.K5.Honest.Points

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open VerifiableInference.Desc.First.Att.P (Geo W1 RemP ScoreP DivP Pts eqTab cover tok)

/-! ## Sums over pieces and points -/

/-- A piece's pair number: layer times the query heads that share a head of keys and values, plus
the query head's number among these. -/
def pairNo (g : Geo) (p : W1) : Nat := p.lam * g.HA + p.a

/-- The sum over a unit's pieces of the piece's weight times f. -/
def overPieces (pw : Array W1) (f : W1 → E) : E :=
  pw.foldl (fun s p => addE s (mulE p.wp (f p))) zeroE

/-- **Cell x of a pair of positions at a unit's inner point**: the sum over the pieces of the weight
times the sum over all indices n of the region of eq(point, n) times the cell. -/
def planeOf (g : Geo) (w : K5In) (u : RemP) (x : Nat) : E :=
  let e := eqTab u.z
  overPieces u.pw fun p => under e fun n => w.c u.isD x (pairNo g p) n

/-- **The row's maximum at a softmax-table unit's inner point.** The tokens' weights are the
verifier's: the tile rows' weights, in which the empty address has no share, times eq at the place
in the tile. -/
def maxAt (g : Geo) (w : K5In) (k : ScoreP) : E :=
  let eg := eqTab k.zg
  let ti := tok g k.wI k.zi
  overPieces k.pw fun p => under eg fun hk => under ti fun i => w.mx (pairNo g p) hk i

/-- A value f of (pair, head, token) at the point (zg, zi), summed over the pieces. -/
def atRow (g : Geo) (pw : Array W1) (zg zi : Array E) (f : Nat → Nat → Nat → E) : E :=
  let eg := eqTab zg
  let ei := eqTab zi
  overPieces pw fun p => under eg fun hk => under ei fun i => f (pairNo g p) hk i

/-- A value f of (pair, head, token, channel) at the point (zg, zi, zc), summed over the pieces. -/
def atChan (g : Geo) (pw : Array W1) (zg zi zc : Array E) (f : Nat → Nat → Nat → Nat → E) : E :=
  let ec := eqTab zc
  atRow g pw zg zi fun b hk i => under ec fun ch => f b hk i ch

/-! ## The weighted sum of the values -/

/-- The index, in the region below the diagonal, of the pair at head hk, address (P, sg), place il
of the query and jl of the key in the tile. -/
def idxM (g : Geo) (hk P sg il jl : Nat) : Nat :=
  (((hk * g.hP + P) * g.nT + sg) * g.B + il) * g.B + jl

/-- The index, in the region on the diagonal, of the pair at head hk, tile I, places il and jl. -/
def idxD (g : Geo) (hk I il jl : Nat) : Nat := ((hk * g.nT + I) * g.B + il) * g.B + jl

/-- One tile's share for one piece and head: the sum over the key's place jl of the value at the
channels' weights ec, times the sum over the query's place il of the token's weight and the pair's
softmax weight. (I, J): the tile's row and column. idx il jl: the pair's index. -/
def tileSum (g : Geo) (w : K5In) (ei ec : Array E) (onDiag : Bool) (p : W1) (hk I J : Nat)
    (idx : Nat → Nat → Nat) : E :=
  sumTo g.B fun jl =>
    mulE (under ec fun ch => w.v p.lam hk (J * g.B + jl) ch)
      (sumTo g.B fun il =>
        mulE (ei.getD (I * g.B + il) zeroE) (w.ew onDiag (pairNo g p) (idx il jl)))

/-- **The weighted sum of the values** at (zgW, ziW, zcW), summed over the pieces. -/
def accAt (g : Geo) (w : K5In) (d : DivP) : E :=
  let eg := eqTab d.zgW
  let ei := eqTab d.ziW
  let ec := eqTab d.zcW
  overPieces d.pwW fun p => under eg fun hk =>
    addE
      (sumTo g.hP fun P => sumTo (g.nT - 1) fun sg =>
        let t := cover g.nT P sg
        tileSum g w ei ec false p hk t.1 t.2 (idxM g hk P sg))
      (sumTo g.nT fun I => tileSum g w ei ec true p hk I I (idxD g hk I))

/-! ## The values at the verifier's points -/

/-- The remainder-table units' values. n: how many such units there are; they stand first. -/
def krAt (g : Geo) (w : K5In) (p : Pts) (n : Nat) : List E :=
  (p.planes.toList.take n).flatMap fun u => (List.range 3).map (planeOf g w u)

/-- The five planes' values and the maximum's of softmax-table unit number i. -/
def kAt (g : Geo) (w : K5In) (p : Pts) (i : Nat) : Option (List E) := do
  let k ← p.scores[i]?
  let u ← p.planes[k.claim]?
  pure ((List.range 5).map (planeOf g w u) ++ [maxAt g w k])

/-- The denominator at (zgW, ziW). -/
def zcAt (g : Geo) (w : K5In) (d : DivP) : E := atRow g d.pwW d.zgW d.ziW w.zd
/-- The cells of the two remainders' high parts at (zgW, ziW, zcW). -/
def rhAt (g : Geo) (w : K5In) (d : DivP) : E := atChan g d.pwW d.zgW d.ziW d.zcW w.rh
def rhpAt (g : Geo) (w : K5In) (d : DivP) : E := atChan g d.pwW d.zgW d.ziW d.zcW w.rhp
/-- The index's bits at (zgX, ziX), the lowest first. -/
def ibAt (g : Geo) (w : K5In) (d : DivP) : List E :=
  (List.range g.lt).map fun k => atRow g d.pwX d.zgX d.ziX (w.ibit k)
/-- The same cells as `rhAt` and `rhpAt` read, at (zgH, ziH, zcH). -/
def rh2At (g : Geo) (w : K5In) (d : DivP) : E := atChan g d.pwH d.zgH d.ziH d.zcH w.rh
def rhp2At (g : Geo) (w : K5In) (d : DivP) : E := atChan g d.pwH d.zgH d.ziH d.zcH w.rhp

/-! ## The values, of the place's numbers, the cells and the challenges -/

/-- **R_(u,0), R_(u,1), R_(u,2)** for each remainder-table unit u, in the order of hearing. -/
def aloneKR (P : Pub5) (w : K5In) (c : Chal) : List E :=
  ((ptsOf P c).map fun p => krAt P.g w p P.x.planeMessages).getD []

/-- **PV_(u,0) .. PV_(u,4), MV_u** for the softmax-table unit number i. -/
def aloneK (P : Pub5) (w : K5In) (c : Chal) (i : Nat) : List E :=
  ((ptsOf P c).bind fun p => kAt P.g w p i).getD []

/-- A value at the division's points; 0 where there are none. -/
def ofDiv (P : Pub5) (c : Chal) (f : DivP → E) : E := ((ptsOf P c).map fun p => f p.d).getD zeroE

/-- **ACC.** -/
def accV (P : Pub5) (w : K5In) (c : Chal) : E := ofDiv P c (accAt P.g w)
/-- **ZC.** -/
def zcV (P : Pub5) (w : K5In) (c : Chal) : E := ofDiv P c (zcAt P.g w)
/-- **RH**, **RHP**: of the cells, which hold the high parts less 128. -/
def rhV (P : Pub5) (w : K5In) (c : Chal) : E := ofDiv P c (rhAt P.g w)
def rhpV (P : Pub5) (w : K5In) (c : Chal) : E := ofDiv P c (rhpAt P.g w)
/-- **IB_0 .. IB_(lt - 1).** -/
def ibV (P : Pub5) (w : K5In) (c : Chal) : List E :=
  ((ptsOf P c).map fun p => ibAt P.g w p.d).getD []
/-- **RH2**, **RHP2**: of the same cells. -/
def rh2V (P : Pub5) (w : K5In) (c : Chal) : E := ofDiv P c (rh2At P.g w)
def rhp2V (P : Pub5) (w : K5In) (c : Chal) : E := ofDiv P c (rhp2At P.g w)

/-! ## In the order sent -/

/-- **The seven scalars in front of the sumcheck of softmax-table unit number i**: PV_(u,0) ..
PV_(u,4), MV_u, SV_u. sv: the sumcheck's total. In front of the first unit's seven stand the values
of `aloneKR`. -/
def leadK (P : Pub5) (w : K5In) (c : Chal) (i : Nat) (sv : E) : List E := aloneK P w c i ++ [sv]

/-- **The scalars in front of the division's sumcheck**: ACC, ZO, ZC, RH, RHP, IB_0 .. IB_(lt - 1),
RH2, RHP2. zo: the sumcheck's total. The points are made once. -/
def leadSE (P : Pub5) (w : K5In) (c : Chal) (zo : E) : List E :=
  ((ptsOf P c).map fun p =>
    let (g, d) := (P.g, p.d)
    [accAt g w d, zo, zcAt g w d, rhAt g w d, rhpAt g w d] ++ ibAt g w d ++
      [rh2At g w d, rhp2At g w d]).getD []

/-- **The points are there and every list has its length**: 3 for each remainder-table unit, 6 for
each softmax-table unit, lt bits. Of the public numbers and the challenges alone. -/
def aloneOk (P : Pub5) (c : Chal) : Bool :=
  match ptsOf P c with
  | none => false
  | some p => decide (P.x.planeMessages ≤ p.planes.size) && p.scores.size == P.x.score.length &&
      p.scores.all fun k => decide (k.claim < p.planes.size)

end H2K5.Honest
