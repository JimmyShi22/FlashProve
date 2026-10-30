-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/AttentionDivide.lean: the attention sub-proof's messages on the division, the value
product, the row maximum and the index.

The check of the attention sub-proof has seven parts (OnBytes/Model/Attention.lean). This file holds
the second half of part 2, the sub-proof's own messages. The first half is in
OnBytes/Model/AttentionScores.lean. The file follows the C++ function run of vf_attention_check.h
from the values of the division up to the last sumcheck before the tables. The values have that
function's names. The page on the sub-proof is docs/format/11-3-attention-segment.md (section 11.3
of the format). OnBytes/Model/AttentionHeard.lean explains the terms.

What is received, in this order. Each of these three sections begins with its own account.
 1. The division.
 2. The value product.
 3. The maximum and the index.

No equation on a value is tested here. The rows of the sumchecks and the slots are stored in the
records Divide and Attain, and part 6 makes the claims from these records
(OnBytes/Model/AttentionClaimsB.lean). The tests made here are on public numbers.

Main definitions: divide, attain. Their parts: coinsOm, scaled, weightedSum, unitOf, productIn,
overTileRows, valueBelowIn, valueOnIn, scoreAtIndexIn, keyTerm, keyAtIndexIn, bitsIn. The names of
its refusals: divideNames.

This file holds no theorem. It claims neither soundness nor hiding.
-/
import OnBytes.Model.AttentionHeard

namespace OnBytes.Attention

open OnBytes.Model

/-! ## Small helpers -/

/-- Draws one element that batches n rows. Returns its powers 0 to n - 1. The name is the C++
routine's. -/
def coinsOm (n : Nat) : SubM (Array E) := SubM.batch n

/-- Each entry of v times f. -/
def scaled (v : Array E) (f : E) : Array E := v.map fun x => mulE x f

/-- The form that is the sum over b < n of w[b] times form b. -/
def weightedSum (n : Nat) (w : Array E) (form : Nat → Aff) : Aff :=
  (List.range n).foldl (fun a b => Aff.addMul a (form b) (w.getD b zeroE)) (Aff.ofConst zeroE)

/-- For segment s: the number of the last call in list order that holds it, the segment's pieces in
that call, and the segment's inner point. zk holds each call's key point, in list order. Nothing if
no call holds the segment. -/
def unitOf (S : Shape) (zk : Array (Array E)) (s : Seg) : Option (Nat × Array PW × Array E) :=
  match lastHolding S s with
  | none => none
  | some q =>
    match S.calls[q]? with
    | none => none
    | some c =>
      let z := zk.getD q #[]
      some (q, pieces c z s, inner S z s)

/-! ## The division

The division. The prover sends 7 + lt hidden values at points that the lookup has drawn. Five
are taken at wl's inner point: the accumulator, the denominator times the output, the
denominator and the high parts of the two remainders. Then come the lt bits of the index at
ix's inner point, and the two high parts once more at wh's inner point. A sumcheck of products
follows for the denominator times the output.
-/

/-- The sumcheck for the denominator times the output. It starts from the hidden value in slot sZO.
Its variables are g (lgk) and the token (lt). The weight of pair b at the point of the challenges is
the weight of piece b of segment wl, times eq of that point with the coordinates zgW and ziW of wl's
inner point. -/
def productIn (S : Shape) (pwW : Array PW) (zgW ziW : Array E) (sZO : Nat) : SubM Sc3 := do
  let lgk := S.cf.lgk
  let o ← sc3In S.nvE S.NP (Aff.slot sZO)
  let f := mulE (eqPts zgW (o.r.extract 0 lgk)) (eqPts ziW (o.r.extract lgk (lgk + S.cf.lt)))
  sc3Row o (timesW pwW f)

/-! ## The value product

The value product. The verifier draws one element gam, which combines two claims in one sum:
accumulator + gam times denominator. The prover sends two sums, one for the tiles below the
diagonal and one for the tiles on it. Each sum has a sumcheck of products.
-/

/-- The sum over the tile rows I of wI[I] eI[I]. -/
def overTileRows (S : Shape) (wI eI : Array E) : E :=
  (List.range S.nT).foldl (fun s I => addE s (mulE (wI.getD I zeroE) (eI.getD I zeroE))) zeroE

/-- The value product's sumcheck below the diagonal. It starts from the hidden value in slot sCl.
Its variables are g (lgk), the slot row (lnT - 1), the tile slot (lnT) and the column within a tile
(lB). The shape has lnT ≥ 2. The point's second and third parts give each tile its weight
(tileSums). The weight of pair b at the point of the challenges is the weight of piece b of segment
wl, times eq of the point's first part with zgW, times the sum over the tile rows of the row's
weight times eq of zihi with the row's number. zihi is the tile row of wl's token. Returns the
sumcheck and the weights of the tile columns. -/
def valueBelowIn (S : Shape) (pwW : Array PW) (zgW zihi : Array E) (sCl : Nat) :
    SubM (Sc3 × Array E) := do
  let lgk := S.cf.lgk
  let atS := lgk + (S.lnT - 1)
  let o ← sc3In S.nvVM S.NP (Aff.slot sCl)
  let eP := Model.eqTab (o.r.extract lgk atS)
  let es := Model.eqTab (o.r.extract atS (atS + S.lnT))
  let w := tileSums S eP es
  let f := overTileRows S w.1 (Model.eqTab zihi)
  let o ← sc3Row o (timesW pwW (mulE f (eqPts zgW (o.r.extract 0 lgk))))
  pure (o, w.2)

/-- The value product's sumcheck on the diagonal. It starts from the hidden value in slot sCl1. Its
variables are g (lgk), the tile row (lnT) and the column within the tile (lB). The weight of pair b
at the point of the challenges is the weight of piece b of segment wl, times eq of the point's first
two parts with zgW and zihi. -/
def valueOnIn (S : Shape) (pwW : Array PW) (zgW zihi : Array E) (sCl1 : Nat) : SubM Sc3 := do
  let lgk := S.cf.lgk
  let o ← sc3In S.nvVD S.NP (Aff.slot sCl1)
  let f := mulE (eqPts zgW (o.r.extract 0 lgk)) (eqPts zihi (o.r.extract lgk (lgk + S.lnT)))
  sc3Row o (timesW pwW f)

/-- Receives the messages of the division and of the value product. zk holds each call's key point,
in list order. Three tests on public numbers come first. (1) Each of the segments wl, ix and wh is
held by a call. (2) Each has NP pieces, as many as there are pairs. (3) Each inner point has the
length that its cut needs; the C++ verifier does not make this test, and a failure is reported as
refused. Not tested: that there is one piece for each pair. That follows from placePieces in
OnBytes/Model/AttentionShape.lean. wl's inner point is one coordinate, g (lgk), the token (lt) and
the feature within a head (ldh); ix's is g and the token; wh's is as wl's without the first
coordinate. -/
def divide (S : Shape) (zk : Array (Array E)) : SubM Divide := do
  let lgk := S.cf.lgk
  let lt := S.cf.lt
  let ldh := S.cf.ldh
  let uW := unitOf S zk .wl
  let uX := unitOf S zk .ix
  let uH := unitOf S zk .wh
  mustAs "internal-af-calls" (uW.isSome && uX.isSome && uH.isSome)
  let (_, pwW, zW) ← SubM.get uW
  let (_, pwX, zX) ← SubM.get uX
  let (qWH, pwH, zH) ← SubM.get uH
  mustAs "internal-af-calls" (pwW.size == S.NP && pwX.size == S.NP && pwH.size == S.NP)
  SubM.must (zW.size == 1 + lgk + lt + ldh && zX.size == lgk + lt && zH.size == lgk + lt + ldh)
  let zgW := zW.extract 1 (1 + lgk)
  let ziW := zW.extract (1 + lgk) (1 + lgk + lt)
  let zihi := ziW.extract 0 S.lnT
  let s5 ← SubM.claimsIn 5
  let sIB ← SubM.claimsIn lt
  let s5h ← SubM.claimsIn 2
  let scE ← productIn S pwW zgW ziW (s5 + 1)
  let gamP ← SubM.batch 2
  let sCl ← SubM.claimsIn 2
  let (vpm, wJv) ← valueBelowIn S pwW zgW zihi sCl
  let vpd ← valueOnIn S pwW zgW zihi (sCl + 1)
  pure {
    pwW := pwW,
    pwX := pwX,
    pwH := pwH,
    qWH := qWH,
    zsl := zW.getD 0 zeroE,
    zgW := zgW,
    ziW := ziW,
    zcW := zW.extract (1 + lgk + lt) (1 + lgk + lt + ldh),
    zgX := zX.extract 0 lgk,
    ziX := zX.extract lgk (lgk + lt),
    zgH := zH.extract 0 lgk,
    ziH := zH.extract lgk (lgk + lt),
    zcH := zH.extract (lgk + lt) (lgk + lt + ldh),
    s5 := s5,
    sIB := sIB,
    s5h := s5h,
    scE := scE,
    gam := gamP.getD 1 zeroE,
    sCl := sCl,
    vpm := vpm,
    wJv := wJv,
    vpd := vpd }

/-! ## The maximum and the index

The maximum. The verifier draws two points in one message: (tg, ti) for the maxima and
(tk, tbg, tbi) for the bits. The prover sends each pair's row maximum at the first point. Three
sumchecks follow. A sumcheck of products is for the score at the index, which must equal the
maximum. A sumcheck by degrees is for the key at the index. A sumcheck of products is for the
cells of the index, which must be bits. None of this is tested here: part 6 adds the claims
(OnBytes/Model/AttentionClaimsB.lean).
-/

/-- The score at the index. Receives each pair's row maximum at the drawn point (tg, ti), as one
message. Draws the element whose powers om batch the pairs. Runs the sumcheck of products that
starts from the sum of om[b] times the maximum of pair b. Its variables are the token (lt), g (lgk)
and the feature within a head (ldh). The weight of pair b at the point of the challenges is om[b]
times eq of the point's first two parts with ti and tg. Returns the slot of the first maximum and
the sumcheck. -/
def scoreAtIndexIn (S : Shape) (tg ti : Array E) : SubM (Nat × Sc3) := do
  let lgk := S.cf.lgk
  let lt := S.cf.lt
  let sM6 ← SubM.claimsIn S.NP
  let om ← coinsOm S.NP
  let o ← sc3In S.nvF S.NP (weightedSum S.NP om fun b => Aff.slot (sM6 + b))
  let f := mulE (eqPts tg (o.r.extract lt (lt + lgk))) (eqPts ti (o.r.extract 0 lt))
  let o ← sc3Row o (scaled om f)
  pure (sM6, o)

/-- The term of pair b in the summand of the sumcheck for the key at the index, on the scalars that
were shown for the end values. sKC is the slot of the first end value. The end values are one key
value for each layer, then the lt bits of each pair's index. The term is w, times the key value of
the pair's layer, times the product over the bits k < lt of v (2 y - 1) + (1 - y), which equals
v y + (1 - v) (1 - y). Here v was shown for bit k, and y is coordinate lt - 1 - k of pj, the part of
the point of the challenges that stands for the key's token. -/
def keyTerm (S : Shape) (sKC : Nat) (pj : Array E) (w : E) (b : Nat) : SubM E := do
  let lt := S.cf.lt
  let kc ← SubM.shown (sKC + b / S.HA)
  (List.range lt).foldlM
    (fun t k => do
      let y := pj.getD (lt - 1 - k) zeroE
      let v ← SubM.shown (sKC + (S.Lam + b * lt + k))
      pure (mulE t (addE (mulE v (subE (addE y y) oneE)) (subE oneE y))))
    (mulE w kc)

/-- The key at the index. scF is the sumcheck for the score at the index. Draws the element whose
powers om4 batch the pairs. Runs the sumcheck by degrees that starts from the sum of om4[b] times
the second end value of pair b in scF. Its variables are the key's token (lt), g (lgk) and the
query's token (lt). It has Lam + NP lt end values. The summand at the point of the challenges is the
sum of the pairs' terms (keyTerm), times eq of the point's last two parts with g and the token in
scF's point. Returns the sumcheck with its row. -/
def keyAtIndexIn (S : Shape) (scF : Sc3) : SubM Scd := do
  let lgk := S.cf.lgk
  let lt := S.cf.lt
  let om4 ← coinsOm S.NP
  let o ← scdIn S.scdDegrees (lt + 1) (S.Lam + S.NP * lt) (weightedSum S.NP om4 (sc3B scF))
  let pj := o.r.extract 0 lt
  let pg := o.r.extract lt (lt + lgk)
  let pi := o.r.extract (lt + lgk) (2 * lt + lgk)
  let ri := scF.r.extract 0 lt
  let rg := scF.r.extract lt (lt + lgk)
  let s0 ← (List.range S.NP).foldlM
    (fun s b => do
      let t ← keyTerm S o.sEnd pj (om4.getD b zeroE) b
      pure (addE s t))
    zeroE
  scdRow o (mulE (mulE (eqPts ri pi) (eqPts rg pg)) s0)

/-- The sumcheck for the cells of the index, which must be bits. Draws the element whose powers om5
batch the pairs. Runs the sumcheck of products that starts from 0. Its variables are the token
(lt), g (lgk) and the number of the bit (4 coordinates: lt is at most 16). The weight of pair b at
the point of the challenges is om5[b] times eq of the point's three parts with the drawn tbi, tbg
and tk. -/
def bitsIn (S : Shape) (tk tbg tbi : Array E) : SubM Sc3 := do
  let lgk := S.cf.lgk
  let lt := S.cf.lt
  let om5 ← coinsOm S.NP
  let o ← sc3In S.nvH S.NP (Aff.ofConst zeroE)
  let f := mulE (mulE (eqPts tbi (o.r.extract 0 lt)) (eqPts tbg (o.r.extract lt (lt + lgk))))
    (eqPts tk (o.r.extract (lt + lgk) (lt + lgk + 4)))
  sc3Row o (scaled om5 f)

/-- Receives the messages on the row maximum and on the index. The verifier's first message holds
2 lgk + 2 lt + 4 elements: tg (lgk), ti (lt), tk (4), tbg (lgk) and tbi (lt), in this order. -/
def attain (S : Shape) : SubM Attain := do
  let lgk := S.cf.lgk
  let lt := S.cf.lt
  let points ← SubM.point .zero (2 * lgk + 2 * lt + 4)
  let tg := points.extract 0 lgk
  let ti := points.extract lgk (lgk + lt)
  let tk := points.extract (lgk + lt) (lgk + lt + 4)
  let tbg := points.extract (lgk + lt + 4) (2 * lgk + lt + 4)
  let tbi := points.extract (2 * lgk + lt + 4) (2 * lgk + 2 * lt + 4)
  let (sM6, scF) ← scoreAtIndexIn S tg ti
  let scd ← keyAtIndexIn S scF
  let scH ← bitsIn S tk tbg tbi
  pure {
    tg := tg,
    ti := ti,
    sM6 := sM6,
    scF := scF,
    scd := scd,
    scH := scH }

/-- The names under which this file's tests fail. A name must be listed here to be printed:
proofRefusalName in OnBytes/Model/VerifyStages.lean passes on listed names only. The test on the
lengths of the inner points in divide has no name of its own: a failure is reported as refused
(unnamed in OnBytes/Iop/Ground.lean). Some routines that the file calls refuse under names of other
lists (sumsNames, Rounds.names). -/
def divideNames : List String := ["internal-af-calls"]

end OnBytes.Attention
