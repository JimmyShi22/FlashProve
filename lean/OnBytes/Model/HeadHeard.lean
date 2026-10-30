-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/HeadHeard.lean: the messages of the sub-proof of the output head, up to its reads.

The sub-proof runs as the last link of a request's first chain. This file holds the first part of
its check: what the verifier receives and draws between the commitment to the sub-proof's cells and
the commitment to its vector of reads. No equation of the protocol is tested here. Every sumcheck
leaves one linear claim, which is kept and added later (OnBytes/Model/Head.lean). Two tests in this
file are on values: the form of the reply's token, and the key points that the lookup returns. The
others are on public numbers. The C++ counterpart is the first part of runForkHidH2 in
verifier/src/vf_output_head_check.inc. The names of matrices, tensors and segments (hf, hd, hr, bH;
aw, ra, d1, d2, ex; NF, NFH, HD0 and so on) are explained in OnBytes/Model/HeadLayout.lean. A
refusal has the name under which cp_verify refuses at that place, without the prefix "H:" that
cp_verify puts before some names that mark a fault of the program.

The messages, in their order:
 - the lookup of all calls of the head, which gives each call its key point;
 - the norm's point P_V over the positions;
 - the sums of limb products, one element that batches them, and the product layer of the squares;
 - the row products, one element that batches them, and the token sumcheck at P_V;
 - the token sumcheck of the stream times the reciprocal;
 - the token sumcheck of the activations times the head's weights, which goes on over the channels
   (the d features of an activation, padded to 2^lPd).

Main definitions: `replyToken`, `winOf`, `Heard`, `callNo`, `zjOf`, `ztOf`, `hearSquares`,
`hearProducts`, `hearStream`, `hearLogits`, `hear`.
What is not claimed: no theorem is stated here.
-/
import OnBytes.Model.HeadPlan
import OnBytes.Model.Look
import OnBytes.Model.Tensors

namespace OnBytes.Model.Head

/-- The names of this file's refusals, without the prefix "H:" that cp_verify puts before the second
of them. Where cp_verify appends the name of a segment to a name, the name here ends before it.
`held` passes on the last of them from `lastOf` (OnBytes/Model/Tensors.lean). -/
def Heard.names : List String :=
  ["header-y", "internal-h-merged-point", "internal-segment", "plan-tensor-layout"]

/-- The value of x, or a refusal with the name that x carries. It is meant for results that depend
on public numbers alone. -/
def held {α : Type} (x : Except String α) : Blk α :=
  match x with
  | .ok a => pure a
  | .error name => refuse name

/-- The value of x, or a refusal with the given name. It is meant for a value whose presence depends
on public numbers alone. -/
def getAs {α : Type} (name : String) (x : Option α) : Blk α :=
  match x with
  | some a => pure a
  | none => refuse name

/-- In a run that keeps intermediate values, records one under a name that begins with "head: ". No
test reads it. Such values let this check be compared step by step with another verifier's. -/
def noteH (what : String) (value : E) : SubM Unit := StateT.lift (Blk.note ("head: " ++ what) value)

/-- The reply's token. The prover names it as one plain scalar in the message that holds the
head's cells, and the chain has received it. Here only its form is tested: it is an entry of the
vocabulary. This function does not compare it with the reply that the caller was given. -/
def replyToken (plain : Array E) (V : Nat) : SubM Nat := do
  mustAs "header-y" (plain.size == 1)
  let y := plain.getD 0 zeroE
  testAs "header-y" (y.c1 == 0 && y.c2 == 0 && decide (y.c0.toNat < V))
  pure y.c0.toNat

/-- The token that is checked at each covered position. At the last position, if that is covered, it
is the token that the prover has named. -/
def winOf (cov : Covered) (T yTok : Nat) : Array Nat :=
  if cov.hOn.getD (T - 1) false then cov.hWin.setIfInBounds (T - 1) yTok else cov.hWin

/-- What the verifier holds after the messages of this file. -/
structure Heard where
  /-- the token that is checked at each covered position -/
  win : Array Nat
  /-- the lookup of the head's calls -/
  g1 : Forest.Heard
  /-- the last la coordinates of every call's key point -/
  Zl : Array E
  /-- the norm's point over the positions -/
  PV : Array E
  /-- the first slot of the sums of limb products -/
  sW : Nat
  /-- the powers of the element that batches these sums -/
  gp : Array E
  /-- the product layer of the squares -/
  wpl : Level
  /-- the first slot of the row products -/
  sPv : Nat
  /-- the powers of the element that batches the row products -/
  omV : Array E
  /-- the token sumcheck of the row products, at P_V -/
  tV : Tsc
  /-- the token sumcheck of the stream times the reciprocal -/
  tN : Tsc
  /-- the token sumcheck of the activations times the head's weights -/
  tH : Tsc
  /-- the challenges of that sumcheck's rounds over the channels; rs[v] belongs to bit v -/
  rs : Array E
  /-- the number of the call with the segment NF -/
  qN : Nat
  /-- the number of the call with the segment HD0 -/
  qH : Nat

/-- The slot of the value that the merge takes: the head's weights at the last sumcheck's
point. -/
def Heard.sV (x : Heard) : Nat := x.tH.sEnd + 1

/-- The number of the first call that has a segment with this name. C++: callOf. -/
def callNo (L : HL) (seg : String) : Option Nat := L.calls.findIdx? fun c => (c.seg? seg).isSome

/-- The coordinates of a call's key point that belong to its columns. -/
def zjOf (L : HL) (g1 : Forest.Heard) (q : Nat) : Array E :=
  (g1.zk.getD q #[]).extract 0 (L.calls.getD q default).lJ

/-- The coordinates of a call's key point that belong to the positions. -/
def ztOf (h : Shape) (L : HL) (g1 : Forest.Heard) (q : Nat) : Array E :=
  let lJ := (L.calls.getD q default).lJ
  (g1.zk.getD q #[]).extract lJ (lJ + h.lt)

/-- The inverse of 2. A plain sum over an index of n bits is run under equality weights at this
coordinate: each value of the index then has the weight 2^-n. -/
def half : E := invE (ofNat 2)

/-- The last la coordinates of the lookup's point. Tests that every call's key point ends in them,
as it must: all trees share that part of the point (dT is at least la, by `layout`). The one long
table of hf that serves all calls relies on this. -/
def mergedPoint (h : Shape) (g1 : Forest.Heard) : SubM (Array E) := do
  let Zl ← held (lastOf g1.zx h.la)
  testAs "internal-h-merged-point" (g1.zk.all fun zk => zk.extract (zk.size - h.la) zk.size == Zl)
  pure Zl

/-- The sums of limb products, the element that batches them, and the product layer. The layer sums
the squares over the positions, at P_V, and over the features, without weights. It starts from
2^-lPd times the batched sums. Returns the first slot, the powers and the layer. -/
def hearSquares (h : Shape) (PV : Array E) : SubM (Nat × Array E × Level) := do
  let n := ledNS h.XL
  let sW ← SubM.claimsIn n
  let gp ← SubM.batch n
  let plainPd := powE half h.lPd
  let C := (List.range n).foldl
    (fun C s => Aff.addMul C (Aff.slot (sW + s)) (mulE (gp.getD s zeroE) plainPd)) {}
  let mu := h.lPd + h.lt
  let wpl ← levelIn mu (Array.replicate h.lPd half ++ PV) C (orderDefault mu)
  pure (sW, gp, wpl)

/-- The batched products on the scalars shown in the end values' slots of the sumcheck at P_V
(shown: OnBytes/Model/Hide.lean). The slots are those of a, b, Rlo, Rhi with five limbs, else of
sigma, Rlo, Rhi. -/
def productsShown (XL : Nat) (omV sh : Array E) : E :=
  let s := fun j => sh.getD j zeroE
  let w := fun j => omV.getD j zeroE
  if XL == 5 then ledProducts5 omV 0 (s 0) (s 1) (s 2) (s 3)
  else addE (addE (mulE (mulE (w 0) (s 0)) (s 0)) (mulE (mulE (w 1) (s 1)) (s 0)))
    (mulE (mulE (w 2) (s 2)) (s 0))

/-- The values shown in the n slots that begin at `first`. -/
def shownRun (first n : Nat) : SubM (Array E) :=
  (List.range n).foldlM (fun a j => do pure (a.push (← SubM.shown (first + j)))) #[]

/-- The row products, the element that batches them, and the token sumcheck at P_V. Returns the
first slot, the powers and the sumcheck with its claim. -/
def hearProducts (h : Shape) (PV : Array E) : SubM (Nat × Array E × Tsc) := do
  let sPv ← SubM.claimsIn (ledNP h.XL)
  let omV ← SubM.batch (ledNP h.XL)
  let tV ← tscIn PV h.lt (ledNO h.XL) 2
  let sh ← shownRun tV.sEnd (ledNO h.XL)
  let (row, p) ← pscRow tV.p (productsShown h.XL omV sh)
  pure (sPv, omV, { tV with p := p, rowU := row })

/-- The token sumcheck at the position coordinates zt of the call with the segment NF. Shown at
its end: the reciprocal R, and the weighted stream. -/
def hearStream (h : Shape) (zt : Array E) : SubM Tsc := do
  let tN ← tscIn zt h.lt 2 2
  let (row, p) ← pscRow tN.p (mulE (← SubM.shown tN.sEnd) (← SubM.shown (tN.sEnd + 1)))
  pure { tN with p := p, rowU := row }

/-- The rounds over the channels, from the top bit down. Returns the challenges in the order of the
rounds. -/
def channelRounds : Nat → Array E → Psc → SubM (Array E × Psc)
  | 0, r, p => pure (r, p)
  | n + 1, r, p => do
    let (x, p) ← roundIn .eq2 p half
    channelRounds n (r.push x) p

/-- The token sumcheck at the position coordinates zt of the call with the segment HD0. The column
of the head's weights that a position reads depends on the position, so the sum does not split into
a factor on positions and one on channels. The sumcheck therefore goes on over the channels, which
are summed without weights: lam rounds at the coordinate 1/2. Its first slot holds 2^-lam times the
sum. Shown at its end: the activations and the weights at the point of all challenges. Returns the
sumcheck with its claim, and the channels' challenges, that of bit v at place v. -/
def hearLogits (h : Shape) (lam : Nat) (zt : Array E) : SubM (Tsc × Array E) := do
  let tH ← tscRounds zt h.lt
  let (r, p) ← channelRounds lam #[] tH.p
  let (sEnd, p) ← pscEnds p 2 2
  let (row, p) ← pscRow p (mulE (← SubM.shown sEnd) (← SubM.shown (sEnd + 1)))
  pure ({ tH with sEnd := sEnd, p := p, rowU := row }, r.reverse)

/-- All messages of the sub-proof up to the commitment to its reads. plain: the plain scalars of
the link's first message. -/
def hear (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered) (plain : Array E) : SubM Heard := do
  let yTok ← replyToken plain h.V
  SubM.slots hp.ns
  let g1 ← Forest.pad L.cl L.fs.pub h.LIDB
  let Zl ← mergedPoint h g1
  let PV ← SubM.point .zero h.lt
  let (sW, gp, wpl) ← hearSquares h PV
  let (sPv, omV, tV) ← hearProducts h PV
  let qN ← getAs "internal-segment" (callNo L "NF")
  let qH ← getAs "internal-segment" (callNo L "HD0")
  let tN ← hearStream h (ztOf h L g1 qN)
  let (tH, rs) ← hearLogits h hp.lamS (ztOf h L g1 qH)
  noteH "look-up, alpha" g1.alpha
  noteH "look-up, theta" g1.theta
  noteH "Z[0]" (Zl.getD 0 zeroE)
  noteH "P_V[0]" (PV.getD 0 zeroE)
  noteH "limbs, batching element" (gp.getD 1 zeroE)
  noteH "sum of squares, tau" wpl.tau
  noteH "sum of squares, r[0]" (wpl.r.getD 0 zeroE)
  noteH "row products, batching element" (omV.getD 1 zeroE)
  noteH "row products, r[0]" (tV.r.getD 0 zeroE)
  noteH "stream times reciprocal, r[0]" (tN.r.getD 0 zeroE)
  noteH "activations times head, r[0]" (tH.r.getD 0 zeroE)
  noteH "activations times head, rs[0]" (rs.getD 0 zeroE)
  pure { win := winOf cov h.T yTok, g1 := g1, Zl := Zl, PV := PV, sW := sW, gp := gp, wpl := wpl,
         sPv := sPv, omV := omV, tV := tV, tN := tN, tH := tH, rs := rs, qN := qN, qH := qH }

end OnBytes.Model.Head
