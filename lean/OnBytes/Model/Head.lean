-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Head.lean: the check of the sub-proof of the output head.

The last link of a request's first chain is about the end of the model: the final norm, the product
with the head's weights, and the acceptance policy on the logits of the covered positions. This
file puts the check together. Its parts are in the files HeadLayout, HeadPlan, HeadHeard,
HeadTables and HeadForms beside it. The C++ counterpart is runForkHidH2 in
verifier/src/vf_output_head_check.inc.

The steps of the check.
 1. The messages up to the reads (`hear`).
 2. The chain receives the commitment to the reads. The tables of reads are fixed (`tablesOf`).
 3. The messages of the smallness test, and the merge of the one claim on the committed weights.
 4. One element is drawn. Its powers are the weights of the claims.
 5. The claims are added, in a fixed order. A claim says that a form is 0. No claim is tested
    here: their weighted sum is one equation.
 6. The equation goes to the chain, which tests it at its end, and the link is closed.

What the claims say, group by group: see `claimSquares`, `claimLedger`, `claimStream`, `claimJoin`,
`claimPolicy`, `claimPlanes`, `claimLogits`. The names of matrices, tensors and segments are
explained in OnBytes/Model/HeadLayout.lean.

Words. Slot, hidden value, shown, form, claim: OnBytes/Model/Hide.lean. Link, chain:
OnBytes/Model/Trees.lean. Lookup, call: OnBytes/Model/Look.lean. A call's key point is the point at
which its key vector is read (`Forest.Heard.zk`, in the same file). The reads:
OnBytes/Model/HeadTables.lean. The merge: OnBytes/Model/Merge.lean. The smallness test (tl, the
tail): OnBytes/Model/Tail.lean.

Main definitions: `weightsClaim`, the claims named above, `walk`, `selfTests`, `runForkHidH2`.
What is not claimed: no theorem is stated here. This file does not compare the reply's token with
the one that the caller was given. That is done where the whole proof file is checked. Hidden is the
name of a value's part in the protocol (OnBytes/Model/Hide.lean). Nothing here says that a value
stays hidden.
-/
import OnBytes.Model.HeadForms

namespace OnBytes.Model.Head

/-- The names of this file's refusals, without the prefix "H:" that cp_verify puts before
some of them. cp_verify has no name like the last one, internal-h-covered. -/
def Check.names : List String :=
  ["internal-claim-unit", "header-y", "internal-claim-factors", "plan-tensor-layout",
   "internal-h-table-index", "internal-h-free-slot", "internal-h-claim-count",
   "internal-h-rows-booked", "internal-h-calls-booked", "internal-f-fun-moved", "plan-link",
   "internal-h-owner-TX", "internal-h-tree-list", "internal-f-fun-closed", "internal-claim-count",
   "internal-slot-count", "internal-f-draws", "internal-h-covered"]

/-- All names of the refusals that the files of the head's sub-proof raise themselves. -/
def names : List String :=
  Layout.names ++ Plan.names ++ Heard.names ++ Tables.names ++ Forms.names ++ Check.names

/-- The one claim on the committed weights, on the head's unit, which is the last unit of the layout
and has two index groups. On the vocabulary's index ("x") the factor is AV[v] = wx psi[v] - sR
ew[v]. r_H holds the challenges of the last token sumcheck's rounds over the positions. psi[v] is
the sum of eq(r_H, t) over the covered positions t whose checked token is v, and sR is that sum over
all covered positions. ew[v] is the weight of entry v of the segment HD0, and wx is the sum of ew
over the vocabulary. On the channels' index ("kk") the factor is the equality polynomial at the
challenges of the rounds over the channels. -/
def weightsClaim (R : Run) (wsLay : WsLay) : SubM WsClaim := do
  let ew0 ← ewOf R "HD0"
  let wx0 := wxOf R ew0
  let ui := wsLay.U.size - 1
  mustAs "internal-claim-unit" ((wsLay.U.back?.map (·.X)) == some 13)
  let eH := eqTab R.x.tH.r
  let sR := onSum R R.x.tH.r
  let mut f : List WsFac := []
  for G in (wsLay.U.getD ui default).g do
    if G.name == "x" then
      let mut AV := (Array.range R.h.V).map fun v => subE zeroE (mulE sR (ew0.getD v zeroE))
      for t in [0:R.h.T] do
        if R.cov.hOn.getD t false then
          let v := R.x.win.getD t 0
          testAs "header-y" (v < R.h.V)
          AV := AV.modify v fun a => addE a (mulE wx0 (eH.getD t zeroE))
      f := f ++ [{ AV := AV }]
    else if G.name == "kk" then
      let pt := (Array.range G.z).map fun i => R.x.rs.getD (G.z - 1 - i) zeroE
      let e := eqLow R.x.rs G.z R.hp.lamS
      f := f ++ [{ pt := pt, HV := e.extract 0 G.o }]
    else refuse "internal-claim-factors"
  pure { ui := ui, f := f }

/-- The final norm, the sum of squares. The claim that the product layer's sumcheck leaves. Its two
end values are equal: both are the stream's value. That value is read in the stream's table at the
layer's point, limb by limb under the powers of the batching element. -/
def claimSquares (R : Run) : SubM Unit := do
  let x := R.x
  layerObject x.wpl
  SubM.lin (S_ x.wpl.sL - S_ x.wpl.sR)
  mustAs "plan-tensor-layout" (R.b.nl == R.h.XL)
  -- The point has lPd + lt coordinates and la = ls + lt. hiTab refuses a point of fewer than la
  -- coordinates, so if it succeeds then ls ≤ lPd, and lPd - ls is the true difference.
  let e ← held (hiTab x.wpl.r R.h.la (R.h.lPd - R.h.ls))
  let t ← tabAt R "xbL@Z_V"
  let mut b := S_ x.wpl.sL
  for kh in [0:R.h.d / R.h.S2] do
    for l in [0:R.b.nl] do
      b := Aff.addMul b (← U3at R t (R.b.cell l 0 / R.h.S2 + kh))
        (subE zeroE (mulE (e.getD kh zeroE) (x.gp.getD l zeroE)))
  SubM.lin b

/-- The lines of the norm's ledger with five limbs: what the sumcheck's four end values are, the
nine lines of the carries, and the eight lines on root and reciprocal. -/
def claimLedger5 (R : Run) : SubM Unit := do
  let x := R.x
  let r ← row5At R "r_tV"
  SubM.lin (S_ x.tV.sEnd - r.a)
  SubM.lin (S_ (x.tV.sEnd + 1) - r.b)
  SubM.lin (S_ (x.tV.sEnd + 2) - r.Rlo)
  SubM.lin (S_ (x.tV.sEnd + 3) - r.Rhi)
  let q ← row5At R "P_V"
  for s in [0:9] do
    SubM.lin (ledCarry5 q s (S_ (x.sW + s)))
  let Pr := (Array.range 7).map fun j => S_ (x.sPv + j)
  for o in ledLines5 q Pr (ofNat R.h.epsF) (Aff.ofConst (ofNat (2 ^ (R.h.MF + 1)))) do
    SubM.lin o

/-- The lines of the norm's ledger with four limbs: what the sumcheck's three end values are, the
seven lines of the carries, and the five lines on root and reciprocal. -/
def claimLedger4 (R : Run) : SubM Unit := do
  let x := R.x
  let r ← rowAt R "r_tV"
  SubM.lin (S_ x.tV.sEnd - r.sig)
  SubM.lin (S_ (x.tV.sEnd + 1) - r.Rlo)
  SubM.lin (S_ (x.tV.sEnd + 2) - r.Rhi)
  let q ← rowAt R "P_V"
  for s in [0:7] do
    SubM.lin (S_ (x.sW + s) + q.c.getD s {} - q.Dg.getD s {} -
      Aff.scale (q.c.getD (s + 1) {}) (ofNat 256))
  SubM.lin (q.V + Aff.ofConst (ofNat R.h.epsF) - S_ x.sPv - q.l1)
  SubM.lin (q.l1 + q.h1 - Aff.scale q.sig (ofNat 2))
  SubM.lin (S_ (x.sPv + 2) - q.p1)
  SubM.lin (Aff.ofConst (ofNat (2 ^ (R.h.MF + 1))) + q.sig - q.s0 -
    Aff.scale (S_ (x.sPv + 1)) (ofNat 2) - Aff.scale q.p1 (ofNat (2 ^ 25)) -
    Aff.scale q.rr (ofNat 2))
  SubM.lin (q.rr + q.rq - q.sig + Aff.ofConst oneE)

/-- The final norm, the row ledger. The first slot of the sumcheck at P_V is the batched sum of
the row products. Then the claim that this sumcheck leaves, and the ledger's lines. -/
def claimLedger (R : Run) : SubM Unit := do
  let x := R.x
  let a := (List.range (ledNP R.h.XL)).foldl
    (fun a i => Aff.addMul a (S_ (x.sPv + i)) (subE zeroE (x.omV.getD i zeroE))) (S_ x.tV.sCl)
  SubM.lin a
  SubM.lin x.tV.rowU
  if R.h.XL == 5 then claimLedger5 R else claimLedger4 R

/-- The final norm, the stream times the reciprocal. The claim that the sumcheck leaves. Its end
values are the reciprocal, read in the ledger, and the stream under the weights of the segment NF,
read in the stream's second table. -/
def claimStream (R : Run) : SubM Unit := do
  let x := R.x
  let wh ← ewh R "NF"
  let t ← tabAt R "xbL@Y_N"
  let mut SX : Aff := {}
  for kh in [0:R.h.d / R.h.S2] do
    SX := Aff.addMul SX (← xbA R t kh) (wh.getD kh zeroE)
  SubM.lin x.tN.rowU
  let recip ← if R.h.XL == 5 then (·.R) <$> row5At R "rt_N" else (·.R) <$> rowAt R "rt_N"
  SubM.lin (S_ x.tN.sEnd - recip)
  SubM.lin (S_ (x.tN.sEnd + 1) - SX)

/-- The lookup's one claim on the key vectors of all calls. The places at which the key forms put
the padding key must be as many, tree by tree, as the lookup has counted. -/
def claimJoin (R : Run) : SubM Unit := do
  let mut KF : Array Aff := #[]
  let mut laid := Array.replicate R.x.g1.shape.NT 0
  for q in [0:R.L.calls.size] do
    let (v, l) ← keyForm R q laid
    KF := KF.push v
    laid := l
  Forest.paddingLaid R.x.g1 laid
  SubM.lin (← Forest.join R.x.g1 KF)

/-- The four lines of the acceptance policy, on the hidden numbers c, b, u, k, z, zs of the
positions that have a cost. Their digits are keys of the call with the segment ROW, which is meant
to keep all six at or above 0.
 1. Summed over these positions: c + C b + u = theta times their number.
 2. Summed over these positions: b + z = cap, or 0 if there is no such position.
 3. At each such position c + k = C, tested at the random point of the call with HD0.
 4. At each such position zs and the position's V table values add up to 2^F, tested at the same
    point.
The constant of line 4: the table that is read sums the cells of ex over all JV columns, each
reading is short by the offset of ex, and a column from V on holds 2^F.
With the margins (OnBytes/Model/HeadForms.lean) the lines are meant to give this: c is at most C;
the costs, each clipped at C, add up to at most theta times the number of these positions; at most
cap of them have a cost above C. A cost is the logit gap plus 2^sh. If sT - sh is 4 to 10, the same
is meant to hold with the token's negative log-probability at the exponent sT as the cost; at sT -
sh = -4 line 4 says only that no middle digit of a margin is 0. No theorem here shows any of this.
-/
def claimPolicy (R : Run) : SubM Unit := do
  let h := R.h
  let L := R.L
  let R_ := ofNat R.cov.hRC
  let ERC := ercOf R
  SubM.lin ((← gapAt R "rhoC" 0 R_) + Aff.scale (← gapAt R "rhoC" 1 R_) (ofNat h.clipC) +
    (← gapAt R "rhoC" 2 R_) - Aff.ofConst (scaleNat R_ h.theta))
  SubM.lin ((← gapAt R "rhoC" 1 R_) + (← gapAt R "rhoC" 4 R_) -
    Aff.ofConst (ofNat (if R.cov.hRC != 0 then h.cap else 0)))
  SubM.lin ((← gapAt R "phiC" 0 ERC) + (← gapAt R "phiC" 3 ERC) -
    Aff.ofConst (scaleNat ERC h.clipC))
  let te ← tabAt R "hf@phiZ"
  let mut a := (← gapAt R "phiC" 5 ERC) + Aff.ofConst
    (subE (mulE (scaleNat ERC offE) (ofNat L.JV)) (scaleNat ERC ((L.JV - h.V + 1) * 2 ^ h.famF)))
  for l in [0:exc] do
    for xh in [0:L.JV / h.S2] do
      a := Aff.addMul a (← U3at R te ((L.oE + l * L.JV) / h.S2 + xh)) (ofNat (256 ^ l))
  SubM.lin a

/-- The three claims of the lookup that read the planes of its counts. They read them in the three
tables of bH. -/
def claimPlanes (R : Run) : SubM Unit := do
  let tB0 ← tabAt R "bH-bits-0"
  let tB1 ← tabAt R "bH-bits-1"
  let tP ← tabAt R "bH-pin"
  let col : Nat → Nat → SubM Aff := fun t x => do
    mustAs "internal-h-table-index" (x < R.L.kb)
    U3at R t x
  Forest.planeLins R.x.g1 R.h.lmbH (fun e x => col (if e == 0 then tB0 else tB1) x) (col tP)

/-- The logits against the normalized activations and the weights. The claim that the last token
sumcheck leaves. Its first end value is the activations at the point of all challenges, read in the
second table of hd. Its second end value is the one that the merge takes (`Heard.sV`). -/
def claimLogits (R : Run) : SubM Unit := do
  let x := R.x
  let eq := eqLow x.rs 0 R.hp.lamS
  let t ← tabAt R "hd@r_H"
  let mut Alin : Aff := {}
  for kk in [0:R.h.d] do
    Alin := Aff.addMul Alin (← sh2 R t kk) (eq.getD kk zeroE)
  SubM.lin x.tH.rowU
  SubM.lin (S_ x.tH.sEnd - Alin)

/-- Records the constant of the one equation as it is after a group of claims. -/
def noteConstant (group : String) : SubM Unit := do
  noteH ("constant behind " ++ group) (← get).c0

/-- Adds all claims of the sub-proof, in the order of the C++ routine. Returns the tail's new
state. -/
def walk (R : Run) (tl : HTailF2) (wo : WsForkOut) : LinkM HTailF2 := do
  Forest.objects R.x.g1
  noteConstant "the look-up's claims on mask entries"
  claimSquares R
  noteConstant "the sum of squares"
  claimLedger R
  noteConstant "the row ledger"
  claimStream R
  noteConstant "the stream times the reciprocal"
  claimJoin R
  noteConstant "the look-up's join"
  claimPolicy R
  noteConstant "the acceptance policy"
  claimPlanes R
  noteConstant "the look-up's planes"
  let tl ← tl.objectsF R.t.funs
  noteConstant "the smallness test"
  claimLogits R
  noteConstant "the logits"
  wsForkLin wo.toWsMerged
  noteConstant "the merge"
  pure tl

/-- Tests of the verifier's own walk. Every slot has a coefficient other than 0 in the one equation,
except the slot of the merge's end value, which has 0: what that value is, no claim of this
sub-proof says; the row on the committed weights does. This first test must stay: a value that the
prover sends and that no claim names would be bound by no equation, and no verifier would notice.
The numbers of claims, of draws of the matrix and of lookups are the expected ones. Then come the
tail's own tests. The tail's coefficients, which its closing steps use, are computed here too. -/
def selfTests (R : Run) (tl : HTailF2) (wo : WsForkOut) : LinkM Unit := do
  let F ← LinkM.fork
  testAs "internal-h-free-slot"
    ((List.range R.hp.nMsg).all fun j => isZeroE (F.LS.getD j zeroE) == (j == wo.sFv))
  mustAs "internal-h-claim-count" (F.nClaim == R.hp.nLin)
  mustAs "internal-h-rows-booked" (tl.foldDrawn == 1)
  mustAs "internal-h-calls-booked" (1 + tl.groupsRun == 2)
  mustAs "internal-f-fun-moved" (tl.funsHeld R.t.funs)
  tl.selfTest R.hp.nU
  tl.coefficients
  tl.rkSelfTest

/-- True if what the caller (runLinkH, OnBytes/Model/StagesLinks.lean) passes in agrees with the
plan hp: the list is closed and has hp's records, and each array has hp's name, rows, columns and
number of virtual rows. buildLinksH, in the same file, has compared the chain's layout with the
arrays of the record from which runLinkH passes them in, and this check takes its counts from hp.
This test makes sure that both are the same plan. -/
def planHanded (hp : HPlanH2) (list : Tail2) (F : Fork) : Bool :=
  list.planned && list.nt == hp.Tp.nt &&
    F.trees.map (fun X => (X.name, X.R, X.K, X.rows.size)) ==
      hp.Fp.trees.map (fun X => (X.name, X.R, X.K, X.rows.size))

/-- The check of the head's sub-proof, from just after the link's first message to the link's close.
It runs in the state of the link that the caller has opened: the caller sets the state of the
chain's calls, the link's number, the names of its arrays, the list of arrays and the arrays
themselves. The check starts from these arrays and rebuilds none of this. h, L, b, hp: the public
numbers, the layout, the matrix of the stream and the plan. O: the plan of the last group of layers.
cov: the covered positions of the request, as `coveredOf` makes them for this h's T; the first test
refuses arrays of another length. wsLay: the layout of the committed matrix of weights. Returns what
the merge leaves for the row on the committed weights. -/
def runForkHidH2 (h : Shape) (L : HL) (b : Border) (hp : HPlanH2) (O : Owner) (cov : Covered)
    (wsLay : WsLay) : LinkM WsForkOut := do
  -- Beyond the end of a short hOn a position would read as not covered, and beyond the end of a
  -- short hOnC as a position without a cost.
  mustAs "internal-h-covered" (cov.sized h.T)
  let C ← get
  let plain := C.check.plain
  mustAs "plan-link" (planHanded hp C.list (← LinkM.fork))
  LinkM.sub (SubM.change fun F => some ({ trees := F.trees } : Fork).fillL)
  mustAs "internal-h-owner-TX" (!O.tl.ix.TX.isEmpty && O.tl.kTX.back? == some b.kxb)
  let iU3 ← getAs "internal-h-tree-list" (hp.tl.ix.U.getD 2 none)
  let x ← hear h L hp cov plain
  rootInH [iU3]
  let t ← tablesOf h L hp cov x
  let R : Run := { h := h, L := L, b := b, hp := hp, cov := cov, x := x, t := t, iU3 := iU3 }
  let tl ← getAs "internal-f-fun-closed" (hp.tl.closeFuns t.funs)
  let tl ← tl.transcript
  let claim ← weightsClaim R wsLay
  mustAs "internal-claim-count" (hp.NCL == 1)
  let wo ← wsForkEnd wsLay #[claim] #[x.sV]
  let slot ← SubM.slot
  mustAs "internal-slot-count" (slot == hp.nMsg)
  SubM.setPlanClaims hp.nLin
  t2Batch slot
  let tl ← walk R tl wo
  selfTests R tl wo
  doorH (← getAs "internal-f-draws" tl.equationsLaidF)
  let F ← LinkM.fork
  mustAs "internal-f-draws" (F.nClaim == F.planClaimsF)
  SubM.allTaken
  mustAs "internal-f-draws" tl.foldAllTakenF
  pure wo

end OnBytes.Model.Head
