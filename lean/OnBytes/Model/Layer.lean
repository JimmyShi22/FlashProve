-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Layer.lean: the check of the sub-proof of one group of layers.

A request's proof has one sub-proof for each group of 2^ll layers. Its statement is that the cells
to which the prover has committed are the values of the model's integer arithmetic on these layers:
the two norms, the products with the weight matrices, the rounding of each product, the rotary
embedding, the gated feed-forward part and, if the model has routed experts, these experts on every
second layer. In profile 4 attention itself has a sub-proof of its own. In profile 3 no sub-proof
checks it: public numbers made from a seed (stubO) take the place of its output.

This file follows verifier/src/vf_layers_check.inc and keeps that file's order of messages and of
claims. The check has two passes.
 1. The messages, in the prover's order: the lookup of all calls; the norms' convolution sums W_s,
    of which the sums of squares are composed, with a product layer; the norms' row products with a
    token sumcheck; a second token sumcheck for the terms that are products of two vectors over the
    tokens; the batched sumcheck of all inner products; one or two product layers for the gated
    products; the merge of the weight claims; the root of the reads; the smallness test; the element
    that batches the claims.
 2. The claims. No equation of the protocol is tested while the messages are read. Each part leaves
    linear claims on hidden values and on entries of the reads. They are added up under the powers
    of the last drawn element, and the one equation that results is handed to the request's chain.
Besides these claims, this file itself makes three tests on values, each under its name in the C++
verifier: the last la coordinates of every call's point are those of the lookup's point; the element
eps of the second token sumcheck is not 0; and every slot has a coefficient other than 0 in the one
equation, except one, which has 0. The parts that it calls, the smallness test for one, make further
tests on values under their own names.

Words. Slot, hidden value, shown value, claim and form (Aff) are those of OnBytes/Model/Hide.lean: a
slot is the number of a scalar that the prover sends, and a form is a constant plus a linear
combination of hidden values and of entries of committed arrays. The reads are one committed vector
(U3) that holds all tables (OnBytes/Model/LayerForms.lean). Panels and never-sent vectors are
explained in OnBytes/Model/LayerPanels.lean.

The same code runs twice, as every block does (OnBytes/Iop/Ground.lean): a dry run on zeros gives
the list of the chain's rounds, and a run on the values read from the proof file (a view) gives the
decision. Which messages are received and which rounds are closed follows from public numbers alone.

Main definitions: Heard, hearLook, normsStart, hearNorms, hearTerms, joinStart, hearStack,
hearGated, pointsOf, funsOf, hearOwn, claimsNorms, claimsLedger4, claimsLedger5, claimsTerms,
claimsGated, claimsOneHot, claimsPlanes, claimEmbedding, freeSlotTest, runForkHidG2, names.

What is not claimed: nothing is proved here. Names of sections, which the C++ source gives its
claims for a test's report, have no counterpart here.
-/
import OnBytes.Model.LayerPlan
import OnBytes.Model.LayerPanels
import OnBytes.Model.Merge

namespace OnBytes.Model.Layer

/-- Unwraps x; the check fails if x is none. Whether x is there depends only on public numbers and,
at claimE (OnBytes/Model/LayerPanels.lean), on the request's tokens. Not to be confused with the
affine forms (Aff) of which the rest of the file speaks. -/
def form {α : Type} (x : Option α) : SubM α := SubM.get x

/-- A name of a refusal with the group's number before it, as the C++ verifier prints it. -/
def ofGroup (g : Nat) (name : String) : String := s!"G{g}:" ++ name

/-- Keeps an intermediate value under a name, if the run keeps such values (Proof.firstNotes,
OnBytes/Proof/File.lean). The program's own runs keep none. No test reads it. -/
def note (what : String) (x : E) : SubM Unit := Blk.note ("layer: " ++ what) x

/-- Records the constant of the one equation after one part of the claims has been added. -/
def noteClaims (what : String) : SubM Unit := do note ("c0 after " ++ what) (← get).c0

/-- The values that were shown under the n slots from first on. -/
def shownRun (first n : Nat) : SubM (Array E) :=
  (Array.range n).mapM fun i => SubM.shown (first + i)

/-! ## The messages -/

/-- What the verifier holds after the messages of the norms and of the two token sumchecks. -/
structure Heard where
  /-- the lookup of all calls -/
  fo : Forest.Heard
  /-- the norms' token point -/
  PV : Array E
  /-- in the first group: the embedding's point -/
  ZE : Array E := #[]
  /-- in the first group: the further coordinates of the embedding's feature -/
  tkh : Array E := #[]
  /-- the last lt coordinates of the lookup's point -/
  ztF : Array E
  /-- the first slot of the convolution sums W_s (OnBytes/Model/Ledger.lean) -/
  sW : Nat
  /-- the powers that batch the convolution sums -/
  gp : Array E
  /-- the product layer of the squares -/
  wpl : Level
  /-- the first slot of the row products -/
  sPv : Nat
  /-- the powers that batch the row products -/
  omV : Array E
  /-- the token sumcheck of the row products -/
  tV : Tsc
  /-- the second token sumcheck, if some call has terms for it -/
  tT : Option Tsc := none
  /-- what the second token sumcheck leaves: the sum of its terms at its end point, with the shown
  values in the place of the shown factors -/
  KT : Aff := {}

/-- The start form and the point of the product layer of the squares. The vector of each feature's
squares, summed over the tokens under the equality weights at PV, is never sent. The layer runs on
its sum over the features, with equality weights at rhoI on the norms' numbers and plain weights on
the features. A plain weight is twice the equality weight at 1/2, so the point has 1/2 in the
features' coordinates, and the start form is divided by 2^lPd. -/
def normsStart (y : Lay) (sW : Nat) (gp rhoI PV : Array E) : Aff × Array E :=
  let NSl := ledNS y.h.xl
  let e := eqTab rhoI
  let half := invE (ofNat 2)
  let scale := powE half y.lPd
  let C := (List.range y.NI).foldl
    (fun C i =>
      let w := mulE scale (e.getD i zeroE)
      (List.range NSl).foldl
        (fun (C : Aff) s => C.addMul (Aff.slot (sW + NSl * i + s)) (mulE w (gp.getD s zeroE))) C)
    aff0
  (C, rhoI ++ Array.replicate y.lPd half ++ PV)

/-- Runs the one lookup for all calls of the layout. Fails unless the numbers that the run computes
equal the layout's (y.fo), from which the layout sized the matrix b and the reads, and the plan
counted the slots. -/
def hearLook (y : Lay) (g : Nat) : SubM Forest.Heard := do
  let fo ← Forest.pad y.cl y.fo.pub y.h.lidb
  let s := fo.shape
  mustAs (ofGroup g "internal-g-forest")
    (s.dT == y.fo.dT && s.kT == y.fo.kT && s.NT == y.fo.NT && s.rK == y.fo.rK &&
      s.first == y.fo.first && s.iota == y.fo.iota && s.callOf == y.fo.callOf)
  pure fo

/-- The points, and the messages of the norms: the convolution sums, the product layer of the
squares, the row products and their token sumcheck. fo: the lookup. -/
def hearNorms (P : Pub) (g : Nat) (fo : Forest.Heard) : SubM Heard := do
  let y := P.y
  let h := y.h
  let xl := h.xl
  let s := fo.shape
  let PV ← SubM.point .zero h.lt
  let ZE ← if g == 0 then SubM.point .zero (y.ls + h.lt) else pure #[]
  let tkh ← if g == 0 then SubM.point .zero (y.lPd - y.ls) else pure #[]
  -- The last la coordinates of every call's point are the last la of the lookup's point.
  mustAs "forest-depth-G" (h.la ≤ s.dT)
  let Z ← form (lastOf fo.zx h.la).toOption
  let ends ← form (fo.zk.mapM fun zk => (lastOf zk h.la).toOption)
  Blk.check (ofGroup g "internal-g-merged-point") (ends.all (· == Z))
  let ztF ← form (lastOf fo.zx h.lt).toOption
  let sW ← SubM.claimsIn (ledNS xl * y.NI)
  let gp ← SubM.batch (ledNS xl)
  let rhoI ← if P.rd.lNI != 0 then SubM.point .join P.rd.lNI else pure #[]
  let (C, rho) := normsStart y sW gp rhoI PV
  let wpl ← levelIn P.rd.muV rho C (orderDefault P.rd.muV)
  let sPv ← SubM.claimsIn (ledNP xl * y.NI)
  let omV ← SubM.batch (ledNP xl * y.NI)
  let tV ← tscIn PV h.lt (ledNO xl * y.NI) 2
  note "alpha" fo.alpha
  note "theta" fo.theta
  note "zx[0]" (fo.zx.getD 0 zeroE)
  note "P_V[0]" (PV.getD 0 zeroE)
  note "gam" (gp.getD 1 zeroE)
  note "wpl.r[0]" (wpl.r.getD 0 zeroE)
  note "omV[1]" (omV.getD 1 zeroE)
  note "tV.r[0]" (tV.r.getD 0 zeroE)
  pure { fo, PV, ZE, tkh, ztF, sW, gp, wpl, sPv, omV, tV }

/-- The number of values that the second token sumcheck shows: the reciprocal of every norm and,
with routed experts, the score and the selector's entries of every layer that has them. -/
def nEndT (y : Lay) : Nat := y.NN * y.Lam + (if y.h.p3 then y.LamM * (1 + y.h.NE) else 0)

/-- The second token sumcheck, if some call has terms for it. KT is its summand at its end point
(Heard.KT). The factors of KT that are not shown hold products with weights, so KT cannot be written
as a form in the reads. pscRow is therefore asked for the claim without the summand (S0 = 0, nothing
kept). It returns a form u in slots, and the sumcheck's claim reads u + eps KT = 0. So KT is set to
-u / eps and enters the start form of the batched sumcheck (joinStart), whose panels prove the
products. A drawn eps of 0 is refused at the end of the run (Blk.check); in such a run KT is 0. -/
def hearTerms (P : Pub) (H : Heard) : SubM Heard := do
  if P.rd.tscCalls.isEmpty then pure H
  else
    let tT ← tscIn H.ztF P.y.h.lt (nEndT P.y) 1
    Blk.check "coin-zero" (!isZeroE tT.p.eps)
    let (row, p) ← pscRow tT.p zeroE
    note "tT.r[0]" (tT.r.getD 0 zeroE)
    note "tT.eps" tT.p.eps
    pure { H with tT := some { tT with p := p }, KT := row.scale (negE (invE tT.p.eps)) }

/-- The start form of the batched sumcheck: the lookup's join with the inner products moved to the
sumcheck's side, less the claimed sum of the second token sumcheck, plus om[1] times what that
sumcheck leaves. Tests, as Forest.join does (OnBytes/Model/Look.lean), that there is one part
(joinPart) and one weight e for each call of the lookup; the C++ routine has no such test. Also
tests, tree by tree, that the columns which no segment lists hold as many keys as the lookup counts
as padding. That test reads the segments' lists of columns (weighedOf), not the forms. -/
def joinStart (v : Env) (H : Heard) (om : Array E) : SubM Aff := do
  let fo := H.fo
  let s := fo.shape
  let weighed ← form (v.y.calls.mapM v.weighedOf)
  let parts ← form ((v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
    v.joinPart fo.alpha fo.theta x.2 x.1.1 x.1.2)
  mustAs "internal-forest-join" (parts.length == s.calls.size && fo.e.size == s.calls.size)
  let c0 := parts.zipIdx.foldl (fun (a : Aff) x => a.addMul x.1 (fo.e.getD x.2 zeroE)) aff0
  Forest.paddingLaid fo
    (← form (weighed.toList.zipIdx.foldlM (fun laid x => v.laidOf x.2 x.1 laid) (Forest.noPub s)))
  let ey := eqTab fo.zy
  let pad := (List.range (2 ^ s.rK - s.NT)).foldl
    (fun a t => addE a (mulE (ey.getD (s.NT + t) zeroE) (subE fo.alpha (fo.padKey 0)))) zeroE
  let c1 := c0 + Aff.ofConst pad
  let c2 := match H.tT with
    | some tT => c1 - Aff.slot tT.sCl
    | none => c1
  let c3 := c2 - fo.cEnd
  pure (if H.tT.isSome then c3.addMul H.KT (om.getD 1 zeroE) else c3)

/-- What the verifier holds after the batched sumcheck. -/
structure HeardStack where
  /-- the challenges, rs[t] for bit t -/
  rs : Array E
  /-- the slot of the shown value of the A side -/
  sA0 : Nat
  /-- the slot of the first never-sent vector's value -/
  sH1 : Nat
  /-- the slot of the shown value of the B side -/
  sB0 : Nat
  /-- the slot of the first weight claim's value -/
  sV : Nat
  /-- the two sides' values at the end point, and the forms that the two shown values must equal -/
  fin : StackEnd
  /-- the claim that the sumcheck leaves -/
  rowS : Aff

/-- The numbers of the calls that have terms in the second token sumcheck. Returns none if the
layout has no call of one of their names. -/
def callsTS (P : Pub) : Option (List Nat) := P.rd.tscCalls.mapM P.y.callNo

/-- The public numbers that take the place of the attention output at profile 3.
C++: stubO in runStage, verifier/src/cp_verify.cpp. -/
def stubO (y : Lay) (l t j : Nat) : Int :=
  let x := (mix64 (y.h.seed + 80 * 2 ^ 40 + (l * y.T + t) * y.dq + j).toUInt64).toNat % 4096
  if x == 0 then 0 else (x : Int) - 2048

/-- The element that joins the two claims, the batched sumcheck and its end. NCLp: the number of
the panels' weight claims by the plan; lamS: the number of rounds by the plan. -/
def hearStack (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) : SubM HeardStack := do
  let y := P.y
  let om ← if H.tT.isSome then SubM.batch 2 else pure #[oneE]
  let shownT ← match H.tT with
    | some tT => shownRun tT.sEnd (nEndT y)
    | none => pure #[]
  let pe : PanelEnv := { v, e := H.fo.e, shownT, zt := H.ztF, stubO := stubO y }
  let TS ← form (callsTS P)
  let pans ← form (panelsT pe TS (panelsA pe {}))
  let (bl, places) := placePanels pans.bl
  mustAs (ofGroup v.g "internal-stack") (ceilLog2 places == lamS)
  let p ← pscBegin (← joinStart v H om)
  note "om[1]" (om.getD 1 zeroE)
  note "the public part of the batched sum-check's start" p.target
  let st ← stackRounds { lam := lamS, p := p }
  let NVIRT := 1 + (if y.h.p3 then y.LamM else 0)
  mustAs (ofGroup v.g "internal-claim-count") (pans.nextV == NCLp)
  let (sA0, p) ← pscEnds st.p 2 (2 + NVIRT + NCLp)
  let sH1 := sA0 + 1
  let sB0 := sH1 + NVIRT
  let sV := sB0 + 1
  let fin ← form (stackEnd y bl st.rs lamS om (← shownRun sH1 NVIRT) (← shownRun sV NCLp)
    (← SubM.shown sA0) (← SubM.shown sB0))
  let (rowS, _) ← pscRow p (mulE fin.As fin.Bs)
  note "rs[0]" (st.rs.getD 0 zeroE)
  note "As" fin.As
  note "Bs" fin.Bs
  pure { rs := st.rs, sA0, sH1, sB0, sV, fin, rowS }

/-- The coordinates n - 1 down to 0 of rs. -/
def downFrom (rs : Array E) (n : Nat) : Array E := (rs.extract 0 n).reverse

/-- The product layer of the gated products, from the shown value of the never-sent vector of the
down product's panel; and, with routed experts, the second one. The routed layers' never-sent
vectors were all shown at one point of the column bits. Their values are combined under the
equality weights of a fresh point of the layer bits. A group with a single such layer (ll = 1) draws
no point: the one value then stands by itself, under the weight 1. -/
def hearGated (P : Pub) (H : Heard) (K : HeardStack) : SubM (Level × Option Level) := do
  let y := P.y
  let h := y.h
  let hd ← levelIn P.rd.muH (downFrom K.rs K.fin.wD ++ H.ztF) (Aff.slot K.sH1)
    (orderRange P.rd.muH)
  note "hd.r[0]" (hd.r.getD 0 zeroE)
  if !h.p3 then pure (hd, none)
  else
    let tT ← form H.tT
    let rhoM ← if h.ll > 1 then SubM.point .join (h.ll - 1) else pure #[]
    let e := eqTab rhoM
    let C := (List.range y.LamM).foldl
      (fun (C : Aff) lm => C.addMul (Aff.slot (K.sH1 + 1 + lm)) (e.getD lm zeroE)) aff0
    let hd2 ← levelIn P.rd.muH2 (rhoM ++ downFrom K.rs y.lfe ++ tT.r) C (orderRange P.rd.muH2)
    note "hd2.r[0]" (hd2.r.getD 0 zeroE)
    pure (hd, some hd2)

/-- The points at which the tables are read, by name. Returns none if a point from which the last la
coordinates are taken has fewer. -/
def pointsOf (y : Lay) (H : Heard) (hd : Level) (hd2 : Option Level) :
    Option (List (String × Array E)) := do
  let last (z : Array E) : Option (Array E) := (lastOf z y.h.la).toOption
  let Z ← last H.fo.zx
  let terms := match H.tT with
    | some tT => [("Y", longPoint (Z.extract 0 y.ls) tT.r), ("rt", tT.r)]
    | none => []
  let routed ← match hd2 with
    | some o => (last o.r).map fun z => [("Z_b", z)]
    | none => some []
  pure ([("Z", Z), ("zt", H.ztF), ("Z_V", ← last H.wpl.r), ("P_V", H.PV), ("Z_E", H.ZE),
    ("r_tV", H.tV.r), ("Z_a", ← last hd.r)] ++ terms ++ routed)

/-- The weights of one family of tables on the rows over which an entry sums. Returns none if the
family's point is not among pt or does not have the length that the kind of table asks for. -/
def phiOf (y : Lay) (fo : Forest.Heard) (pt : List (String × Array E)) (a : TableAsk) :
    Option (Array E) :=
  if a.name == "b-bits-0" then Forest.phiB fo y.h.lmb 0
  else if a.name == "b-bits-1" then Forest.phiB fo y.h.lmb 1
  else if a.name == "b-pin" then some (Forest.phiP y.h.lmb)
  else
    match pt.find? fun p => p.1 == a.point with
    | none => none
    | some p =>
      if p.2.size != (if a.lng then y.h.la else y.h.lt) then none
      else some (if a.lng then longPhi p.2 y.ls y.h.lt else eqTab p.2)

/-- All tables with their weights, in their order in the reads. The number 2 says that they lie in
the reads: of the vectors U1 to U3 of OnBytes/Model/Tail.lean, counted from 0, the reads are U3.
Returns none if phiOf returns none for a family. -/
def funsOf (y : Lay) (fo : Forest.Heard) (pt : List (String × Array E))
    (laid : List (TableAsk × List (Nat × Nat))) : Option (Array HFun) := do
  let l ← laid.mapM fun x => do
    let phi ← phiOf y fo pt x.1
    pure (x.2.map fun m => ({ mat := m.1, len := x.1.L, phi, tree := 2, start := m.2 } : HFun))
  pure l.flatten.toArray

/-! ## The claims -/

/-- The claims of the sums of squares: the product layer's; that its two end values are one
vector's; and that this vector is the residual stream's limbs under the powers gp. -/
def claimsNorms (P : Pub) (v : Env) (H : Heard) : SubM Unit := do
  let y := P.y
  let wpl := H.wpl
  layerObject wpl
  SubM.lin (Aff.slot wpl.sL - Aff.slot wpl.sR)
  let txs ← form (y.T_ "xs")
  mustAs "plan-tensor-layout"
    (txs.nl == y.xb.nl && y.xb.nl == y.h.xl && ledNS y.h.xl == 2 * y.xb.nl - 1)
  let tI ← form (v.tabAt "xbI@Z_V")
  let tA ← form (v.tabAt "af@Z_V")
  let e ← form (hiTab wpl.r y.h.la (P.rd.lNI + y.lPd - y.ls)).toOption
  let blocks := y.h.d / y.S2
  let sum ← form (sumForms (y.NI * blocks * y.xb.nl) fun x =>
    let l := x % y.xb.nl
    let kh := x / y.xb.nl % blocks
    let i := x / y.xb.nl / blocks
    (if i == 0 then v.U3at tI (tenCell y.xb l 0 0 / y.S2 + kh)
     else v.U3at tA (tenCell txs.place l (i - 1) 0 / y.S2 + kh)).map fun a =>
      (a, negE (mulE (e.getD (i * y.Pd / y.S2 + kh) zeroE) (H.gp.getD l zeroE))))
  SubM.lin (Aff.slot wpl.sL + sum)

/-- The claim that the token sumcheck of the row products starts from their batch. -/
def claimRowBatch (y : Lay) (H : Heard) : SubM Unit :=
  SubM.lin ((List.range (ledNP y.h.xl * y.NI)).foldl
    (fun (a : Aff) i => a.addMul (Aff.slot (H.sPv + i)) (negE (H.omV.getD i zeroE)))
    (Aff.slot H.tV.sCl))

/-- 2^(M + 1) for norm number i of the group, as a form. M is word LM1 or LM2 of the layer's record
of scales. Norm i of the group is norm 1 + i % 2 of layer i / NN; a layer has NN = 2 norms. -/
def twoM (v : Env) (i : Nat) : Aff :=
  Aff.ofConst (pw (v.sc.kl (v.lay (i / v.y.NN)) (if i % 2 == 1 then LM2 else LM1) + 1))

/-- The constant eps of norm number i of the group. -/
def epsOf (y : Lay) (i : Nat) : E := ofNat (if i % 2 == 1 then y.h.eps2 else y.h.eps1)

/-- The claims of the norms' rows with five limbs: the token sumcheck's; that the four shown values
of each norm equal their forms in the reads; the nine carries of each norm's convolution sums; the
eight lines of each norm's row. -/
def claimsLedger5 (v : Env) (H : Heard) : SubM Unit := do
  let y := v.y
  let NI := y.NI
  let tV := H.tV
  mustAs "plan-tensor-layout" (ledNO y.h.xl == 4)
  let sh ← shownRun tV.sEnd (4 * NI)
  let S0 := (List.range NI).foldl
    (fun s i => addE s (ledProducts5 H.omV (7 * i) (sh.getD (4 * i) zeroE)
      (sh.getD (4 * i + 1) zeroE) (sh.getD (4 * i + 2) zeroE) (sh.getD (4 * i + 3) zeroE)))
    zeroE
  SubM.lin (← pscRow tV.p S0).1
  for i in List.range NI do
    let r ← form (v.row5At "r_tV" i)
    for (k, f) in [r.a, r.b, r.Rlo, r.Rhi].zipIdx.map fun x => (x.2, x.1) do
      SubM.lin (Aff.slot (tV.sEnd + 4 * i + k) - f)
  let rP ← form ((Array.range NI).mapM fun i => v.row5At "P_V" i)
  for (r, i) in rP.toList.zipIdx do
    for s in List.range 9 do
      SubM.lin (ledCarry5 r s (Aff.slot (H.sW + 9 * i + s)))
  for (r, i) in rP.toList.zipIdx do
    let Pr := (Array.range 7).map fun j => Aff.slot (H.sPv + 7 * i + j)
    (ledLines5 r Pr (epsOf y i) (twoM v i)).forM SubM.lin

/-- The same with four limbs: three shown values, seven carries and five lines for each norm. -/
def claimsLedger4 (v : Env) (H : Heard) : SubM Unit := do
  let y := v.y
  let NI := y.NI
  let tV := H.tV
  mustAs "plan-tensor-layout" (ledNO y.h.xl == 3)
  let sh ← shownRun tV.sEnd (3 * NI)
  let S0 := (List.range NI).foldl
    (fun s i =>
      let a := sh.getD (3 * i) zeroE
      let t (k : Nat) : E :=
        mulE (mulE (H.omV.getD (3 * i + k) zeroE) (sh.getD (3 * i + k) zeroE)) a
      addE (addE (addE s (t 0)) (t 1)) (t 2))
    zeroE
  SubM.lin (← pscRow tV.p S0).1
  for i in List.range NI do
    let r ← form (v.rowAt "r_tV" i)
    for (k, f) in [r.sig, r.Rlo, r.Rhi].zipIdx.map fun x => (x.2, x.1) do
      SubM.lin (Aff.slot (tV.sEnd + 3 * i + k) - f)
  let rP ← form ((Array.range NI).mapM fun i => v.rowAt "P_V" i)
  for (r, i) in rP.toList.zipIdx do
    for s in List.range 7 do
      SubM.lin (Aff.slot (H.sW + 7 * i + s) + r.c.getD s aff0 - r.Dg.getD s aff0 -
        (r.c.getD (s + 1) aff0).scale (ofNat 256))
  for (r, i) in rP.toList.zipIdx do
    let pv (k : Nat) : Aff := Aff.slot (H.sPv + 3 * i + k)
    SubM.lin (r.V + Aff.ofConst (epsOf y i) - pv 0 - r.l1)
    SubM.lin (r.l1 + r.h1 - r.sig.scale (ofNat 2))
    SubM.lin (pv 2 - r.p1)
    SubM.lin (twoM v i + r.sig - r.s0 - (pv 1).scale (ofNat 2) - r.p1.scale (ofNat (2 ^ 25)) -
      r.rr.scale (ofNat 2))
    SubM.lin (r.rr + r.rq - r.sig + Aff.ofConst oneE)

/-- The claims that the values which the second token sumcheck has shown equal their forms in the
reads at its end point: the reciprocals, the scores, the selectors' entries. Its own claim is inside
the start form of the batched sumcheck. -/
def claimsTerms (v : Env) (H : Heard) : SubM Unit := do
  let y := v.y
  match H.tT with
  | none => pure ()
  | some tT =>
    let n := y.NN * y.Lam
    for i in List.range n do
      SubM.lin (Aff.slot (tT.sEnd + i) - (← form (v.rowR "rt" i)))
    if y.h.p3 then
      for lm in List.range y.LamM do
        SubM.lin (Aff.slot (tT.sEnd + n + lm) - (← form (v.shA "sc" "rt" lm 0)))
      for x in List.range (y.LamM * y.h.NE) do
        SubM.lin (Aff.slot (tT.sEnd + n + y.LamM + x) -
          (← form (v.shA "sel" "rt" (x / y.h.NE) (x % y.h.NE))))

/-- The two claims on the end values of a product layer o of the gated products: the left one plus
the tensor s at the layer's point is 0, and so is the right one plus the tensor u. So each end value
is the negative of its tensor's value, and their product is the product of the two tensors' values.
e: the weights of the blocks at the layer's point; t: the first entry of the tables of af at that
point; rows: the layers; blocks: the blocks of features of a layer; stride: the distance of two
layers in e; lamOf and first give a row's layer and its first block. -/
def claimsEnds (v : Env) (o : Level) (e : Array E) (t rows blocks stride : Nat)
    (lamOf : Nat → Nat) (first : Nat) : SubM Unit := do
  let ts ← form (v.y.T_ "s")
  let tu ← form (v.y.T_ "u")
  let sumOf (X : Ten) : Option Aff :=
    sumForms (rows * blocks) fun x =>
      (v.longA t X (lamOf (x / blocks)) (first + x % blocks)).map fun a =>
        (a, e.getD (x / blocks * stride + x % blocks) zeroE)
  SubM.lin (Aff.slot o.sL + (← form (sumOf ts)))
  SubM.lin (Aff.slot o.sR + (← form (sumOf tu)))

/-- The claims of the one or two product layers of the gated products. -/
def claimsGated (P : Pub) (v : Env) (hd : Level) (hd2 : Option Level) : SubM Unit := do
  let y := P.y
  let h := y.h
  layerObject hd
  let e ← form (hiTab hd.r h.la (h.ll + y.lPf - y.ls)).toOption
  claimsEnds v hd e (← form (v.tabAt "af@Z_a")) y.Lam (h.f / y.S2) (y.Pf / y.S2) id 0
  match hd2 with
  | none => pure ()
  | some o =>
    layerObject o
    let e ← form (hiTab o.r h.la (h.ll - 1 + y.lfe - y.ls)).toOption
    claimsEnds v o e (← form (v.tabAt "af@Z_b")) y.LamM (h.fe / y.S2) (h.fe / y.S2)
      (fun lm => 2 * lm + 1) (h.fe / y.S2)

/-- With routed experts: at the token point zt the selector's entries of each layer sum to 1. -/
def claimsOneHot (v : Env) : SubM Unit := do
  let y := v.y
  if y.h.p3 then
    for lm in List.range y.LamM do
      let s ← form (sumForms y.h.NE fun e => (v.shA "sel" "zt" lm e).map fun a => (a, oneE))
      SubM.lin (Aff.ofConst (negE oneE) + s)

/-- The lookup's three claims that read the planes, on the three tables of matrix b. -/
def claimsPlanes (v : Env) (fo : Forest.Heard) : SubM Unit := do
  let y := v.y
  let tB0 ← form (v.tabAt "b-bits-0")
  let tB1 ← form (v.tabAt "b-bits-1")
  let tP ← form (v.tabAt "b-pin")
  let col (t x : Nat) : SubM Aff := form (if x < y.kbm then v.U3at t x else none)
  Forest.planeLins fo y.h.lmb (fun e x => col (if e == 0 then tB0 else tB1) x) (col tP)

/-- In the first group: the embedding's value equals its form in the table at the point Z_E of the
stream that comes in. -/
def claimEmbedding (v : Env) (H : Heard) (sVE : Nat) : SubM Unit := do
  let y := v.y
  let e := eqTab H.tkh
  let t ← form (v.tabAt "xbI@Z_E")
  let s ← form (sumForms (y.h.d / y.S2) fun kh => (v.xbA t kh).map fun a => (a, e.getD kh zeroE))
  SubM.lin ((Aff.slot sVE).scale (negE oneE) + s)

/-- A test of this file's own list of claims: every slot occurs in some claim, except the slot of
the value that the merge shows, whose claim leaves the sub-proof. A slot's coefficient in the one
equation is a sum of products of challenges. For an honest proof it is 0 only if no claim holds the
slot, or by a chance of about one in the size of the field. -/
def freeSlotTest (g used sFv : Nat) : SubM Unit := do
  let F ← get
  Blk.check (ofGroup g "internal-g-free-slot")
    ((List.range used).all fun j => isZeroE (F.LS.getD j zeroE) == (j == sFv))

/-! ## The whole check -/

/-- What the verifier holds after the sub-proof's own messages. -/
structure Own where
  /-- what the forms read -/
  v : Env
  /-- the norms and the two token sumchecks -/
  H : Heard
  /-- the batched sumcheck -/
  K : HeardStack
  /-- the product layer of the gated products -/
  hd : Level
  /-- the product layer of the routed experts' gated products -/
  hd2 : Option Level
  /-- in the first group: the slot of the embedding's value -/
  sVE : Nat
  /-- the merge of the weight claims -/
  wo : WsForkOut
  /-- all tables with their weights -/
  funs : Array HFun

/-- The sub-proof's own messages: from the norms' token point, after the lookup, to the value that
the merge shows, before the root of the reads. fo: the lookup. -/
def hearOwn (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) : SubM Own := do
  let y := P.y
  let hasE := g == 0
  let iU3 ← form (hp.tl.ix.U.getD 2 none)
  let H ← hearTerms P (← hearNorms P g fo)
  -- The tables are laid out before the batched sumcheck, whose forms name their entries.
  SubM.must hp.tl.funOpen
  let mats := (P.tails.getD g {}).mats.map fun M => (M.m, M.k)
  let (tab, laid, nU3) ← form (layTables mats (tableAsks y P.rd g) 0)
  mustAs "internal-W-length" (nU3 == hp.nU.getD 2 0)
  let K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0
  let v : Env := { y, sc := P.sc, g, iU3, K3, tab, zk := fo.zk }
  let NCLp := hp.NCL - (if hasE then 1 else 0)
  let K ← hearStack P v H hp.lamS NCLp
  let (hd, hd2) ← hearGated P H K
  -- The merge of the weight claims. In the first group the embedding's claim comes last.
  let ce : ClaimEnv :=
    { v, wsLay := P.wsLay, rope := P.rope, rs := K.rs, rt := (H.tT.map (·.r)).getD #[] }
  let claimsP ← form (ce.weightClaims (← form (callsTS P)))
  let claimsE ← if hasE then form ((ce.claimE H.ZE H.tkh P.V P.tokv).map ([·])) else pure []
  let claims := (claimsP ++ claimsE).toArray
  mustAs (ofGroup g "internal-claim-count") (claims.size == hp.NCL)
  let sVE ← if hasE then SubM.claimsIn 1 else pure 0
  let sVa := (Array.range NCLp).map (K.sV + ·) ++ (if hasE then #[sVE] else #[])
  let wo ← wsForkEnd P.wsLay claims sVa
  note "the merge's shown value" wo.fvp
  -- From here on all points are known.
  let funs ← form (funsOf y fo (← form (pointsOf y H hd hd2)) laid)
  pure { v, H, K, hd, hd2, sVE, wo, funs }

/-- The check of the sub-proof of group g. hp: its plan. The caller starts the link from the plan's
arrays (hp.Fp) and their list (hp.Tp). Returns what the pending row on the committed weights is made
from. C++: runForkHidG2. -/
def runForkHidG2 (P : Pub) (hp : HPlan2) (g : Nat) : LinkM WsForkOut := do
  let y := P.y
  let h := y.h
  let hasE := g == 0
  -- The present link of the request's walk is this sub-proof's.
  let L ← get
  mustAs "internal-g-link" (L.link == (if h.p4 then 2 * g else g))
  -- The link's list of arrays is the plan's, and the link's arrays have the sizes of the plan's.
  let sizes (F : Fork) : Array (Nat × Nat) := F.trees.map fun X => (X.R, X.K)
  LinkM.must (L.list.nt == hp.Tp.nt && sizes (← LinkM.fork) == sizes hp.Fp)
  LinkM.sub (SubM.change fun F => some (F.fillL.slots hp.ns))
  let iU3 ← LinkM.sub (form (hp.tl.ix.U.getD 2 none))
  let o ← LinkM.sub (do hearOwn P hp g (← hearLook y g))
  let v := o.v
  let H := o.H
  let K := o.K
  let wo := o.wo
  let funs := o.funs
  -- The root of the reads.
  rootInH [iU3]
  let tl ← LinkM.sub (form (hp.tl.closeFuns funs))
  -- The messages of the smallness test, and the element that batches the claims.
  let tl ← tl.transcript
  let slot ← LinkM.sub SubM.slot
  mustAs (ofGroup g "internal-slot-count") (slot == hp.used)
  LinkM.sub (SubM.setPlanClaims hp.nLin)
  t2Batch slot
  -- The list of claims.
  LinkM.sub (do note "the element that batches the claims" (← get).theta)
  LinkM.sub (Forest.objects H.fo)
  LinkM.sub (noteClaims "the look-up's own claims")
  LinkM.sub (claimsNorms P v H)
  LinkM.sub (noteClaims "the sums of squares")
  LinkM.sub (claimRowBatch y H)
  LinkM.sub (if h.xl == 5 then claimsLedger5 v H else claimsLedger4 v H)
  LinkM.sub (noteClaims "the norms' rows")
  LinkM.sub (claimsTerms v H)
  LinkM.sub (noteClaims "the second token sum-check's shown values")
  LinkM.sub (claimsGated P v o.hd o.hd2)
  LinkM.sub (noteClaims "the gated products")
  LinkM.sub (claimsOneHot v)
  LinkM.sub (claimsPlanes v H.fo)
  if hasE then LinkM.sub (claimEmbedding v H o.sVE)
  LinkM.sub (noteClaims "the planes and the embedding")
  -- Two counts: the smallness test has drawn its matrix once, and it has run its own lookup. The 1
  -- stands for this check's lookup, which is not counted.
  mustAs (ofGroup g "internal-g-rows-booked") (tl.foldDrawn == 1)
  mustAs (ofGroup g "internal-g-calls-booked") (1 + tl.groupsRun == 2)
  let tl ← tl.objectsF funs
  LinkM.sub (noteClaims "the smallness test")
  LinkM.sub (SubM.lin K.rowS)
  -- The lookup's join is the first summand of the batched sumcheck's start form (joinStart).
  LinkM.sub (Forest.joinAdded H.fo)
  LinkM.sub (SubM.lin (Aff.slot K.sA0 - K.fin.Alin))
  LinkM.sub (SubM.lin (Aff.slot K.sB0 - K.fin.Blin))
  LinkM.sub (wsForkLin wo.toWsMerged)
  LinkM.sub (noteClaims "all claims")
  -- Tests of this file's own list of claims.
  LinkM.sub (freeSlotTest g hp.used wo.sFv)
  mustAs (ofGroup g "internal-g-claim-count") ((← LinkM.fork).nClaim == hp.nLin)
  LinkM.must (tl.funsHeld funs)
  tl.selfTest hp.nU
  tl.coefficients
  tl.rkSelfTest
  doorH (← LinkM.sub (form tl.equationsLaidF))
  let F ← LinkM.fork
  mustAs (ofGroup g "internal-f-draws") (F.nClaim == F.planClaimsF)
  LinkM.sub SubM.allTaken
  LinkM.must tl.foldAllTakenF
  pure wo

/-! ## The names of the refusals -/

/-- The names of the check's tests that the C++ verifier prints after the group's number. -/
def groupNames : List String :=
  ["internal-g-forest", "internal-g-merged-point", "internal-stack", "internal-claim-count",
   "internal-slot-count", "internal-g-rows-booked", "internal-g-calls-booked",
   "internal-g-free-slot", "internal-g-claim-count", "internal-f-draws"]

/-- The names under which this file's own tests fail. Three belong to tests on values, by Blk.check
(coin-zero, internal-g-merged-point, internal-g-free-slot). The others belong to tests on public
numbers, by mustAs. A failure of form has no name of its own. There are at most 28 groups, so g is
at most 27. The list also has 28, which no run reaches. -/
def checkNames : List String :=
  ["coin-zero", "internal-g-link", "forest-depth-G", "plan-tensor-layout", "internal-W-length",
   "internal-forest-join"] ++
  (List.range 29).flatMap fun g => groupNames.map (ofGroup g)

/-- All names that the layer sub-proofs' layout, plans and checks write at their own tests. The
parts that they call (lookup, smallness test, merge) list their names themselves. -/
def names : List String := layoutNames ++ planNames ++ checkNames

end OnBytes.Model.Layer
