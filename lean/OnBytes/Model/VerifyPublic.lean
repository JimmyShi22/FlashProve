-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyPublic.lean: all that a stage of a call computes from the configuration files
before it looks at a key, an entry, a request or a proof.

Every stage of the C++ verifier begins in the same way (verifier/src/cp_verify.cpp, runStage, from
its start to the call of buildLinksH). It scans the parameter file, tests the scales, compares the
public tables with their digests, lays out the committed matrix of weights, and makes the layout and
the plan of every sub-proof. Then it compares the plans with one another. This file puts these steps
in the order of the C++ source. Nearly every step is a function defined in another file. What this
file adds is the filling of each step's record of public numbers from the parameter file as read,
and three small steps (`planesHeld`, `callsDigest`, `ownerOf`).

A function here returns its result or the name of the first test that failed. The names are those of
the C++ verifier, without the name of a lookup call that it appends to some. Some guards of this
program on itself have names of their own or borrow a C++ name; all of these begin with internal-.

Main definitions: `layerShape`, `headShape`, `weightShape`, `Digests`, `Public`, `publicOf`.
What is not claimed: no theorem is stated here. The C++ verifier computes four public tables in
floating point. Here they are computed in whole numbers (OnBytes/Model/LayerTables.lean,
OnBytes/Model/AttentionExp.lean). It is not shown that both give the same tables at all allowed
parameters. Each table is compared with its digest in the parameter file, if the file has these
lines.
-/
import OnBytes.Model.VerifyHeads
import OnBytes.Model.VerifyCross
import OnBytes.Model.AttentionConfig
import OnBytes.Model.LayerPlan
import OnBytes.Model.HeadPlan

namespace OnBytes.Model.Verify

/-! ## The records of public numbers -/

/-- The numbers of the parameter file on which a layer sub-proof depends. -/
def layerShape (P : PolScan) : Layer.Shape :=
  let h := P.h
  { prof := h.prof, lt := h.lt, L := h.L, ll := h.ll, d := h.d, H := h.H, Gk := h.Gk, dh := h.dh,
    f := h.f, fe := h.fe, NE := h.NE, eps1 := h.eps.getD 0 0, eps2 := h.eps.getD 1 0,
    epsF := h.epsF, cs := h.cs, theta0 := h.theta0, hq := P.value "hq", hv := P.value "hv",
    ho := P.value "ho", hgD := P.value "hgD", huD := P.value "huD", hdD := P.value "hdD",
    hr := P.value "hr", ut := h.ut, la := h.la, nmin := h.nmin, D := h.D, tau := h.tau,
    lmaf := h.lmaf, NAf := h.NAf, lmad := h.lmad, NAd := h.NAd, lmar := h.lmar, lmb := h.lmb,
    lmq := h.lmq, lmx := h.lmx, wb := h.wb, iota := h.iota, seed := h.seed, gcl := P.gcl,
    rcl := P.rcl, xl := P.XL, lidb := P.settings.lidb, eg := P.EG, smax := P.SMAX }

/-- The numbers on which the head's sub-proof depends. lPd comes from the layers' layout. -/
def headShape (P : PolScan) (y : Layer.Lay) : Head.Shape :=
  let h := P.h
  { lt := h.lt, la := h.la, d := h.d, lPd := y.lPd, V := h.V, MF := h.MF, KF := h.KF,
    epsF := h.epsF, toksrc := h.toksrc, clipC := h.clipC, theta := h.theta, cap := h.cap,
    logS := h.logS, digSh := h.digSh, tabS := h.tabS, famF := h.famF, lmhf := h.lmhf,
    NHf := h.NHf, lmhd := h.lmhd, lmhr := h.lmhr, lmbH := h.lmbH, wbEmb := h.wbH.getD 0 0,
    wbHead := h.wbH.getD 1 0, iotaH := h.iotaH.toList, nmin := h.nmin,
    NMINH := P.settings.nminH, LIDB := P.settings.lidb, XL := P.XL, polCallsH := P.polCallsH }

/-- The numbers on which the layout of the committed matrix of weights depends. -/
def weightShape (P : PolScan) (y : Layer.Lay) : WsShape :=
  let h := P.h
  { D := h.D, L := h.L, d := h.d, dh := h.dh, dkv := y.dkv, dq := y.dq, f := h.f, fe := h.fe,
    NE := h.NE, V := h.V }

/-- What the head needs to know, from the layers' layout, about a matrix that holds the residual
stream. -/
def borderOf (y : Layer.Lay) : Head.Border :=
  { mxb := y.mxb, kxb := y.kxb, off := y.xb.off, nl := y.xb.nl, cnt := y.xb.cnt, J := y.xb.J }

/-- What the head's plan reads of the plan of the last group of layers. Refuses if there is no
group. The layout has refused a model without layers before, so no file can cause this refusal. -/
def ownerOf (y : Layer.Lay) (G : Array Layer.HPlan2) : Except String Head.Owner :=
  match G.back? with
  | some O => pure { tl := O.tl, Fp := O.Fp, Tp := O.Tp, iXO := (Layer.matIx y).iXO }
  | none => throw "internal-h-owner-TX"

/-! ## The whole public part -/

/-- The digest of a layout's list of lookup calls, written out as the lines of the parameter file.
word: the first word of such a line. -/
def callsDigest (word : String) (calls : List CallD) : ByteArray :=
  secondHashFunction 73 (OnBytes.textWords (callText word calls).toUTF8)

/-- The digests of the lists of lookup calls that the sub-proofs use. They are words of the
statement. That of attention is empty below profile 4. -/
structure Digests where
  /-- of the calls of a layer sub-proof -/
  hCalls : ByteArray
  /-- of the calls of an attention sub-proof -/
  hCallsA : ByteArray
  /-- of the calls of the head's sub-proof -/
  hCallsH : ByteArray

/-- All that follows from the configuration files: the parameter file as read, and the layout and
the plan of every sub-proof. -/
structure Public where
  /-- the parameter file as read -/
  P : PolScan
  /-- the digests of the call lists that the sub-proofs use -/
  digests : Digests
  /-- what the layer sub-proofs read, with the layout, the scales, the tables and the layout of the
  committed matrix of weights. It holds no token yet -/
  layers : Layer.Pub
  /-- the numbers of the head's sub-proof -/
  hS : Head.Shape
  /-- the layout of the head's sub-proof -/
  HLy : Head.HL
  /-- the plans of the layer sub-proofs, one for each group of layers -/
  G : Array Layer.HPlan2
  /-- the plans of the attention sub-proofs: one for each group, or none below profile 4 -/
  A : Array Attention.Plan
  /-- the plan of the head's sub-proof -/
  H : Head.HPlanH2
  /-- what the head reads of the last group's plan -/
  owner : Head.Owner

namespace Public

/-- The layout of the layer sub-proofs. -/
def y (X : Public) : Layer.Lay := X.layers.y

/-- True at profile 4, where the proof covers attention. -/
def p4 (X : Public) : Bool := X.y.h.p4

/-- The number of groups of layers. -/
def NGr (X : Public) : Nat := X.y.NGr

/-- The number of tokens of a request. -/
def T (X : Public) : Nat := X.y.T

end Public

/-- Tests that every call of the layers' lookup has multiplicities of 32 bits. The C++ verifier
appends the call's name to the refusal's. That name comes from the parameter file and is left out
here. -/
def planesHeld (cl : Array Call) : Except String Unit :=
  refuseIf (cl.any fun c => c.kappa != 5) "hid-planes"

/-- The scan of the parameter file and the layout of a layer sub-proof, with the tests made just
before and after that layout. C++: polPrescan, the two tests on the line lt in runStage,
polSkeleton, polScan (here all in `polScan`), then polLayout. -/
def polLayout (pol : ByteArray) : Except String (PolScan × Layer.Lay) := do
  let P ← polScan pol
  polBeforeLayout P
  let y ← Layer.layout (layerShape P) P.polCalls
  polBehindLayout P
  planesHeld y.cl
  polTablesAdmitted P
  pure (P, y)

/-- The public part of a stage, in the order of runStage. pol, KL, layout: the three configuration
files. -/
def publicOf (pol KL : ByteArray) (layout : Option ByteArray) : Except String Public := do
  let (P, y) ← polLayout pol
  let h := y.h
  -- the scales
  let sc ← Layer.scalesOf h (fileWords KL)
  Layer.scalesHeld h sc
  -- the tables of the gate and of the sigmoid
  tableHeld P .silu y.silu
  if h.p3 then tableHeld P .sigmoid y.fs
  Layer.noWrap h sc y.dq
  let _ ← hPar pol KL layout
  -- the widths of the weights, and the committed matrix
  Layer.weightWidthsHeld h y.kinds
  let hS := headShape P y
  Head.vocabulary hS
  let wsLay ← wsLayOf (weightShape P y) h.p3 P.lkW
  -- the rotary table
  let rope ← Layer.ropeOf h
  tableHeld P .rope rope
  -- the layouts of the head and of attention
  let tails := Layer.tailsOf y
  let HLy ← Head.layout hS y.tauFC
  let iQA := (Layer.matIx y).iQA
  let (A0, hCallsA) ←
    if h.p4 then do
      let c ← Attention.config P y sc fun g => ((tails.getD g {}).mats.getD iQA {}).aId
      pure (c.plans, c.hCallsA)
    else pure (#[], ByteArray.empty)
  -- the plans
  let layers ← Layer.Pub.of y sc rope wsLay P.h.V #[] P.settings
  let G ← Layer.plansG layers
  let seenG := G.map fun O => (⟨O.tl, O.Fp, O.Tp⟩ : SubPlan)
  let seenA ← attentionOwners h.p4 y.NGr seenG
    (A0.map fun X => ⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩)
  let A := A0.zipWith (fun X s => { X with seam := { X.seam with tl := s.tl } }) seenA
  let owner ← ownerOf y G
  let H ← Head.planH2 P.settings hS HLy (borderOf y) owner y.NGr P.lkW
  -- The C++ counts its comparisons of records as it makes them: one for each group but the first,
  -- for each attention and for the head. Here the count is computed from the numbers of plans, so
  -- crossPlans' first test shows only that the owners' and the readers' records are that many.
  crossPlans (G.size - 1 + A.size + 1) y.NGr h.p4 tails seenG seenA ⟨H.tl, H.Fp, H.Tp⟩
  let digests : Digests :=
    { hCalls := callsDigest "call" y.calls.toList, hCallsA := hCallsA,
      hCallsH := callsDigest "callH" HLy.calls.toList }
  pure { P := P, digests := digests, layers := layers, hS := hS, HLy := HLy, G := G, A := A,
         H := { H with Fp := H.Fp.trimL }, owner := owner }

/-- The names with which this file itself refuses. -/
def namesPublic : List String := ["hid-planes", "internal-h-owner-TX"]

end OnBytes.Model.Verify
