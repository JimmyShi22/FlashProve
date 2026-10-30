-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifySubproofs.lean: what the plan of a proof's first chain takes from the model's
sub-proofs.

A request's proof file holds three chains (OnBytes/Params/Chains.lean), and each sub-proof is one
link of the first. The plan of that chain lists every round with a bound on its error. The frame of
the chain is planned from the parameter file's first lines (OnBytes/Params/DeriveReq.lean). The
rounds of a sub-proof are planned from a few numbers of that sub-proof
(OnBytes/Params/SubRounds.lean). This file takes these numbers from the plans of the sub-proofs, and
puts them together for the frame.

It follows the part of the C++ verifier that fills blk::LayerRounds and sets the field rounds of a
layer sub-proof's plan (verifier/src/vf_layers_plan.inc), and the lines of buildLinksH
(verifier/src/vf_segments.inc) that fill the record subH. The rounds of attention are taken from
OnBytes/Model/AttentionRounds.lean, the head's from OnBytes/Model/HeadRounds.lean, and the sizes of
a lookup and of a smallness test from OnBytes/Model/RoundSizes.lean. The range checks are made in
OnBytes/Model/VerifyHiding.lean.

Main definitions: layerNumbers, linkRounds, withReply, subproofsWith, rangeChecksOf, shapesWith.

What this file does not do: it reads no layout file. The links with their oracle messages and the
layout are arguments. It reads no proof. No theorem is stated here.
-/
import OnBytes.Model.VerifyPublic
import OnBytes.Model.HeadRounds
import OnBytes.Model.AttentionRounds
import OnBytes.Model.RoundSizes
import OnBytes.Model.VerifyHiding
import OnBytes.Params.SubRounds
import OnBytes.Params.Configure
import OnBytes.Plan.FromLayout

namespace OnBytes.Model.Verify

/-- The numbers from which the rounds of the layer sub-proof of group g are planned, apart from
those of its lookup and of its smallness test. P: what all layer sub-proofs read; hp: the plan of
this one. C++: the record x in verifier/src/vf_layers_plan.inc. -/
def layerNumbers (P : Layer.Pub) (hp : Layer.HPlan2) (g : Nat) : Params.LayerRounds :=
  let y := P.y
  { lt := y.h.lt, ls := y.ls, lNI := P.rd.lNI, lPd := y.lPd, ll := y.h.ll, lPf := y.lPf,
    lfe := y.lfe, lamS := hp.lamS, lkW := P.wsLay.lk, NI := y.NI
    NS := ledNS y.h.xl, NP := ledNP y.h.xl, NO := ledNO y.h.xl
    withTerms := !P.rd.tscCalls.isEmpty
    shownByTheTerms := Layer.shownByTerms y P.rd
    neverSent := 1 + (if y.h.p3 then y.LamM else 0)
    weightClaims := hp.NCL - (if g == 0 then 1 else 0)
    firstGroup := g == 0
    routed := y.h.p3 }

/-- The rounds of a link's sub-proof that follow the sending of the oracle messages of one moment
(OnBytes/Params/SubRounds.lean). The links are numbered in the chain's order: for each group g of
layers G_g, directly followed by A_g if the proof covers attention; last the head. For a number that
names no link the plan is refused as "parameters-not-admitted" (Params.notAdmitted).
C++: the field rounds of each of the three kinds of plan, as buildLinksH calls it. -/
def linkRounds (X : Public) (link moment : Nat) : Params.Planning Unit :=
  let step := if X.p4 then 2 else 1
  let g := link / step
  if link == step * X.NGr then
    X.H.rounds X.hS X.HLy moment
  else if link % step == 0 then
    match X.G[g]? with
    | some hp =>
      Params.layerRounds (forestSize X.y.fo) (layerNumbers X.layers hp g) (smallSize hp.tl)
        hp.nBatched moment
    | none => Params.needs false
  else
    match X.A[g]? with
    | some a => Attention.rounds a moment
    | none => Params.needs false

/-- The links with one plain scalar before the last link's first message: the reply's token. -/
def withReply : List Params.ReqLink → List Params.ReqLink
  | [] => []
  | [l] => [{ l with plain := 1 }]
  | l :: ls => l :: withReply ls

/-- What the frame asks of the model's sub-proofs. links: the links with their oracle messages, as
they follow from the arrays that the sub-proofs declare and from the layout file. Each sub-proof
ends in one equation. Each group of layers and the head leave one row on the weight table (the
committed matrix of weights), whose number of rows is the layout's. C++: the lines of buildLinksH
that fill subH. -/
def subproofsWith (X : Public) (links : List Params.ReqLink) : Params.Subproofs :=
  { links := withReply links
    openRows := List.replicate links.length 1
    plan := linkRounds X
    pendingRows := X.NGr + 1
    matrixRows := X.layers.wsLay.m0 }

/-- The closing parts (the states of the smallness tests, OnBytes/Model/Tail.lean) of the sub-proofs
of group g: that of the layers, then that of attention if the proof covers attention. Nothing if a
plan is missing. -/
def closingPartsOf (X : Public) (g : Nat) : Option (List HTailF2) :=
  match X.G[g]?, X.A[g]? with
  | some hp, some a => some (if X.p4 then [hp.tl, a.seam.tl] else [hp.tl])
  | some hp, none => if X.p4 then none else some [hp.tl]
  | none, _ => none

/-- The closing parts of the sub-proofs in the chain's order: see linkRounds. Nothing if a plan is
missing. -/
def closingParts (X : Public) : Option (List HTailF2) :=
  ((List.range X.NGr).mapM (closingPartsOf X)).map fun l => l.flatten ++ [X.H.tl]

/-- A request's range checks, for the conditions of hiding, in the chain's order. Nothing if a plan
is missing. -/
def rangeChecksOf (X : Public) : Option (List Params.RangeCheck) :=
  (closingParts X).map rangeChecksH

/-- What the verifier's own plans hand to the derivation of all sizes and plans
(OnBytes/Params/Configure.lean). links, layout: the links with their oracle messages, and where each
array lies in them. identifiers: the sub-proofs' public identifiers in the chain's order. What the
key's proof of the ranges looks up follows from the layout of the weight table.
Refused as "plan-link": a number of links that differs from the model's number of sub-proofs, or a
missing plan. Refused as "internal-weight-limbs": a unit of that layout other than the embedding has
four digits (of such a unit a key's range proof covers nothing beyond its bytes), or the units are
not in order. C++: the record made at the end of buildLinksH, verifier/src/vf_segments.inc. -/
def shapesWith (X : Public) (links : List Params.ReqLink) (layout : Params.ReqLayout)
    (identifiers : List Nat) : Except String Params.Shapes := do
  let lay := X.layers.wsLay
  let rangeChecks ← Params.orRefuse (rangeChecksOf X) "plan-link"
  if links.length != (if X.p4 then 2 else 1) * X.NGr + 1 then throw "plan-link"
  if lay.U.any fun u => u.nlw == 4 && u.X != 12 then throw "internal-weight-limbs"
  let ranges ← Params.orRefuse (Plan.shapeOfLayout lay lay.lk) "internal-weight-limbs"
  pure
    { sub := subproofsWith X links, layout := layout, identifiers := identifiers, ranges := ranges,
      rangeChecks := rangeChecks }

/-- The names under which shapesWith refuses. linkRounds refuses under Params.notAdmitted, which is
in the planner's list (OnBytes/Params/RefusalNames.lean). -/
def Subproofs.names : List String := ["plan-link", "internal-weight-limbs"]

end OnBytes.Model.Verify
