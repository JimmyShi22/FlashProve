-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyLinks.lean: the links of a request's chain, made from the sub-proofs' plans.

A sub-proof is one link of the first chain of a proof. The order of the links, their names and their
identifiers are set in OnBytes/Model/StagesLinks.lean (listLinksH). This file passes that routine
one record for each sub-proof: the plan, and the check that runs under that plan.

Main definitions: `layersPlanOf`, `attentionPlanOf`, `headPlanOf`, `linksOf`.
What is not claimed: no theorem is stated here.
-/
import OnBytes.Model.VerifyPublic
import OnBytes.Model.StagesLinks
import OnBytes.Model.Layer
import OnBytes.Model.Head
import OnBytes.Model.Attention

namespace OnBytes.Model.Verify

open OnBytes.Model.Stages

/-- What the plan of the layer sub-proof of group g gives to its link. tokv: the request's
tokens. -/
def layersPlanOf (X : Public) (tokv : Array Nat) (g : Nat) (hp : Layer.HPlan2) : SubPlanH :=
  { tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
    run := some <$> Layer.runForkHidG2 { X.layers with tokv := tokv } hp g }

/-- What the plan of an attention sub-proof gives to its link. It leaves no row on the weight
table. -/
def attentionPlanOf (A : Attention.Plan) : SubPlanH :=
  { tl := A.seam.tl, Fp := A.seam.Fp, Tp := A.seam.Tp, ns := A.ns,
    run := do
      Attention.run A
      pure none }

/-- What the plan of the head's sub-proof gives to its link. -/
def headPlanOf (X : Public) (cov : Head.Covered) : SubPlanH :=
  { tl := X.H.tl, Fp := X.H.Fp, Tp := X.H.Tp, ns := X.H.ns, NCL := X.H.NCL,
    run := some <$> Head.runForkHidH2 X.hS X.HLy (borderOf X.y) X.H X.owner cov X.layers.wsLay }

/-- The links of a request's chain, in the chain's order. cov: the request's tokens and covered
positions. Only the checks of the sub-proofs read it; no public number depends on it. Each link's
record of its plan and its check are made from one and the same plan of X. -/
def linksOf (X : Public) (cov : Head.Covered) : Except String (Array LinkH) :=
  listLinksH X.NGr X.p4 (X.G.mapIdx fun g hp => layersPlanOf X cov.tokv g hp)
    (X.A.map attentionPlanOf) (headPlanOf X cov)

end OnBytes.Model.Verify
