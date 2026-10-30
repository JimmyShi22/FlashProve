-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/FitSubLayer.lean: the planning of a layer sub-proof's rounds keeps a property of
single entries, if the planner's basic routines keep it and the record's numbers are within their
caps.

The calculus, the record SubBase of what is asked of the planner's basic routines, and the caps on
the records' numbers: OnBytes/Params/Fit/FitCalc.lean and FitSub.lean.

Main theorems, each under SubBase s Q: keeps_layerOwn (under LayerCap), keeps_layerRounds
(under LayerCap and SmallCap).

Limits. Those of OnBytes/Params/Fit/FitSub.lean. The program does not import this file.


-/
import OnBytes.Params.Fit.FitSub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

-- In the walks below no routine that has its own law is looked into.
attribute [local irreducible] planPsc planLookup planZero planJoin planLine planBatSigma planRng
  planScalars theSetting theScope needs forEach
  planForest planSmall planProductLayer planTokenSumcheck planTokenSum

section
variable {s : Setting} {Q : Fmt.Entry → Prop} (B : SubBase s Q)
include B

theorem keeps_layerOwn {x : LayerRounds} (hc : LayerCap x) : Keeps s Q (planLayerOwn x) := by
  unfold planLayerOwn
  try dsimp only
  repeat' first
    | exact B.psc _
    | exact B.lookup _
    | exact B.line
    | exact B.batSigma _
    | exact keeps_scalars _
    | exact keeps_pure trivial
    | exact keeps_setting.any
    | exact keeps_scope
    | exact (keeps_needs _ _).any
    | exact B.zero _ hc.lt
    | exact B.zero _ hc.lsLt
    | exact B.zero _ hc.lPd
    | exact B.join _ hc.lNI
    | exact B.join _ hc.ll
    | exact keeps_productLayer B _
    | exact keeps_tokenSumcheck B _ _ _
    | refine keeps_forEach _ fun _ _ => ?_
    | refine keeps_skip ?_ ?_
    | refine keeps_skip2 ?_ ?_ ?_
    | refine keeps_ite (fun _ => ?_) fun _ => ?_
    | refine keeps_bind (m1 := 0) (R := fun _ => True) ?_ fun _ _ => ?_

attribute [local irreducible] planLayerOwn

theorem keeps_layerRounds (look : ForestSize) {x : LayerRounds} (hc : LayerCap x)
    {small : SmallSize} (hs : SmallCap small) (claims moment : Nat) :
    Keeps s Q (layerRounds look x small claims moment) := by
  unfold layerRounds
  try dsimp only
  repeat' first
    | exact B.psc _
    | exact B.lookup _
    | exact B.line
    | exact B.batSigma _
    | exact keeps_scalars _
    | exact keeps_pure trivial
    | exact keeps_setting.any
    | exact keeps_scope
    | exact (keeps_needs _ _).any
    | exact keeps_forest B _
    | exact keeps_layerOwn B hc
    | exact keeps_small B hs _
    | refine keeps_forEach _ fun _ _ => ?_
    | refine keeps_skip ?_ ?_
    | refine keeps_skip2 ?_ ?_ ?_
    | refine keeps_ite (fun _ => ?_) fun _ => ?_
    | refine keeps_bind (m1 := 0) (R := fun _ => True) ?_ fun _ _ => ?_

end

end OnBytes.Params
