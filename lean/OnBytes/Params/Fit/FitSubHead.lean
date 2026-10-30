-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/FitSubHead.lean: the planning of the head sub-proof's rounds keeps a property of
single entries, if the planner's basic routines keep it and the record's numbers are within their
caps.

The calculus, the record SubBase of what is asked of the planner's basic routines, and the caps on
the records' numbers: OnBytes/Params/Fit/FitCalc.lean and FitSub.lean.

Main theorems, each under SubBase s Q: keeps_headOwn (under HeadCap), keeps_headEnd,
keeps_headRounds (under HeadCap and SmallCap).

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

theorem keeps_headOwn {x : HeadRounds} (hc : HeadCap x) : Keeps s Q (planHeadOwn x) := by
  unfold planHeadOwn
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
    | exact keeps_tokenSum B _ _ _ _
    | refine keeps_forEach _ fun _ _ => ?_
    | refine keeps_skip ?_ ?_
    | refine keeps_skip2 ?_ ?_ ?_
    | refine keeps_ite (fun _ => ?_) fun _ => ?_
    | refine keeps_bind (m1 := 0) (R := fun _ => True) ?_ fun _ _ => ?_

theorem keeps_headEnd (x : HeadRounds) : Keeps s Q (planHeadEnd x) := by
  unfold planHeadEnd
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
    | refine keeps_forEach _ fun _ _ => ?_
    | refine keeps_skip ?_ ?_
    | refine keeps_skip2 ?_ ?_ ?_
    | refine keeps_ite (fun _ => ?_) fun _ => ?_
    | refine keeps_bind (m1 := 0) (R := fun _ => True) ?_ fun _ _ => ?_

attribute [local irreducible] planHeadOwn planHeadEnd

theorem keeps_headRounds (look : ForestSize) {x : HeadRounds} (hc : HeadCap x)
    {small : SmallSize} (hs : SmallCap small) (moment : Nat) :
    Keeps s Q (headRounds look x small moment) := by
  unfold headRounds
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
    | exact keeps_headOwn B hc
    | exact keeps_small B hs _
    | exact keeps_headEnd B _
    | refine keeps_forEach _ fun _ _ => ?_
    | refine keeps_skip ?_ ?_
    | refine keeps_skip2 ?_ ?_ ?_
    | refine keeps_ite (fun _ => ?_) fun _ => ?_

end

end OnBytes.Params
