-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/FitSubAtt.lean: the planning of an attention sub-proof's rounds keeps a property
of single entries, if the planner's basic routines keep it and the record's numbers are within their
caps.

The calculus, the record SubBase of what is asked of the planner's basic routines, and the caps on
the records' numbers: OnBytes/Params/Fit/FitCalc.lean and FitSub.lean.

Main theorems, each under SubBase s Q: keeps_scores, keeps_attentionOwn (under AttentionCap),
keeps_attentionRounds (under AttentionCap and SmallCap).

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

theorem keeps_scores (l : List (Nat × Nat)) :
    Keeps s Q (forEach l fun x => do
      planScalars 7
      planPsc (attentionSc3 x.1 x.2)) :=
  keeps_forEach _ fun _ _ => keeps_bind (keeps_scalars _) fun _ _ => B.psc _

theorem keeps_attentionOwn {x : AttentionRounds} (hc : AttentionCap x) :
    Keeps s Q (planAttentionOwn x) := by
  unfold planAttentionOwn
  refine keeps_skip (keeps_scalars _) ?_
  refine keeps_bind (m1 := 0) (R := fun _ => True) (keeps_scores B _) fun _ _ => ?_
  repeat' first
    | exact B.psc _
    | exact B.batSigma _
    | exact keeps_scalars _
    | exact B.zero _ hc.zero
    | refine keeps_bind (m1 := 0) (R := fun _ => True) ?_ fun _ _ => ?_

attribute [local irreducible] planAttentionOwn

theorem keeps_attentionRounds (look : ForestSize) {x : AttentionRounds} (hc : AttentionCap x)
    {small : SmallSize} (hs : SmallCap small) (moment : Nat) :
    Keeps s Q (attentionRounds look x small moment) := by
  unfold attentionRounds
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
    | exact keeps_attentionOwn B hc
    | exact keeps_small B hs _
    | refine keeps_forEach _ fun _ _ => ?_
    | refine keeps_skip ?_ ?_
    | refine keeps_skip2 ?_ ?_ ?_
    | refine keeps_ite (fun _ => ?_) fun _ => ?_

end

end OnBytes.Params
