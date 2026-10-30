-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/FitSub.lean: what the planner's routines for the rounds of the model's three
kinds of sub-proof ask of the planner's basic routines and of their records' numbers, so that they
keep a property of single entries; and the laws of the five helping routines.

OnBytes/Params/SubRounds.lean plans the own rounds of a group of layers, of its attention and of the
output head. Its routines write no round themselves: the rounds are written by seven routines of
OnBytes/Params/Planner.lean that they call (planPsc, planLookup, planZero, planJoin, planLine,
planBatSigma, planRng). They also call that file's planScalars, needs, theSetting, theScope and
forEach, which write none. OnBytes/Params/Fit/FitCalc.lean has the calculus. Keeps s Q x says:
wherever x ends well from a state with the setting s, no root open, all of whose entries have Q, the
new state is such a state again. So the laws here and in the three files named below also say that
the sub-proofs' routines leave no root open.

Main definitions.
  SubBase s Q: the seven basic routines keep Q at the setting s: planZero and planJoin at up to
    2 ^ 40 variables, planRng at columns with columns * 276 ≤ 2 ^ 45, the other four at every
    argument. The bounds are those at which OnBytes/Params/Fit/FitSmall.lean has the laws for its
    property Small.
  SmallCap, LayerCap, AttentionCap, HeadCap: what is asked of a record's numbers: the arguments of
    its calls of planZero, planJoin and planRng are within these bounds.
Main theorems. keeps_skip, keeps_skip2: a step, or two, that are taken or left out, with what
follows, in the form that Lean gives a routine's text.
Under SubBase s Q: keeps_forest, keeps_small (under SmallCap), keeps_productLayer,
keeps_tokenSumcheck, keeps_tokenSum.
The three kinds' own routines: OnBytes/Params/Fit/FitSubLayer.lean, FitSubAtt.lean, FitSubHead.lean.

Limits. Q and s are letters: that SubBase holds of any Q is not shown here. That the records which
the program fills meet the caps is not shown here. Of a routine that refuses nothing is said: so of
planSmall at which ≥ 2 or at another tau than the setting's, and of the three kinds' rounds at a
moment above 2. Nothing on the errors that a plan states. Nothing on soundness.
The program does not import this file.


-/
import OnBytes.Params.Fit.FitCalc
import OnBytes.Params.SubRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

/-- The seven basic routines that the sub-proofs' routines call keep Q at the setting s, three of
them under a bound on their argument. -/
structure SubBase (s : Setting) (Q : Fmt.Entry → Prop) : Prop where
  psc : ∀ x, Keeps s Q (planPsc x)
  lookup : ∀ x, Keeps s Q (planLookup x)
  zero : ∀ v, v ≤ 2 ^ 40 → Keeps s Q (planZero v)
  join : ∀ v, v ≤ 2 ^ 40 → Keeps s Q (planJoin v)
  line : Keeps s Q planLine
  batSigma : ∀ n, Keeps s Q (planBatSigma n)
  rng : ∀ c, c * 276 ≤ 2 ^ 45 → Keeps s Q (planRng c)

/-- What is asked of a smallness test's numbers. -/
structure SmallCap (x : SmallSize) : Prop where
  columns : x.columns * 276 ≤ 2 ^ 45

/-- What is asked of a layer sub-proof's numbers: the five arguments of planZero and planJoin. -/
structure LayerCap (x : LayerRounds) : Prop where
  lt : x.lt ≤ 2 ^ 40
  lsLt : x.ls + x.lt ≤ 2 ^ 40
  lPd : x.lPd - x.ls ≤ 2 ^ 40
  lNI : x.lNI ≤ 2 ^ 40
  ll : x.ll - 1 ≤ 2 ^ 40

/-- What is asked of an attention sub-proof's numbers: the one argument of planZero. -/
structure AttentionCap (x : AttentionRounds) : Prop where
  zero : 2 * x.lgk + 2 * x.lt + 4 ≤ 2 ^ 40

/-- What is asked of the head sub-proof's numbers: the one argument of planZero. -/
structure HeadCap (x : HeadRounds) : Prop where
  lt : x.lt ≤ 2 ^ 40

section
variable {s : Setting} {Q : Fmt.Entry → Prop}

/-- A step that is taken or left out, and what follows it in both cases, in the form that Lean gives
a routine's text: where the step is left out, "pure ()" is done first. -/
theorem keeps_skip {β : Type} {R : β → Prop} {c : Prop} [Decidable c] {a : Planning PUnit}
    {T : Planning β} (ha : Keeps s Q a) (hT : Keeps s Q T R) :
    Keeps s Q (if c then a >>= fun _ => T else pure PUnit.unit >>= fun _ => T) R :=
  keeps_ite (fun _ => keeps_bind ha fun _ _ => hT)
    fun _ => keeps_bind (R := fun _ => True) (keeps_pure trivial) fun _ _ => hT

/-- The same with two steps. -/
theorem keeps_skip2 {β : Type} {R : β → Prop} {c : Prop} [Decidable c] {a b : Planning PUnit}
    {T : Planning β} (ha : Keeps s Q a) (hb : Keeps s Q b) (hT : Keeps s Q T R) :
    Keeps s Q
      (if c then a >>= fun _ => b >>= fun _ => T else pure PUnit.unit >>= fun _ => T) R :=
  keeps_ite (fun _ => keeps_bind ha fun _ _ => keeps_bind hb fun _ _ => hT)
    fun _ => keeps_bind (R := fun _ => True) (keeps_pure trivial) fun _ _ => hT

end

-- In the walks below no routine that has its own law is looked into.
attribute [local irreducible] planPsc planLookup planZero planJoin planLine planBatSigma planRng
  planScalars theSetting theScope needs forEach

section
variable {s : Setting} {Q : Fmt.Entry → Prop} (B : SubBase s Q)
include B

theorem keeps_forest (x : ForestSize) : Keeps s Q (planForest x) := by
  unfold planForest
  exact B.lookup _

attribute [local irreducible] planForest

theorem keeps_small {x : SmallSize} (hc : SmallCap x) (which : Nat) :
    Keeps s Q (planSmall x which) := by
  unfold planSmall
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
    | exact B.rng _ hc.columns
    | exact keeps_forest B _
    | refine keeps_forEach _ fun _ _ => ?_
    | refine keeps_skip ?_ ?_
    | refine keeps_skip2 ?_ ?_ ?_
    | refine keeps_ite (fun _ => ?_) fun _ => ?_
    | refine keeps_bind (m1 := 0) (R := fun _ => True) ?_ fun _ _ => ?_

attribute [local irreducible] planSmall

theorem keeps_productLayer (n : Nat) : Keeps s Q (planProductLayer n) := by
  unfold planProductLayer
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

theorem keeps_tokenSumcheck (lt degreeY shown : Nat) :
    Keeps s Q (planTokenSumcheck lt degreeY shown) := by
  unfold planTokenSumcheck
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

theorem keeps_tokenSum (lt shown degreeInY more : Nat) :
    Keeps s Q (planTokenSum lt shown degreeInY more) := by
  unfold planTokenSum
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

end

end OnBytes.Params
