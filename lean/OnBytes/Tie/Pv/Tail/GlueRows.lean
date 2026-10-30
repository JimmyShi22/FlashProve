-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/GlueRows.lean: open steps on the plans with which the verifier runs: that their
numbers are those with which the planner is called; each typed as a closed statement.

Definitions alone: nothing is proved here and nothing is assumed. Whoever proves a step states a
theorem of that very type in a file of its own.

`head_meets`, `att_meets` and `lay_meets` (OnBytes/Tie/Pv/Head/HeadMeets.lean,
OnBytes/Tie/Pv/Tail/EndMeetAtt.lean, EndMeetLay.lean) lay a link's run against the planner's rounds.
Each takes a record of equations as a premise (`HeadGlue`, `AttGlue`, `LayGlue`). The statements
here are those fields of the three records that speak of a plan alone, at the plans that
`Verify.publicOf` (OnBytes/Model/VerifyPublic.lean) returns: X.G[g], X.A[g], X.H. The other fields
(the link's record, number and group in the frame) speak of the chain's state.

At hand: `Fo.Pub.publicOf_cut`, `public_G`, `public_H` (OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean),
`public_A` (FoPublicA.lean): a run of publicOf that returns, in X's own fields; the members of X.G,
X.A and X.H from the planning routines.

Main names:
  `LookIs calls lid fs`: the shape that the lookup's routine makes of the calls has the three sizes
    of fs that the planner takes.
  `row_glue_look_G`, `row_glue_look_A`, `row_glue_look_H`: the lookup on the calls.
  `row_glue_digits_G`, `row_glue_digits_A`, `row_glue_digits_H`: the lookup on the digits, at the
    plan's record.
  `row_glue_plan_A`: a member of X.A has the shape and the own rounds' numbers of a plan that
    Attention.plan has made.
  `row_glue_lam_H`, `row_glue_merge_H`: two numbers of the head's plan.
  `row_glue_mu_G`: the numbers of variables of the layers' three product layers.

Limits: statements alone; whether they hold is not shown in this file.


-/
import OnBytes.Model.RoundSizes
import OnBytes.Model.VerifyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.GlueRows
open OnBytes OnBytes.Model

/-- The shape that the lookup's routine makes of the calls (Forest.pad begins with Forest.shape
calls lid) has the three sizes of fs that the planner takes (forestSize: v, d, and whether there is
more than one call). -/
def LookIs (calls : Array Call) (lid : Nat) (fs : Forest.Shape) : Prop :=
  ∃ h0, (Forest.shape calls lid).toOption = some h0 ∧ forestSize h0 = forestSize fs

/-! ## The lookup on the calls -/

/-- (U1) The layers. Text: OnBytes/Model/LayerLayout.lean (Layer.layout: the fields cl, fo, h.lidb),
VerifyPublic.lean (polLayout; Layer.Pub.of keeps y: Fo.Pub.pubOf_y). -/
def row_glue_look_G : Prop :=
  ∀ (pol KL : ByteArray) (layout : Option ByteArray) (X : Verify.Public),
    Verify.publicOf pol KL layout = .ok X →
    LookIs X.layers.y.cl X.layers.y.h.lidb X.layers.y.fo

/-- (U2) Attention. Text: OnBytes/Model/AttentionPlan.lean (plan: (S, fs) ← shapeHid settings.lidb
cf; Plan.lid), AttentionShape.lean (shapeHid). From public_A: S, fs and settings are those of the
plan that Attention.plan returned. -/
def row_glue_look_A : Prop :=
  ∀ (pol KL : ByteArray) (layout : Option ByteArray) (X : Verify.Public),
    Verify.publicOf pol KL layout = .ok X → ∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a →
    LookIs (a.S.calls.map (·.call)) a.lid a.fs

/-- (U3) The head. Text: OnBytes/Model/HeadLayout.lean (Head.layout: the fields cl, fs),
VerifyPublic.lean (HLy ← Head.layout hS y.tauFC). Head.layout makes the shape of a first list of
calls and then sets each call's field iota from that shape: the field cl is the second list. -/
def row_glue_look_H : Prop :=
  ∀ (pol KL : ByteArray) (layout : Option ByteArray) (X : Verify.Public),
    Verify.publicOf pol KL layout = .ok X → LookIs X.HLy.cl X.hS.LIDB X.HLy.fs

/-! ## The lookup on the digits -/

/-- (U4) The layers. Text: OnBytes/Model/Tail.lean (shapeF and what it calls make z1, z2, f9 and
lidb of a record; addTreesF, and the routines that write the lists plOwn and plFor, leave them). -/
def row_glue_digits_G : Prop :=
  ∀ (pol KL : ByteArray) (layout : Option ByteArray) (X : Verify.Public),
    Verify.publicOf pol KL layout = .ok X → ∀ (g : Nat) (hp : Layer.HPlan2), X.G[g]? = some hp →
    LookIs #[hp.tl.z1.call, hp.tl.z2.call] hp.tl.lidb hp.tl.f9

/-- (U5) Attention. The record of a member of X.A is not the one that Attention.plan returned:
attentionOwners has filled one record of its list plFor. -/
def row_glue_digits_A : Prop :=
  ∀ (pol KL : ByteArray) (layout : Option ByteArray) (X : Verify.Public),
    Verify.publicOf pol KL layout = .ok X → ∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a →
    LookIs #[a.seam.tl.z1.call, a.seam.tl.z2.call] a.seam.tl.lidb a.seam.tl.f9

/-- (U6) The head. -/
def row_glue_digits_H : Prop :=
  ∀ (pol KL : ByteArray) (layout : Option ByteArray) (X : Verify.Public),
    Verify.publicOf pol KL layout = .ok X →
    LookIs #[X.H.tl.z1.call, X.H.tl.z2.call] X.H.tl.lidb X.H.tl.f9

/-! ## Single numbers -/

/-- (U7) A member of X.A has the shape and the own rounds' numbers of a plan that Attention.plan has
made. From public_A. -/
def row_glue_plan_A : Prop :=
  ∀ (pol KL : ByteArray) (layout : Option ByteArray) (X : Verify.Public),
    Verify.publicOf pol KL layout = .ok X → ∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a →
    ∃ settings i cf P0, Attention.plan settings i cf = .ok P0 ∧ a.S = P0.S ∧ a.own = P0.own

/-- (U8) The number of rounds over the channels in the head's last sumcheck. Text:
OnBytes/Model/HeadPlan.lean (planH2: lamS := h.lPd). From public_H. -/
def row_glue_lam_H : Prop :=
  ∀ (pol KL : ByteArray) (layout : Option ByteArray) (X : Verify.Public),
    Verify.publicOf pol KL layout = .ok X → X.H.lamS = X.hS.lPd

/-- (U9) The number of rounds of the merge. Text: VerifyPublic.lean (wsLay ← wsLayOf … P.lkW;
Layer.Pub.of … wsLay …; planH2 … P.lkW), OnBytes/Model/Weights.lean (wsLayOf, WsLay.build),
LayerPlan.lean (Pub.of), HeadPlan.lean (planH2: lkW := lkW). -/
def row_glue_merge_H : Prop :=
  ∀ (pol KL : ByteArray) (layout : Option ByteArray) (X : Verify.Public),
    Verify.publicOf pol KL layout = .ok X → X.layers.wsLay.lk = X.H.lkW

/-- (U10) The numbers of variables of the layers' three product layers. Text:
OnBytes/Model/LayerLayout.lean:719-721, and Layer.Pub.of, which makes the field rd. -/
def row_glue_mu_G : Prop :=
  ∀ (pol KL : ByteArray) (layout : Option ByteArray) (X : Verify.Public),
    Verify.publicOf pol KL layout = .ok X →
    X.layers.rd.muV = X.layers.rd.lNI + X.layers.y.lPd + X.layers.y.h.lt ∧
      X.layers.rd.muH = X.layers.y.h.ll + X.layers.y.lPf + X.layers.y.h.lt ∧
      X.layers.rd.muH2 = X.layers.y.h.ll - 1 + X.layers.y.lfe + X.layers.y.h.lt

end OnBytes.Tie.Pv.Tail.GlueRows
