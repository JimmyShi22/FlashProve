-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PlanTail.lean: THE TIES OF THE CHAIN OF A LAYERS' SUB-PROOF's OWN ROUNDS TO THE
PLANNER, AT THE RECORD OF SIZES THAT THE PROGRAM's OWN FUNCTION MAKES
(`Verify.layerNumbers P hp g`, OnBytes/Model/VerifySubproofs.lean) and at the value of
Johnson/Road/K4/Value.lean, for a sub-proof that is not the first. Four
short theorems. The last three are each one theorem from elsewhere with `DimIs` paid by
`dimIs_layerNumbers` (Johnson/Road/K4/PlanSizes.lean).

  `full_layerNumbers`: where K4's text covers the public record, the program's record of sizes has
    terms, routed experts and both joins (`Full`, OnBytes/Tie/Pv/Lay/OwnPlan.lean). A proof of its
    own, off the text's test.
  `Plan4.tailIs_plan`: the numbers of the stages of the value's chain from the limbs' scalars on
    are that record's (`tailIs_at`, OnBytes/Desc/First/P1/OwnMapsAt.lean, which wraps `tailIs` of
    OnBytes/Tie/Pv/Lay/OwnSizes.lean). The token point in front is not among them.
  `Plan4.shape_plan`: the chain's rounds are the rounds of the planner's list at that record
    (`own_shape`, OnBytes/Tie/Pv/Lay/At/Sizes.lean: it counts what a round sends and draws).
  `Plan4.counts_plan`: the chain's bounds on bad draws, round by round, are the numerators of the
    plan's pairs at that record; at a drawn point: the count with the same quotient
    (`own_counts`, same file; the pairs' denominator c is free).

Premises of the last three: those of `dimIs_layerNumbers` at the value's sizes Q.D; the value's
number of rounds of the merge is the committed matrix's layout's (Q.kW = P.wsLay.lk); the group is
not the first.

Limits. Those of the called theorems: numbers of stages, of scalars and of draws, and counts; no
names, kinds, work or rows. The value's other letters are tied to no plan (Value.lean's limits).
That the planner's list at this record is the list of a made plan is not said here.
-/
import Johnson.Road.K4.PlanSizes
import Johnson.Road.K4.Value
import OnBytes.Desc.First.P1.OwnMapsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Shape Pub HPlan2 layout readsOf lamSOf nclOf)
open OnBytes.Tie.Pv.Lay (TailIs Full CountIs ownList ownRatios)
open OnBytes.G4 (ShapeIs)
open Inst.Model (Scl)
open OnBytes.Desc.First.K4 (covers)

/-- Where K4's text covers the public record, the program's record of sizes is full. -/
theorem full_layerNumbers {P : Pub} (hp : HPlan2) (g : ℕ) (hc : covers P = true) :
    Full (Verify.layerNumbers P hp g) := by
  unfold covers at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨-, p3⟩, c3⟩, c4⟩, c5⟩ := hc
  exact ⟨c5, p3, c4, of_decide_eq_true c3⟩

variable [scl : Scl] {M X : Type} (Q : Plan4 Cb.Gl.E M X) {hS : Shape} {pc : List (List String)}
  {P : Pub} {hp : HPlan2} {g : ℕ}

/-- **The value's chain, from the limbs' scalars on, has the numbers of the program's own record of
sizes**, under the premises of `dimIs_layerNumbers`, Q.kW = P.wsLay.lk, in a group that is not the
first. -/
theorem Plan4.tailIs_plan (hy : layout hS pc = .ok P.y) (hc : covers P = true)
    (hrd : readsOf P.y = .ok P.rd) (Z : Sized hS Q.D) (hl : hp.lamS = lamSOf P.y)
    (hn : hp.NCL = nclOf P.y g) (wk : Q.kW = P.wsLay.lk) (hg : (g == 0) = false) :
    TailIs Q.full.own.toOwn.tail (Verify.layerNumbers P hp g) :=
  OnBytes.Desc.First.P1.tailIs_at Q.full (Verify.layerNumbers P hp g)
    (dimIs_layerNumbers hy hc hrd Z hl hn) wk hg

/-- **Its rounds are the rounds of the planner's list at that record**, under the same premises. -/
theorem Plan4.shape_plan (hy : layout hS pc = .ok P.y) (hc : covers P = true)
    (hrd : readsOf P.y = .ok P.rd) (Z : Sized hS Q.D) (hl : hp.lamS = lamSOf P.y)
    (hn : hp.NCL = nclOf P.y g) (wk : Q.kW = P.wsLay.lk) (hg : (g == 0) = false) (w : ℕ)
    (Ex : Iop.ExtSpec) :
    ShapeIs Cb.Gl.E (Q.full.own.toOwn.ch.R Ex).shape (ownList w (Verify.layerNumbers P hp g)) :=
  OnBytes.Tie.Pv.Lay.At.own_shape Q.full (Verify.layerNumbers P hp g) (full_layerNumbers hp g hc)
    (dimIs_layerNumbers hy hc hrd Z hl hn) wk hg w Ex

/-- **Its bounds on bad draws are the numerators of the plan's pairs at that record** (at a drawn
point: the count with the same quotient), under the same premises. -/
theorem Plan4.counts_plan (hy : layout hS pc = .ok P.y) (hc : covers P = true)
    (hrd : readsOf P.y = .ok P.rd) (Z : Sized hS Q.D) (hl : hp.lamS = lamSOf P.y)
    (hn : hp.NCL = nclOf P.y g) (wk : Q.kW = P.wsLay.lk) (hg : (g == 0) = false) (c : ℕ)
    (Ex : Iop.ExtSpec) :
    List.Forall₂ (CountIs (Fintype.card Cb.Gl.E))
      (TWhole.errList (Q.full.own.toOwn.ch.eps Ex)) (ownRatios c (Verify.layerNumbers P hp g)) :=
  OnBytes.Tie.Pv.Lay.At.own_counts Q.full (Verify.layerNumbers P hp g) (full_layerNumbers hp g hc)
    (dimIs_layerNumbers hy hc hrd Z hl hn) wk hg c Ex

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.full_layerNumbers
#print axioms OnBytes.Road.K4.Plan4.tailIs_plan
#print axioms OnBytes.Road.K4.Plan4.shape_plan
#print axioms OnBytes.Road.K4.Plan4.counts_plan
