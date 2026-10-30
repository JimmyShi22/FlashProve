-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/FrameMore.lean: the routines from which the plan of a proof file's first chain
is made read no round that the plan already holds. It goes on where Johnson/AtFull/Rows/FrameP.lean
ends (`FrP`, its closure, the tactic `frp`): the lookup, the proximity test, the sub-proofs'
routines, the routine of an arm, the frame's sending and moments. Theorems by unfolding. A law file;
no running text imports it.

Statements. `frP_‹routine›` for: planLkp, times, planLookup, planStages, planIopp, planForest,
planSmall, planLayerOwn, layerRounds, planAttentionOwn, attentionRounds, planHeadOwn, planHeadEnd,
headRounds, armRounds, linPlanFirst, reqSend, reqMoments.

The tactic. Below most statements one line adds the statement to the tactic's steps (`macro_rules`
for `frp_step`, as in FrameP.lean): fourteen such lines. They extend a tactic and state nothing. The
tactic `frp` with these steps is called in the proofs of this file's own `frP_…` statements and of
those of Johnson/AtFull/Made/FirstCut.lean. Every file that imports this one inherits these steps.
They write proof terms that Lean's kernel checks like any other.

Limits. `FrP` is a conditional on returns: of a routine that refuses nothing is said. Nothing on
what a round means. Nothing on soundness.
-/
import Johnson.AtFull.Rows.FrameP
import Johnson.AtFull.Rows.ArmRounds
import OnBytes.Params.DeriveReq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params

theorem frP_planLkp (k : Nat) : FrP (planLkp k) := by
  unfold planLkp
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planLkp _)

theorem frP_times {x : Planning Unit} (h : FrP x) : ∀ n : Nat, FrP (times n x)
  | 0 => by
    unfold times
    frp
  | n + 1 => by
    have := frP_times h n
    unfold times
    frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible apply frP_times)
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible apply frP_forEach)

theorem frP_planLookup (x : LookupSize) : FrP (planLookup x) := by
  unfold planLookup
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planLookup _)

theorem frP_planStages (f : Nat) (m : Bool) :
    ∀ (first : Bool) (st : List StageSize), FrP (planStages f m first st)
  | first, x :: y :: rest => by
    have := frP_planStages f m false (y :: rest)
    unfold planStages
    frp
  | _, [x] => by
    unfold planStages
    frp
  | _, [] => by
    unfold planStages
    frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planStages _ _ _ _)

theorem frP_planIopp (st : List StageSize) (rows f : Nat) (m : Bool) :
    FrP (planIopp st rows f m) := by
  unfold planIopp
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planIopp _ _ _ _)

theorem frP_planForest (x : ForestSize) : FrP (planForest x) := frP_planLookup _
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planForest _)

theorem frP_planSmall (x : SmallSize) (which : Nat) : FrP (planSmall x which) := by
  unfold planSmall
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planSmall _ _)

theorem frP_planLayerOwn (x : LayerRounds) : FrP (planLayerOwn x) := by
  unfold planLayerOwn
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planLayerOwn _)

theorem frP_layerRounds (look : ForestSize) (x : LayerRounds) (small : SmallSize)
    (claims moment : Nat) : FrP (layerRounds look x small claims moment) := by
  unfold layerRounds
  frp

theorem frP_planAttentionOwn (x : AttentionRounds) : FrP (planAttentionOwn x) := by
  unfold planAttentionOwn
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planAttentionOwn _)

theorem frP_attentionRounds (look : ForestSize) (x : AttentionRounds) (small : SmallSize)
    (moment : Nat) : FrP (attentionRounds look x small moment) := by
  unfold attentionRounds
  frp

theorem frP_planHeadOwn (x : HeadRounds) : FrP (planHeadOwn x) := by
  unfold planHeadOwn
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planHeadOwn _)

theorem frP_planHeadEnd (x : HeadRounds) : FrP (planHeadEnd x) := by
  unfold planHeadEnd
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_planHeadEnd _)

theorem frP_headRounds (look : ForestSize) (x : HeadRounds) (small : SmallSize) (moment : Nat) :
    FrP (headRounds look x small moment) := by
  unfold headRounds
  frp

/-- **The routine of an arm reads no round.** -/
theorem frP_armRounds (a : Arm) (moment : Nat) : FrP (AtFull.Rows.armRounds a moment) := by
  cases a with
  | head l x s => exact frP_headRounds _ _ _ _
  | layer l x s c => exact frP_layerRounds _ _ _ _ _
  | attention l x s => exact frP_attentionRounds _ _ _ _
  | none => exact frP_needs _ _

theorem frP_linPlanFirst (codes : Codes) (x : LinSized) : FrP (linPlanFirst codes x) := by
  unfold linPlanFirst
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_linPlanFirst _ _)

theorem frP_reqSend (codes : Codes) (sent : List OracleNotice) (group atStart : GroupSize)
    (riders : Nat) (ownRound : Bool) : FrP (reqSend codes sent group atStart riders ownRound) := by
  unfold reqSend
  frp
macro_rules | `(tactic| frp_step) => `(tactic| with_reducible exact frP_reqSend _ _ _ _ _ _)

theorem frP_reqMoments (z : ProofSized) {sub : Subproofs} {l : Nat}
    (h : ∀ m, FrP (sub.plan l m)) (msgs : List ReqMessage) :
    ∀ fuel moment : Nat, FrP (Params.reqMoments z sub l msgs fuel moment)
  | 0, _ => by
    unfold Params.reqMoments
    frp
  | fuel + 1, moment => by
    have := frP_reqMoments z h msgs fuel (moment + 1)
    have := h moment
    unfold Params.reqMoments
    frp

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.frP_planLkp
#print axioms VerifiableInference.Desc.LinkJoin.frP_times
#print axioms VerifiableInference.Desc.LinkJoin.frP_planLookup
#print axioms VerifiableInference.Desc.LinkJoin.frP_planStages
#print axioms VerifiableInference.Desc.LinkJoin.frP_planIopp
#print axioms VerifiableInference.Desc.LinkJoin.frP_planForest
#print axioms VerifiableInference.Desc.LinkJoin.frP_planSmall
#print axioms VerifiableInference.Desc.LinkJoin.frP_planLayerOwn
#print axioms VerifiableInference.Desc.LinkJoin.frP_layerRounds
#print axioms VerifiableInference.Desc.LinkJoin.frP_planAttentionOwn
#print axioms VerifiableInference.Desc.LinkJoin.frP_attentionRounds
#print axioms VerifiableInference.Desc.LinkJoin.frP_planHeadOwn
#print axioms VerifiableInference.Desc.LinkJoin.frP_planHeadEnd
#print axioms VerifiableInference.Desc.LinkJoin.frP_headRounds
#print axioms VerifiableInference.Desc.LinkJoin.frP_armRounds
#print axioms VerifiableInference.Desc.LinkJoin.frP_linPlanFirst
#print axioms VerifiableInference.Desc.LinkJoin.frP_reqSend
#print axioms VerifiableInference.Desc.LinkJoin.frP_reqMoments
