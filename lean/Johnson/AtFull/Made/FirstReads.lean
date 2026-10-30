-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/FirstReads.lean: what the planner's routine for a proof file's first chain
(`Params.firstPlan`, OnBytes/Params/DeriveReq.lean) reads of the sub-proofs. General laws: no
written value, no evaluation. A law file; no running text imports it.

Of its argument `sub : Subproofs` the routine reads `openRows`, `pendingRows`, `afterLinks`, and
`plan` at the numbers of the request's links alone. It reads neither `links` nor `matrixRows`.

Definitions.
  `bodyOf z sub`: the routine that `firstPlan` finishes: its own text.
Statements.
  `firstPlan_body`: firstPlan z sub = finishHeld z.set .request (bodyOf z sub).
  `runs_bodyOf`: `Plan.runs_firstRounds` (OnBytes/Plan/PlanListsReq.lean) at that name.
  `reqMoments_congr`, `reqPlanFrom_congr`, `bodyOf_congr`, `firstPlan_congr`: two values of `sub`
    that agree in what is read give the same routine and the same plan.

Limits. Nothing says that a routine returns. Nothing on soundness.
-/
import OnBytes.Plan.PlanListsReq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params

/-- The routine that `firstPlan` finishes. -/
def bodyOf (z : ProofSized) (sub : Subproofs) : Planning Unit := do
  reqPlan z sub
  sub.afterLinks
  modify fun p => { p with scope := .request }
  if 1 < sub.pendingRows then planBatt sub.pendingRows z.batch.shape.kCol
  linPlanFirst z.codes z.batch
  planSeal

theorem firstPlan_body (z : ProofSized) (sub : Subproofs) :
    firstPlan z sub = finishHeld z.set .request (bodyOf z sub) := rfl

/-- It adds the rounds of the first chain's list. -/
theorem runs_bodyOf {z : ProofSized} {sub : Subproofs} {L : Nat → Nat → List RoundSpec}
    {after : List RoundSpec} (S : Plan.SubRuns z.set sub L after) :
    Runs z.set .request 0 0 0 (bodyOf z sub) () (Plan.firstChainList z sub L after) 0 0 0 :=
  Plan.runs_firstRounds S

theorem reqMoments_congr {z : ProofSized} {sub sub' : Subproofs} {l : Nat}
    (h : ∀ m, sub.plan l m = sub'.plan l m) (msgs : List ReqMessage) : ∀ fuel moment : Nat,
      Params.reqMoments z sub l msgs fuel moment = Params.reqMoments z sub' l msgs fuel moment
  | 0, _ => by
    unfold Params.reqMoments
    rfl
  | fuel + 1, moment => by
    unfold Params.reqMoments
    simp only [h, reqMoments_congr h msgs fuel (moment + 1)]

theorem reqPlanFrom_congr {z : ProofSized} {sub sub' : Subproofs} {n : Nat}
    (h : ∀ l, l < n → ∀ m, sub.plan l m = sub'.plan l m) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat)
      (before : GroupSize), l + links.length ≤ n →
      reqPlanFrom z sub l gs links open_ before = reqPlanFrom z sub' l gs links open_ before
  | [], _, _, _, _, _ => by
    unfold reqPlanFrom
    rfl
  | g :: gs, l, [], open_, before, _ => by
    unfold reqPlanFrom
    rfl
  | g :: gs, l, k :: ks, open_, before, hl => by
    have hl' : l < n := by
      simp only [List.length_cons] at hl
      omega
    have ih := reqPlanFrom_congr (z := z) h gs (l + 1) ks (open_.drop 1)
    have hk : l + 1 + ks.length ≤ n := by
      simp only [List.length_cons] at hl
      omega
    have hd : (k :: ks).drop 1 = ks := rfl
    unfold reqPlanFrom
    simp only [List.head?_cons, hd, h l hl', reqMoments_congr (h l hl'), fun b => ih b hk]

/-- **Two values of `sub` that agree in what is read give the same routine.** -/
theorem bodyOf_congr {z : ProofSized} {sub sub' : Subproofs} {n : Nat}
    (hn : z.request.link.length ≤ n) (h1 : ∀ l, l < n → ∀ m, sub.plan l m = sub'.plan l m)
    (h2 : sub.openRows = sub'.openRows) (h3 : sub.pendingRows = sub'.pendingRows)
    (h4 : sub.afterLinks = sub'.afterLinks) : bodyOf z sub = bodyOf z sub' := by
  unfold bodyOf reqPlan
  rw [reqPlanFrom_congr h1 _ 0 _ _ _ (by omega), h2, h3, h4]

/-- The same of the plan. -/
theorem firstPlan_congr {z : ProofSized} {sub sub' : Subproofs} {n : Nat}
    (hn : z.request.link.length ≤ n) (h1 : ∀ l, l < n → ∀ m, sub.plan l m = sub'.plan l m)
    (h2 : sub.openRows = sub'.openRows) (h3 : sub.pendingRows = sub'.pendingRows)
    (h4 : sub.afterLinks = sub'.afterLinks) : firstPlan z sub = firstPlan z sub' := by
  rw [firstPlan_body, firstPlan_body, bodyOf_congr hn h1 h2 h3 h4]

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.firstPlan_body
#print axioms Johnson.AtFull.Made.runs_bodyOf
#print axioms Johnson.AtFull.Made.reqPlanFrom_congr
#print axioms Johnson.AtFull.Made.bodyOf_congr
#print axioms Johnson.AtFull.Made.firstPlan_congr
