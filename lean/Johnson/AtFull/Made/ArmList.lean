-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ArmList.lean: the rounds of a link's arm as a plain list, and the sub-proofs at
the 26 written arms. A law file; no running text imports it.

An arm (`Arm`, Johnson/Desc/First/Link/RowsRun.lean) holds the numbers that the planner's routine
for a link's sub-proof reads of the public data. `AtFull.Rows.armRounds`
(Johnson/AtFull/Rows/ArmRounds.lean) is that routine over an arm.

Definitions.
  `armList s c a moment`: the list of the arm's rounds after a moment: `headList`, `layerList` or
    `attentionList` (OnBytes/Params/PlanListsSub.lean); empty where there is no arm.
  `subW`: a value of `Subproofs`: the routine of the written arms (`armAtW`,
    Johnson/LPFE1R/RowsAtWritten.lean), 25 times one open row, 13 pending rows. It has no links and
    no matrix rows: `firstPlan` reads neither (Johnson/AtFull/Made/FirstReads.lean). Of the 26
    written arms the last is `.none`: at 25 links it is never asked.
  `listW`: the lists of the written arms under a request's own scope.
Statements.
  `runs_armRounds`: the routine of an arm adds the rounds of the arm's list.
  `subRuns_subW`: so `subW` is as `Plan.SubRuns` asks (OnBytes/Plan/PlanListsReq.lean).
  `firstPlan_at_arms`: where `shapesWith` returns x at X and `armsB X` says yes, and the sizes z
    have at most 26 links: firstPlan z x.sub = firstPlan z subW.

Limits. Of a routine that refuses `Runs` says nothing; where there is no arm the routine refuses.
That `armsB` says yes at any public files is shown nowhere here. Nothing says that a routine
returns. Nothing on soundness.
-/
import Johnson.AtFull.Rows.ArmRounds
import Johnson.AtFull.Made.ArmsGive
import Johnson.AtFull.Made.FirstReads
import OnBytes.Model.LinkRoundsList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params OnBytes.Model.Verify
open VerifiableInference.Desc.LinkJoin (Arm armOf armAtW armsB arm_at)
open AtFull.Rows (armRounds plan_at_arms)

/-- The rounds of an arm after a moment, as a list. -/
def armList (s : Setting) (c : Scope) : Arm → Nat → List RoundSpec
  | .head l x sm, moment => headList s c l x sm moment
  | .layer l x sm k, moment => layerList s c l x sm k moment
  | .attention l x sm, moment => attentionList s c l x sm moment
  | .none, _ => []

/-- **The routine of an arm adds the rounds of the arm's list.** -/
theorem runs_armRounds {s : Setting} {c : Scope} (a : Arm) (moment : Nat) :
    Runs s c 0 0 0 (armRounds a moment) () (armList s c a moment) 0 0 0 := by
  cases a with
  | head l x sm => exact runs_headRounds _ _ _ _
  | layer l x sm k => exact runs_layerRounds _ _ _ _ _
  | attention l x sm => exact runs_attentionRounds _ _ _ _
  | none => exact runs_needs _ _ 0 0 0

/-- The sub-proofs at the written arms. -/
def subW : Subproofs where
  links := []
  openRows := List.replicate 25 1
  plan := fun l moment => armRounds (armAtW l) moment
  pendingRows := 13
  matrixRows := 0

/-- The lists of the written arms. -/
def listW (s : Setting) (l moment : Nat) : List RoundSpec := armList s .request (armAtW l) moment

theorem subRuns_subW (s : Setting) : Plan.SubRuns s subW (listW s) [] :=
  ⟨fun l m => runs_armRounds (armAtW l) m, runs_pure () 0 0 0⟩

/-- **At the model's sub-proofs, where the 26 arms are the written ones.** -/
theorem firstPlan_at_arms {z : ProofSized} (hz : z.request.link.length ≤ 26) {X : Public}
    {links : List ReqLink} {layout : ReqLayout} {identifiers : List Nat} {x : Shapes}
    (hx : shapesWith X links layout identifiers = .ok x) (ha : armsB X = true) :
    firstPlan z x.sub = firstPlan z subW := by
  obtain ⟨h4, hN⟩ := arms_give ha
  have hl : links.length = 25 := by
    unfold shapesWith at hx
    extract_lets at hx
    obtain ⟨rc, _, hx⟩ := exc_bind hx
    by_contra hn
    have hb : (links.length != (if X.p4 then 2 else 1) * X.NGr + 1) = true := by
      rw [h4, hN]
      simpa using hn
    rw [if_pos hb] at hx
    cases hx
  rw [shapesWith_sub hx]
  refine firstPlan_congr hz (fun l h m => plan_at_arms ha links l h m) ?_ ?_ rfl
  · show List.replicate links.length 1 = List.replicate 25 1
    rw [hl]
  · show X.NGr + 1 = 13
    rw [hN]

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.runs_armRounds
#print axioms Johnson.AtFull.Made.subRuns_subW
#print axioms Johnson.AtFull.Made.firstPlan_at_arms
