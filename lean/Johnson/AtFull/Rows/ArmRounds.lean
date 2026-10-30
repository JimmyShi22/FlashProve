-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/ArmRounds.lean: OF A PUBLIC PART X THE PLANNER's ROUTINE FOR A LINK
(`Model.Verify.linkRounds`, OnBytes/Model/VerifySubproofs.lean) READS THE LINK's ARM ALONE (`armOf`,
Johnson/Desc/First/Link/RowsRun.lean). One definition, two theorems by unfolding. A law file; no
running text imports it. Nothing on codes.

Why. `subproofsWith X links` hands `linkRounds X` to the planner as a routine: a closure over the
whole public part. Whatever the planner asks of that routine is so a question on X. Here it becomes
a question on 26 small structures of numbers.

  `armRounds a moment`: the routine of an arm. `linkRounds_arm`: linkRounds X link moment =
    armRounds (armOf X link) moment, at every X. The like for the noted routine is `nLink_arm`
    (Johnson/Desc/First/Link/Law/RowsFrom.lean), whose proof this one follows step for step.
  `plan_at_arms`: armsB X = true ⊢ (subproofsWith X rl).plan j moment = armRounds (armAtW j) moment,
    at j below 26: A CLOSED TERM.

Limits. armsB is a premise: shown at no files (Johnson/AtFull/Rows/ArmsOfFields.lean cuts it into
small equations). SECOND TEXT: `armRounds` repeats `linkRounds`' three branches; `linkRounds_arm`
ties it. Nothing on soundness.

-/
import Johnson.AtFull.Rows.ArmsOfFields
import OnBytes.Model.VerifySubproofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Rows
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Model.Verify (Public linkRounds subproofsWith)
open VerifiableInference.Desc.LinkJoin

/-- The planner's routine of an arm: the three branches of `linkRounds`, and its refusal. -/
def armRounds : Arm → Nat → Planning Unit
  | .head l x s, moment => headRounds l x s moment
  | .layer l x s c, moment => layerRounds l x s c moment
  | .attention l x s, moment => attentionRounds l x s moment
  | .none, _ => needs false

/-- **Of the public part the rounds of a link's sub-proof read the arm alone.** -/
theorem linkRounds_arm (X : Public) (link moment : Nat) :
    linkRounds X link moment = armRounds (armOf X link) moment := by
  unfold linkRounds armOf
  dsimp only
  generalize (if X.p4 = true then 2 else 1) = step
  by_cases h1 : (link == step * X.NGr) = true
  · rw [if_pos h1, if_pos h1]
    rfl
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : (link % step == 0) = true
    · rw [if_pos h2, if_pos h2]
      cases X.G[link / step]? <;> rfl
    · rw [if_neg h2, if_neg h2]
      cases X.A[link / step]? <;> rfl

/-- **Where the 26 arms are the written ones, the routine that `subproofsWith` hands to the planner
is a closed term at each link.** -/
theorem plan_at_arms {X : Public} (ha : armsB X = true) (rl : List ReqLink) (j : Nat)
    (hj : j < 26) (moment : Nat) :
    (subproofsWith X rl).plan j moment = armRounds (armAtW j) moment := by
  show linkRounds X j moment = _
  rw [linkRounds_arm, arm_at ha j hj]

end AtFull.Rows

#print axioms AtFull.Rows.linkRounds_arm
#print axioms AtFull.Rows.plan_at_arms
