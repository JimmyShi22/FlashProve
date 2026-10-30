-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/JointMeetsBServed.lean

Theorems alone; no definition. It states no
goal.

Where the served requests ("AtPublicFiles.AtFiles.ServedRequest", E2E/CompleteAsIOPAtFiles.lean) sit against the
object's relation ("AtPublicFiles.Committed.RyesZ", E2E/TiedAtFiles.lean), typed at the matrices of the full
size's shape ("AtPublicFiles.AtFiles.FullSizeMatrix") and at the typed requests ("LPFD.Full.XF").

Main theorems:
* "servedRequest_below": in scope, at files that are read: a served request is in the object's relation.
* "servedRequest_member": there some request is served (so it is in the relation too).
* "relation_member_of_scope": in scope the object's relation has a member.

Limits.
* All three are calls: "servedRequest_isTrue" and "servedRequest_met"
  (E2E/CompleteAsIOPServedLaws.lean), "below_yesAt" (Johnson/FrontRoad/FromDebts.lean),
  "read_of_scope" (Johnson/Goal/Skeleton/SoundOfVerifyGoals.lean).
* The member's weights are made up ("Meaning.served_met"): nothing is said of a real model's weights.
* That some public files are in scope, or pass the verifier's test on them, is not said here.
* No prover is named. Nothing on completeness, soundness, hiding or any other property of the protocol.
-/
import E2E.CompleteAsIOPServedLaws
import Johnson.FrontRoad.FromDebts
import Johnson.Goal.Skeleton.SoundOfVerifyGoals

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.JointMeets

open AtPublicFiles.AtFiles (FullSizeMatrix ServedRequest)
open AtPublicFiles.Committed (RyesZ)
open FlashProve (committerCoinCountLessOne)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}

/-- **The served requests lie in the object's relation**, typed at the matrices and at the typed
requests of the full size: the premise "hY" of "servesAt_at_plug" at Yes := the served requests. By
"servedRequest_isTrue" (E2E/CompleteAsIOPServedLaws.lean) and "below_yesAt"
(Johnson/FrontRoad/FromDebts.lean). -/
theorem servedRequest_below (scope : VerifierAndGoals.InScope Z = true) (hr : VerifierAndGoals.readFiles Z = .ok pp) :
    ∀ (M : FullSizeMatrix) (x : LPFD.Full.XF), ServedRequest committerCoinCountLessOne Z hr M x → RyesZ Z M x :=
  fun M x h => OnBytes.FrontRoad.below_yesAt committerCoinCountLessOne Z hr M x
    (AtPublicFiles.AtFiles.servedRequest_isTrue committerCoinCountLessOne Z scope hr h)

/-- **In scope some request is served, and it is in the object's relation**: neither set is empty.
The weights are made up ("Meaning.served_met"). By "servedRequest_met". -/
theorem servedRequest_member (scope : VerifierAndGoals.InScope Z = true) (hr : VerifierAndGoals.readFiles Z = .ok pp) :
    ∃ (M : FullSizeMatrix) (x : LPFD.Full.XF), ServedRequest committerCoinCountLessOne Z hr M x ∧ RyesZ Z M x := by
  obtain ⟨M, x, h⟩ := AtPublicFiles.AtFiles.servedRequest_met committerCoinCountLessOne Z scope hr
  exact ⟨M, x, h, servedRequest_below scope hr M x h⟩

/-- **In scope the object's relation has a member.** The reading is "read_of_scope"'s. -/
theorem relation_member_of_scope (scope : VerifierAndGoals.InScope Z = true) :
    ∃ (M : FullSizeMatrix) (x : LPFD.Full.XF), RyesZ Z M x := by
  obtain ⟨pp, hr⟩ := VerifierAndGoals.AtTheName.read_of_scope Z scope
  obtain ⟨M, x, -, h⟩ := servedRequest_member scope hr
  exact ⟨M, x, h⟩

end OnBytes.HonestTrace.JointMeets

#print axioms OnBytes.HonestTrace.JointMeets.servedRequest_below
#print axioms OnBytes.HonestTrace.JointMeets.servedRequest_member
#print axioms OnBytes.HonestTrace.JointMeets.relation_member_of_scope
