-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K11RoundsScope.lean: THE CORE OF THE SECOND ROW OF THE MERGE's LOT
(Johnson/AtFull/Desc/Lots/K11Rounds.lean) WITH ITS THREE HYPOTHESES BY FIELD PAID IN THE GOALS'
SCOPE. Two theorems: calls.

What it says.
  `work_scope`: for public files in the goals' scope (hS, hR), where the plain road's public part Z
    is made at our second, non-standard hash (built on BLAKE2b's compression function) (hZ) and the
    blank segments' structures G₀ are made (hG): the setting of G₀'s public parameters asks no proof
    of work in front of a field's challenge in a request's own rounds.
  `k11_rounds_scope`: there every block of the lot sits at the place ⟨1, some 24, 9, .K11⟩ and its
    rounds are `listAt "H:9"`.
  PAID: hb (25 segments are built): `IM.ground_gets` (Johnson/IMR/PureJoin.lean) · hk (the committed
    table has 18 column bits): `m0lk_in_scope`
    (Johnson/Desc/Sound/K11Tests/NumsHeadInScope.lean) · hw (no proof of work there):
    `Meaning.HeadS.frame_in_scope` (Johnson/Goal/Meaning/HeadShapeScope.lean: in scope the security
    lines are the stored example's) and `work_ref` (Johnson/Goal/Meaning/HeadCondScope.lean: at
    these the number is 0, by the kernel): all at `IM.ground_publicK`: the structures' public
    parameters are `publicOf`'s.

Limits. hS, hR, hZ AND hG STAY PREMISES: that any public files meet them together is shown nowhere
here. May be idle: no example of the head is shown in this file; two, at storedPublicFiles and at zGap alone,
are AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what they are worth.
No law at an opening and none under the
proof file's pins is spent. At `OnBytes.secondHashFunction` alone. The limits of K11Rounds.lean hold here too.
Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K11Rounds
import Johnson.IMR.PureJoin
import Johnson.Desc.Sound.K11Tests.NumsHeadInScope
import Johnson.Goal.Meaning.HeadCondScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K11Rounds

open Johnson.AtFull.Rounds (listAt)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **In the goals' scope the setting asks no proof of work in front of a field's challenge in a
request's own rounds.** -/
theorem work_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    (OnBytes.Params.settingOf G₀.W.P.frame).workOf .field .request = 0 := by
  rw [Meaning.HeadS.frame_in_scope hS hR (IM.ground_publicK hZ hG)]
  exact VerifiableInference.Desc.Kinds.Head.Law.InScope.work_ref

/-- **THE CORE OF THE ROW, with its three hypotheses paid in the goals' scope.** -/
theorem k11_rounds_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    ∀ b ∈ (K11.lot Z).blocks G₀, b.place = placeW ∧ b.rounds = listAt "H:9" :=
  k11_rounds_at (IM.ground_gets hS hR hZ hG).1
    (LT28.K11Tests.m0lk_in_scope hS (IM.ground_publicK hZ hG)).2 (work_scope hS hR hZ hG)

end Johnson.AtFull.Lots.K11Rounds

#print axioms Johnson.AtFull.Lots.K11Rounds.work_scope
#print axioms Johnson.AtFull.Lots.K11Rounds.k11_rounds_scope
