-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Honest/K3/SixAtHead.lean: the kind "lookup" (K3): under the library's one hypothesis at
the full size (`P5J.AtMgA`, "the head") at the first of the goals' two named sets of public files
(`VerifierAndGoals.storedPublicFiles`), the library's six statements on what the two lookups of a link ask of the public
data (`SixAt`, Johnson/AtFull/K3X/SixAt.lean) hold at each of the 25 links, at the head's own public
part. One theorem: three calls; no definition; nothing is evaluated here.

Called. `six_zFull` (Johnson/AtFull/K3X/ReadsAtFull.lean); its premise on the layout file's size:
`lay_size` (AtFullSide/Layout/Size.lean); its premise on the maker's return: the head's own field
pubOne, through `publicOfO_older` (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean). `P5J.At.X Zp`
(Johnson/P5J/LettersAt.lean) is Zp.p.X by its definition.

Hypotheses that remain. `h`: the head at `VerifierAndGoals.storedPublicFiles`: at every member.
AtFullSide/Top/HeadMemberAtFull.lean has a member.

Why here. `lay_size` lies in this side library.


Limits, after those of the files called, which all hold here. At `VerifierAndGoals.storedPublicFiles` alone: at the second
named set (`VerifierAndGoals.zGap`) the library's statement at the output head's link has a premise that fails
there (the head of Johnson/AtFull/K3X/HeadSegment.lean says so): nothing is shown there. `SixAt`
compares with written values: the verifier does not ask it.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.AtFull.K3X.ReadsAtFull
import AtFullSide.Layout.Size
import Johnson.P5J.MgAtAll
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Honest.K3

/-- **Under the head at the first named set of public files the six statements hold at each of the
25 links, at the head's own public part.** -/
theorem six_head_zFull {D r Zp Np cF x}
    (h : P5J.AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x) :
    ∀ i, i < 25 → Johnson.AtFull.K3X.SixAt Zp.p.X i :=
  Johnson.AtFull.K3X.six_zFull Johnson.Unfolds.Layout.lay_size
    (by rw [VerifiableInference.PlanWritten.publicOfO_older]; exact h.toAtMg.pubOne)

end AtFullSide.Honest.K3

#print axioms AtFullSide.Honest.K3.six_head_zFull
