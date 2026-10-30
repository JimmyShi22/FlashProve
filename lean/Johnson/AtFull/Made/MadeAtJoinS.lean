-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/MadeAtJoinS.lean: the proof file's sizes at the join's shapes.

What it says. `proofSized_join`: at a public part as at the full size, `proofSized` at the written
lines and the sub-proofs of the join's shapes (`(xOf X sh rc).sub`, which is
`subproofsWith X reqLinksW` by its definition) returns the written sizes `proofSizedFull`. One
premise: `PubFull X`.
`layout_join`: the layout of the join's shapes is the written one, by its definition.

Where the facts used lie, under Johnson/AtFull/Made/ but for the last. proofSized_returns:
ProofSizedReturns.lean · links_of_frame: ShapesReturn.lean · reqFrame_of_pub: ReqFrameOfPub.lean ·
ws_parts: BuiltAtFull.lean · the small joining steps: Seams.lean · groups_are:
Johnson/AtFull/LayoutRead/GroupsAre.lean.

Limits. A joining. That any public files have such a public part is shown nowhere here. Nothing on
soundness.
-/
import Johnson.AtFull.Made.MadeAtJoinA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages OnBytes.Params
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (layoutFull)
open Johnson.AtFull.LayoutRead (LW)
open H2K.Sizes (PubFull)

/-- **The proof file's sizes at the join's shapes are the written ones.** -/
theorem proofSized_join {X : Public} (P : PubFull X) (sh : Plan.Shape) (rc : List RangeCheck) :
    proofSized recordLines (xOf X sh rc).sub = some proofSizedFull := by
  have b₂ : Plan.reqFrame declaredFull LW X.P.frame.answers = some (reqLinksW, layoutFull) :=
    reqFrame_of_pub P moments_seam rfl
  rw [P.frame] at b₂
  obtain ⟨e1, e2⟩ := links_of_frame
    (show Plan.reqFrame declaredFull LW 1 = some (reqLinksW, layoutFull) from b₂) declared_size
    Johnson.AtFull.LayoutRead.groups_are
  refine proofSized_returns e1 ?_ ?_ (ws_parts P.wsLay).2.2.1
  · show List.replicate reqLinksW.length 1 = List.replicate 25 1
    rw [e2]
  · show X.NGr + 1 = 13
    rw [P.groups]

/-- The layout of the join's shapes. -/
theorem layout_join (X : Public) (sh : Plan.Shape) (rc : List RangeCheck) :
    (xOf X sh rc).layout = layoutFull := rfl

#print axioms Johnson.AtFull.Made.proofSized_join
#print axioms Johnson.AtFull.Made.layout_join

end Johnson.AtFull.Made
