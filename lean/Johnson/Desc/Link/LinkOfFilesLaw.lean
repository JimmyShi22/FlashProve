-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/LinkOfFilesLaw.lean: whoever holds a Link3 out of the entry file's maker holds a
description that has passed its tests on the plan, and that is linkDesc at the planner's record and
declLOf's rounds (two readers' ask).
AN UNSEATED MAKER linkOfFiles (over the middle term linkDesc: Johnson/Desc/Link/LinkDescWithGroundSend.lean) lies
here: seated, run and walked nowhere; beside it stands linkOfFilesV
(LinkOfFiles.lean; VerifierAndGoals.theDescription runs neither: it runs linkDecisionAtParameterFile,
Johnson/Desc/Link/LinkWritten.lean), whose like law is
linkOfFilesV_ok (Johnson/Desc/Link/LinkVariantLaw.lean).
-/
import Johnson.Desc.Link.LinkOfFiles
import Johnson.Desc.Link.LinkDescWithGroundSend
import Johnson.Desc.Link.CoreSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes VerifiableInference.Desc

/-- The unseated maker: a middle term. -/
def linkOfFiles (pol lay KL : ByteArray) : Except String Link3 :=
  match OnBytes.Model.Verify.planned pol KL (some lay), Johnson.G.OfPlan.declLOf pol lay KL with
  | .error e, _ => .error e
  | _, .error e => .error e
  | .ok p, .ok plan =>
    let F := linkDesc p.chains plan
    match F.planWord, F.dsOf "entry file" with
    | some w, _ => .error s!"entry file: {w}"
    | _, .error e => .error e
    | none, .ok ds => .ok ⟨F, ds, F.xsTyped⟩

theorem linkOfFiles_ok (pol lay KL : ByteArray) (L : Link3) (h : linkOfFiles pol lay KL = .ok L) :
    ∃ p plan, OnBytes.Model.Verify.planned pol KL (some lay) = .ok p ∧ Johnson.G.OfPlan.declLOf pol
        lay KL = .ok plan ∧
      L.F = linkDesc p.chains plan ∧ L.F.planOk = true ∧ L.F.dsOf "entry file" = .ok L.ds ∧ L.xs =
          L.F.xsTyped := by
  unfold linkOfFiles at h
  split at h
  · cases h
  · cases h
  · rename_i p plan hp hplan
    dsimp only at h
    split at h
    · cases h
    · cases h
    · rename_i ds hw hds
      cases h
      exact ⟨p, plan, hp, hplan, rfl, OneChainFileDescription.planWord_none _ hw, hds, rfl⟩

end Desc.K15

#print axioms Desc.K15.linkOfFiles_ok
