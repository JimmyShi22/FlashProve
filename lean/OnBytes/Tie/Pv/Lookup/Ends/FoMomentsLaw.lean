-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoMomentsLaw.lean.
The test momentsB as a consequence: the frame's links of a run of shapesOf have three moments or
more each, where every link that the verifier lists has one of the vectors U1 to U4.

OnBytes/Tie/Pv/Lookup/Ends/FoSizedLink.lean has momentsB as a test that can be run.
OnBytes/Tie/Pv/Lookup/Ends/FoPlannedCut.lean cuts a run of shapesOf into a chain of five equations
(ShapesCut). This file joins OnBytes/Tie/Pv/Lookup/Ends/FoDeclMoments.lean (the chain's second
equation) and OnBytes/Tie/Pv/Lookup/Ends/FoFrameFolds.lean (its fourth); the first equation names
the links of which HasU speaks.

* HasU X: every link of linksOf X default has one of the vectors U1 to U4.
* shapesCut_moments: ShapesCut X lf links x rl lay and HasU X give momentsB rl = true.
Not shown here: HasU X. OnBytes/Tie/Pv/Lookup/Ends/FoHasU.lean's `public_hasU` shows it of every X
that Verify.publicOf returns.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoDeclMoments
import OnBytes.Tie.Pv.Lookup.Ends.FoPlannedCut

set_option autoImplicit false

namespace Fo.ReqF
open OnBytes OnBytes.Params OnBytes.Plan OnBytes.Model OnBytes.Model.Stages OnBytes.Model.Verify

/-- Every link that the verifier lists for X has one of the vectors U1 to U4. -/
def HasU (X : Public) : Prop :=
  ∀ links0, linksOf X default = .ok links0 →
    ∀ Y ∈ links0.toList, ∃ u ∈ Y.tl.ix.U.toList.take 4, u.isSome = true

/-- **The frame's links of a run of shapesOf have three moments or more each, where every link has a
vector U.** -/
theorem shapesCut_moments {X : Public} {lf : Option ByteArray} {links : Array LinkH} {x : Shapes}
    {rl : List ReqLink} {lay : ReqLayout} (h : ShapesCut X lf links x rl lay) (hU : HasU X) :
    TwLaw.momentsB rl = true := by
  obtain ⟨links0, declared, file, h1, h2, _, h4, _⟩ := h
  exact reqFrame_moments h4 (declareLinks_moments h2 (hU links0 h1))

end Fo.ReqF
