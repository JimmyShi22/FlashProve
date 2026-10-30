-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/OneRadPlanned.lean: `OneRad` (OneRadOfPlan.lean) at the four proximity tests of
a proof file, from the yes of the program's `planned` on the three public files.

Main name: `oneRad_planned`. `planned_parts` (OnBytes/Model/Fit/PlannedParts.lean) gives
`configure`'s yes and says that the sub-proofs are the model's; `subRuns_subproofsWith`
(OnBytes/Model/LinkRoundsList.lean) gives `Plan.SubRuns` of these. At Omega's test the premise on
the split stays.
Limits: as OneRadOfPlan.lean's. It speaks of what the planner returns: where a law is stated at a
written plan and not at a planner's return, its one premise is not at hand. Nothing on soundness.
Nothing on hiding.

-/
import OnBytes.Model.Fit.PlannedParts
import OnBytes.Model.LinkRoundsList
import Johnson.Desc.K12.Law.OneRadOfConfigure

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Model.Verify

/-- **From the program's yes on the three public files alone.** -/
theorem oneRad_planned {pol KL : ByteArray} {layout : Option ByteArray}
    {p : OnBytes.Model.Verify.Planned}
    (h : planned pol KL layout = .ok p) (σ : Setting) :
    OneRad σ p.chains.made.sized.proof.last.stages ∧
      OneRad σ p.chains.made.sized.proof.batch.folded.stages ∧
      (p.chains.made.sized.proof.batch.shape.sharedSplitNeeded = true →
        OneRad σ p.chains.made.sized.proof.batch.omega.stages) ∧
      OneRad σ p.chains.made.sized.proof.batch.own.stages := by
  obtain ⟨links, shapes, rest, declared, file, rl, lay, _, _, _, _, _, hc, _, _, _, e⟩ :=
    planned_parts h
  have S : Plan.SubRuns (settingOf p.X.P.frame) shapes.sub
      (linkList (settingOf p.X.P.frame) .request p.X) [] := by
    rw [e]
    exact subRuns_subproofsWith _ p.X rl
  exact ⟨oneRad_last_cfg hc S σ, oneRad_folded_cfg hc σ, fun hs => oneRad_omega_cfg hc hs σ,
    oneRad_own_cfg hc σ⟩

end H2K.Pub

#print axioms H2K.Pub.oneRad_planned
