-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/PlanValues/KeyPlansAtScope.lean: at every three public files in the scope of the goals,
the setting and the 32 lines in what the program computes are the written ones, and the three plans
of the key file's chains are what the planner's three routines return at the typed sizes keyFull.

Params.configure makes the key's three plans by Plan.oneTimePlan at the key's sizes, and by
Params.sharedPlan and Params.secondPlan at the setting of ALL sizes (made.sized.set) and parts of
the key's sizes. Johnson/Goal/PlanValues/KeyFullAtScope.lean pins the key's sizes, whose own field
set is the written setting. Here the setting of all sizes is pinned too, so that the three calls
stand at closed arguments.

Main names.
  frame_at_scope   the 32 lines that the program has read are Params.recordLines.
  set_at_scope     p.chains.made.sized.set = Params.recordSet.
  plans_at_scope   p.chains.made.key = [P1, P2, P3] with Plan.oneTimePlan keyFull = .ok P1,
                   sharedPlan keyFull.set keyFull.codes keyFull.once = .ok P2 and
                   secondPlan keyFull.set keyFull.once = .ok P3.

Limits. One direction: from a program that returns. What the plans' entries are is not typed.
Nothing on soundness.
-/
import Johnson.Goal.PlanValues.KeyFullAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.AtPlan
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify

/-- The 32 lines that the program has read, and what it configures of them. -/
theorem frame_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Verify.Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) :
    p.X.P.frame = recordLines ∧
      ∃ shapes cfg, configure recordLines shapes cfg 0 = .ok p.chains.made := by
  obtain ⟨v, hv⟩ := inScope_policy hZ
  rw [hv] at hp
  obtain ⟨links, shapes, _, _, _, _, _, hX, _, hs, _, _, hc, _, _, _, _⟩ := planned_parts hp
  obtain ⟨y, hy, _⟩ := publicOf_wsLay hX
  have hf := scan_frame (polLayout_scan hy)
  rw [hf] at hc
  exact ⟨hf, _, _, hc⟩

/-- **The setting of all sizes is the written setting.** -/
theorem set_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Verify.Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) : p.chains.made.sized.set = recordSet := by
  obtain ⟨_, shapes, cfg, hc⟩ := frame_at_scope hZ hp
  exact (sized_link (configure_plans hc).1).1

/-- **The key file's three plans are what the three routines return at the typed sizes.** -/
theorem plans_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Verify.Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) :
    ∃ P1 P2 P3, p.chains.made.key = [P1, P2, P3] ∧ Plan.oneTimePlan keyFull = .ok P1 ∧
      sharedPlan keyFull.set keyFull.codes keyFull.once = .ok P2 ∧
      secondPlan keyFull.set keyFull.once = .ok P3 := by
  obtain ⟨_, shapes, cfg, hc⟩ := frame_at_scope hZ hp
  obtain ⟨_, _, P1, P2, P3, e, h1, h2, h3, _⟩ := configure_plans hc
  rw [key_eq_at_scope hZ hp] at h1 h2 h3
  rw [set_at_scope hZ hp] at h2 h3
  exact ⟨P1, P2, P3, e, h1, h2, h3⟩

end Lk6.AtPlan

#print axioms Lk6.AtPlan.frame_at_scope
#print axioms Lk6.AtPlan.set_at_scope
#print axioms Lk6.AtPlan.plans_at_scope
