-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/MasksPlan.lean: the block's own test on the plan holds `MasksFixed`
(MasksFixed.lean).

Statements and proofs.
Main names:
  `stagesOk_of_planOk`: the frame's test on the plan holds sizesOk's walk, whatever the parts.
  `masksFixed_of_planOk`: (proximityTestKind guardedProximityTestParts p).planOk = true gives MasksFixed p. Of guardedProximityTestParts it spends
    fixedOk alone (`fixed_of_planOk`, Top.lean): for the field front. The other three fields are had
    from the frame's clauses, whatever the parts.
Limits: at parts whose front does not ask fixedOk the test on the plan can say yes where MasksFixed
fails (the plans of `not_masksFixed_of_empty`). That planOk says yes at a real place is not shown
here: it has been seen in runs only. No soundness is claimed, and nothing is said on hiding.

-/
import Johnson.Desc.K12.Law.MasksFixed
import Johnson.Desc.K12.Law.Top

set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12

theorem stagesOk_of_planOk {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) :
    stagesOk p.answers none p.nums.stages = true := by
  unfold proximityTestKind at hp
  split at hp
  · simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have h := hp.1.1.1.1
    unfold sizesOk at h
    simp only [Bool.and_eq_true] at h
    exact h.2
  · cases hp

/-- **The block's own test on the plan holds MasksFixed.** -/
theorem masksFixed_of_planOk (p : P12)
    (hp : (proximityTestKind guardedProximityTestParts p : H2K.JointK.Blk').planOk = true) : MasksFixed p := by
  obtain ⟨rds, hr, hl⟩ := rounds_of_planOk guardedProximityTestParts p hp
  exact masksFixed_made p rds hr hl p.answers (stagesOk_of_planOk guardedProximityTestParts p hp)
    (H2K.JointK.fixed_of_planOk p hp)

end H2K.Made

#print axioms H2K.Made.masksFixed_of_planOk
