-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/LayerCells.lean: THE LAYERS' SORTS AS Join.lean's CellRel, AT THE LINKS
l EVEN, l < 24: places 2 (lookCalls), 3 (K4), 4 (reads), 7 (lookDigits), 8 (batch), 9 (behind).

  step_of_return   at the stored files' record the head's link is link 24.
  **lookCalls_rel**, **own_rel**, **reads_rel**, **lookDigits_rel**, **batch_rel**, **behind_rel**.

Limits. Each is cellRel_of_eq at LayerSorts.lean's equation. Nothing is evaluated.
-/
import Johnson.AtFull.Shape.Scope.Join
import Johnson.AtFull.Shape.Scope.LayerSorts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.PlanWritten (publicOfO)

variable {X X₀ : Verify.Public}

/-- At the stored files' record the head's link is link 24. -/
theorem step_of_return
    (h₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀) :
    (if X₀.p4 = true then 2 else 1) * X₀.NGr = 24 := by
  have hN : X₀.NGr = 12 := (HonestTraceRun.SetUp.base_facts h₀).2.1
  have h4 : X₀.p4 = true := by
    have h₀' := h₀
    rw [VerifiableInference.PlanWritten.publicOfO_older] at h₀'
    have hS := VerifierAndGoals.inScope_full
    obtain ⟨pp, hR, -⟩ := VerifierAndGoals.filesRead.full.2
    have A := OnBytes.Road.Hd.core_of_scope hS hR h₀'
    show X₀.y.h.p4 = true
    rw [OnBytes.Road.shape_of_public h₀']
    exact OnBytes.Road.Hd.p4_of_core A
  rw [h4, hN]
  rfl

section
variable {l : Nat} (he : l % 2 = 0) (hl : l < 24)
include he hl

theorem odd_even {j : Nat} (hj : j < 14) : oddAt (14 * l + j + 1) = false := by
  rw [oddAt_place hl hj]
  simp [he]

variable (S : SameRead X X₀)
  (h₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
include S

include h₀ in
theorem lookCalls_rel : CellRel X X₀ (14 * l + 2 + 1) ((TabL.linkRow (LW X) l).at 2)
    ((TabL.linkRow (LW X₀) l).at 2) :=
  cellRel_of_eq (odd_even he hl (by omega)) (lookCalls_eq S he (by rw [step_of_return h₀]; omega))

theorem own_rel : CellRel X X₀ (14 * l + 3 + 1) ((TabL.linkRow (LW X) l).at 3)
    ((TabL.linkRow (LW X₀) l).at 3) := by
  refine cellRel_of_eq (odd_even he hl (by omega)) ?_
  have hb : (l % 2 == 0) = true := by simp [he]
  show (if l % 2 == 0 then TabL.k4 (LW X) (l / 2) else TabL.k5 (LW X) (l / 2)).1 =
    (if l % 2 == 0 then TabL.k4 (LW X₀) (l / 2) else TabL.k5 (LW X₀) (l / 2)).1
  rw [if_pos hb, if_pos hb]
  exact k4_eq S _

theorem reads_rel : CellRel X X₀ (14 * l + 4 + 1) ((TabL.linkRow (LW X) l).at 4)
    ((TabL.linkRow (LW X₀) l).at 4) :=
  cellRel_of_eq (odd_even he hl (by omega)) (reads_eq S he)

include h₀ in
theorem lookDigits_rel : CellRel X X₀ (14 * l + 7 + 1) ((TabL.linkRow (LW X) l).at 7)
    ((TabL.linkRow (LW X₀) l).at 7) :=
  cellRel_of_eq (odd_even he hl (by omega)) (lookDigits_eq S he (by rw [step_of_return h₀]; omega))

theorem batch_rel : CellRel X X₀ (14 * l + 8 + 1) ((TabL.linkRow (LW X) l).at 8)
    ((TabL.linkRow (LW X₀) l).at 8) :=
  cellRel_of_eq (odd_even he hl (by omega)) (batch_eq S he (by omega))

theorem behind_rel : CellRel X X₀ (14 * l + 9 + 1) ((TabL.linkRow (LW X) l).at 9)
    ((TabL.linkRow (LW X₀) l).at 9) :=
  cellRel_of_eq (odd_even he hl (by omega)) (behind_eq S he)

end

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.step_of_return
#print axioms Johnson.AtFull.Shape.Scope.lookCalls_rel
#print axioms Johnson.AtFull.Shape.Scope.own_rel
#print axioms Johnson.AtFull.Shape.Scope.reads_rel
#print axioms Johnson.AtFull.Shape.Scope.lookDigits_rel
#print axioms Johnson.AtFull.Shape.Scope.batch_rel
#print axioms Johnson.AtFull.Shape.Scope.behind_rel
