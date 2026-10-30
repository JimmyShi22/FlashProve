-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/Run/SetUpBase.lean

Facts on the public part of the stored full-size example's files "VerifierAndGoals.storedPublicFiles"
(Ladder/Stored.lean). One theorem; its proof calls the library's lemmas alone.

Main theorem:
* "base_facts": where "publicOfO" at "OnBytes.secondHashFunction" returns X₀ at the stored files: Lam = 4,
  NGr = 12, ldh = 7, kFD = 16, Sx = 12, rx = 8, the head's T = 1024, and in each of the twelve
  groups the four layers have one shift "klSh".

Limits. That "publicOfO" returns at the stored files is the hypothesis h₀: it is not proved here.
"attribute [-instance]" takes "Inst.Model.Scl.ref" out for this file: no default table of scales
is in sight. "attribute [local irreducible] VerifierAndGoals.storedPublicFiles" keeps the named files folded (why: the
note in Johnson/Goal/Files/FilesReadProof.lean on comparing the files byte by byte).

Not claimed: any property of a release, of a verifier or of a prover.
-/
import Johnson.Goal.Meaning.AttForInScope
import Johnson.Goal.Meaning.HeadShapeScope
import Johnson.Goal.Files.ScopeExample
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

/- The named files stay folded (Johnson/Goal/Files/FilesReadProof.lean's own note). -/
attribute [local irreducible] VerifierAndGoals.storedPublicFiles

namespace HonestTraceRun

namespace SetUp

open OnBytes OnBytes.Model OnBytes.Model.Verify

theorem base_facts {X₀ : Public} (h₀ : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀) : X₀.layers.y.Lam = 4 ∧ X₀.layers.y.NGr = 12 ∧ X₀.layers.y.ldh = 7 ∧ X₀.P.h.kFD = 16 ∧ X₀.P.h.Sx = 12 ∧ X₀.P.h.rx = 8 ∧ (headShape X₀.P X₀.layers.y).T = 1024 ∧ ∀ g, g < 12 → ∀ l, l < 4 → X₀.layers.sc.klSh (g * 4 + l) = X₀.layers.sc.klSh (g * 4 + 0) := by
  rw [VerifiableInference.PlanWritten.publicOfO_older] at h₀
  have hS := VerifierAndGoals.inScope_full
  obtain ⟨pp, hR, -⟩ := VerifierAndGoals.filesRead.full.2
  have A := OnBytes.Road.Hd.core_of_scope hS hR h₀
  have B := OnBytes.Road.Hd.public_of_core h₀ A
  have Fl := OnBytes.Road.Hd.fillRef_of_core A B
  have hLam : X₀.y.Lam = 4 := by
    rw [(OnBytes.Road.laid_of_layout B.lay B.switches.p3).2.Lam, OnBytes.Road.shape_of_public h₀]
    show 2 ^ X₀.P.h.ll = 4
    rw [show X₀.P.h.ll = 2 from A.num 3]
    all_goals norm_num
  have hk : X₀.P.h.kFD = 16 := by
    rw [OnBytes.Road.Hd.scan_of_scope hS hR h₀]
    rfl
  have hT : (headShape X₀.P X₀.y).T = 1024 := by
    rw [← Meaning.HeadS.headShape_of_public h₀]
    unfold Head.Shape.T
    rw [(Meaning.HeadS.sizes_in_scope hS hR h₀).1]
  exact ⟨hLam, B.groups, Fl.ldh, hk, Fl.Sx, Fl.rx, hT,
    fun g hg l hl => Meaning.Att.shifts_in_scope hS hR h₀ hg hl⟩

end SetUp

end HonestTraceRun

#print axioms HonestTraceRun.SetUp.base_facts
#check @HonestTraceRun.SetUp.base_facts
