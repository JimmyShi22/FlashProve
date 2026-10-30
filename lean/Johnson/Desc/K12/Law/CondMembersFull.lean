-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/CondMembersFull.lean: the condition of the law of a proximity test (the kind
K12), `K12Condition`, with no premise, at the four places of the proof file of the full-size stored
example proof. Statements and proofs; at each place three tests are evaluated in the kernel, and two
equations hold by `rfl`.

Why. As Johnson/Desc/K12/Law/CondMembers.lean, at the full size: at a closed place
(Johnson/Desc/K12/Law/PlacesFull.lean) the four premises of `k12Condition_at_written`
(Johnson/Desc/K12/Law/CondAtWritten.lean) are decided: the two equations by `rfl`, the two tests by
evaluation in the kernel.
Main names:
  `piUFull_stages`, `piUFull_work`, `piUFull_planOk`, `piUFull_pubOk`, and the like at O, W and L.
  `piOFull_own`: at O the first fold sends its own mask.
  `k12Condition_piUFull` … `k12Condition_piLFull`: the written test T of the number 6, 7, 8 or 5 of
    `testsFull` has `K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (radOf T) p codesFull (2⁻¹ ^ 128)` at
    the place p.
  `piUFull_rad` … `piLFull_rad`: at the place's stages the written test's radii are the closed radii
    of PlacesFull.lean: evaluated in the kernel.
  `k12Condition_piUFull_r` … `k12Condition_piLFull_r`: the condition at `fun s => rUFull s.st` …, by
    `k12Condition_congr` (Johnson/Desc/K12/Law/CondCongr.lean): no ∃ is left.
It stands over files of Johnson/Bridge/, and so over Cb/Bridge/CodeListRSProved.lean and
the files under ThirdParty/, adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15). It takes no run of their text; it calls their names.
Limits: that the closed places are the places which a description makes of the stored public files
is a run's word (PlacesFull.lean's head). The limits of the condition stand: one round's share of
its written verifier messages, test bits among them: W of the 128 bits are work; no sum over rounds;
the round "BAT" stands in front of the chain and is not in it; of the chain, not of the block. No
soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.CondMembers
import Johnson.Desc.K12.Law.PlacesFull

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Bridge (TestAt testsFull)
open H2K.Member (piUFull piOFull piWFull piLFull codesFull rUFull rOFull rWFull rLFull)
open scoped ENNReal

theorem piUFull_stages : piUFull.nums.stages = stUFull := rfl

theorem piUFull_work : piUFull.nums.work = 28 := rfl

theorem piUFull_planOk : (proximityTestKind guardedProximityTestParts piUFull : Block T12 Unit).planOk = true := by decide +kernel

theorem piUFull_pubOk : pubOk piUFull codesFull = true := by decide +kernel

/-- **A member**: the condition at the place of the folded row, at the full size, with no
premise. -/
theorem k12Condition_piUFull : ∃ T, testsFull[6]? = some T ∧
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (radOf T) piUFull codesFull ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_written testsFull (fun _ h => ok_full h) 6 stUFull 28 trial_U_full
    piUFull codesFull piUFull_stages piUFull_work piUFull_planOk piUFull_pubOk

theorem piUFull_rad : ∀ a ∈ piUFull.nums.stages,
    radOf (testNo testsFull 6) (sgOf a) = rUFull (sgOf a).st := by decide +kernel

/-- The same at the closed radii `rUFull`. -/
theorem k12Condition_piUFull_r :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => rUFull s.st) piUFull codesFull
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨T, hT, hK⟩ := k12Condition_piUFull
  obtain rfl := testNo_of hT
  exact k12Condition_congr _ _ _ _ _ _ piUFull_rad hK

theorem piOFull_stages : piOFull.nums.stages = stOFull := rfl

theorem piOFull_work : piOFull.nums.work = 28 := rfl

theorem piOFull_planOk : (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).planOk = true := by decide +kernel

theorem piOFull_pubOk : pubOk piOFull codesFull = true := by decide +kernel

theorem piOFull_own : piOFull.nums.ownMask = true := rfl

/-- **A member**: the condition at the place of Omega, at the full size, with no
premise. -/
theorem k12Condition_piOFull : ∃ T, testsFull[7]? = some T ∧
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (radOf T) piOFull codesFull ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_written testsFull (fun _ h => ok_full h) 7 stOFull 28 trial_O_full
    piOFull codesFull piOFull_stages piOFull_work piOFull_planOk piOFull_pubOk

theorem piOFull_rad : ∀ a ∈ piOFull.nums.stages,
    radOf (testNo testsFull 7) (sgOf a) = rOFull (sgOf a).st := by decide +kernel

/-- The same at the closed radii `rOFull`. -/
theorem k12Condition_piOFull_r :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => rOFull s.st) piOFull codesFull
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨T, hT, hK⟩ := k12Condition_piOFull
  obtain rfl := testNo_of hT
  exact k12Condition_congr _ _ _ _ _ _ piOFull_rad hK

theorem piWFull_stages : piWFull.nums.stages = stWFull := rfl

theorem piWFull_work : piWFull.nums.work = 20 := rfl

theorem piWFull_planOk : (proximityTestKind guardedProximityTestParts piWFull : Block T12 Unit).planOk = true := by decide +kernel

theorem piWFull_pubOk : pubOk piWFull codesFull = true := by decide +kernel

/-- **A member**: the condition at the place of the own test, at the full size, with no
premise. -/
theorem k12Condition_piWFull : ∃ T, testsFull[8]? = some T ∧
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (radOf T) piWFull codesFull ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_written testsFull (fun _ h => ok_full h) 8 stWFull 20 trial_W_full
    piWFull codesFull piWFull_stages piWFull_work piWFull_planOk piWFull_pubOk

theorem piWFull_rad : ∀ a ∈ piWFull.nums.stages,
    radOf (testNo testsFull 8) (sgOf a) = rWFull (sgOf a).st := by decide +kernel

/-- The same at the closed radii `rWFull`. -/
theorem k12Condition_piWFull_r :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => rWFull s.st) piWFull codesFull
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨T, hT, hK⟩ := k12Condition_piWFull
  obtain rfl := testNo_of hT
  exact k12Condition_congr _ _ _ _ _ _ piWFull_rad hK

theorem piLFull_stages : piLFull.nums.stages = stLFull := rfl

theorem piLFull_work : piLFull.nums.work = 20 := rfl

theorem piLFull_planOk : (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).planOk = true := by decide +kernel

theorem piLFull_pubOk : pubOk piLFull codesFull = true := by decide +kernel

/-- **A member**: the condition at the place of the last test behind the links, at the full size,
with no
premise. -/
theorem k12Condition_piLFull : ∃ T, testsFull[5]? = some T ∧
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (radOf T) piLFull codesFull ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_written testsFull (fun _ h => ok_full h) 5 stLFull 20 trial_L_full
    piLFull codesFull piLFull_stages piLFull_work piLFull_planOk piLFull_pubOk

theorem piLFull_rad : ∀ a ∈ piLFull.nums.stages,
    radOf (testNo testsFull 5) (sgOf a) = rLFull (sgOf a).st := by decide +kernel

/-- The same at the closed radii `rLFull`. -/
theorem k12Condition_piLFull_r :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => rLFull s.st) piLFull codesFull
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨T, hT, hK⟩ := k12Condition_piLFull
  obtain rfl := testNo_of hT
  exact k12Condition_congr _ _ _ _ _ _ piLFull_rad hK

end H2K.Pub

#print axioms H2K.Pub.piUFull_planOk
#print axioms H2K.Pub.piUFull_pubOk
#print axioms H2K.Pub.k12Condition_piUFull_r
#print axioms H2K.Pub.k12Condition_piOFull_r
#print axioms H2K.Pub.k12Condition_piWFull_r
#print axioms H2K.Pub.k12Condition_piLFull_r
