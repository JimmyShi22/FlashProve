-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/CondMembers.lean: the condition of the law of a proximity test (the kind K12),
`K12Condition`, with no premise, at the four places of the proof file of the smaller stored example
proof. Statements and proofs; at each place three tests are evaluated in the kernel, and two
equations hold by `rfl`.

Why. `k12Condition_at_written` (Johnson/Desc/K12/Law/CondAtWritten.lean) wants, at a place: its
stages and its bits of work are a written test's; the test on the plan of the block
`proximityTestKind guardedProximityTestParts p`; `pubOk p K`. At a closed place (Johnson/Desc/K12/Law/PlacesSmall.lean) each of the
four is decided: the two equations by `rfl`, the two tests by evaluation in the kernel. So the
statements on the condition in this folder are not empty.
Main names:
  `piU_stages`, `piU_work`, `piU_planOk`, `piU_pubOk`, and the like at O, W and L.
  `piO_own`: at O the first fold sends its own mask.
  `k12Condition_piU`, `k12Condition_piO`, `k12Condition_piW`, `k12Condition_piL`: the written test T
    of the number 6, 7, 8 or 5 of `testsSmall` has
    `K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (radOf T) p codesSmall (2⁻¹ ^ 128)` at the place p.
  `testNo`, `piU_rad` … `piL_rad`: at the place's stages the written test's radii are the closed
    radii `rU` … `rL` of PlacesSmall.lean: evaluated in the kernel.
  `k12Condition_piU_r` … `k12Condition_piL_r`: the condition at `fun s => rU s.st` …, by
    `k12Condition_congr` (Johnson/Desc/K12/Law/CondCongr.lean): no ∃ is left.
It stands over files of Johnson/Bridge/, and so over Cb/Bridge/CodeListRSProved.lean and
the files under ThirdParty/, adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15). It takes no run of their text; it calls their names.
Limits: that the closed places are the places which a description makes of the stored public files
is a run's word (PlacesSmall.lean's head). The smaller stored example proof alone. The limits of the
condition stand: one round's share of its written verifier messages, test bits among them: W of the
128 bits are work; no sum over rounds; the round "BAT" stands in front of the chain and is not in
it; of the chain, not of the block. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.CondAtWritten
import Johnson.Desc.K12.Law.CondCongr
import Johnson.Desc.K12.Law.PlacesSmall

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Bridge (TestAt testsSmall)
open H2K.Member (piU piO piW piL codesSmall rU rO rW rL)
open scoped ENNReal

/-- The written test of a number; an empty one where the list has none. -/
def testNo (Ts : List TestAt) (i : ℕ) : TestAt :=
  (Ts[i]?).getD ⟨[], ⟨⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩, 0, 0, 0⟩, 0, 0, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩

theorem testNo_of {Ts : List TestAt} {i : ℕ} {T : TestAt} (h : Ts[i]? = some T) :
    T = testNo Ts i := by
  unfold testNo
  rw [h]
  rfl

theorem piU_stages : piU.nums.stages = stUSmall := rfl

theorem piU_work : piU.nums.work = 28 := rfl

theorem piU_planOk : (proximityTestKind guardedProximityTestParts piU : Block T12 Unit).planOk = true := by decide +kernel

theorem piU_pubOk : pubOk piU codesSmall = true := by decide +kernel

/-- **A member**: the condition at the place of the folded row, with no premise. -/
theorem k12Condition_piU : ∃ T, testsSmall[6]? = some T ∧
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (radOf T) piU codesSmall ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_written testsSmall (fun _ h => ok_small h) 6 stUSmall 28 trial_U_small piU
    codesSmall piU_stages piU_work piU_planOk piU_pubOk

theorem piU_rad : ∀ a ∈ piU.nums.stages,
    radOf (testNo testsSmall 6) (sgOf a) = rU (sgOf a).st := by decide +kernel

/-- The same at the closed radii `rU`. -/
theorem k12Condition_piU_r :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => rU s.st) piU codesSmall
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨T, hT, hK⟩ := k12Condition_piU
  obtain rfl := testNo_of hT
  exact k12Condition_congr _ _ _ _ _ _ piU_rad hK

theorem piO_stages : piO.nums.stages = stOSmall := rfl

theorem piO_work : piO.nums.work = 28 := rfl

theorem piO_planOk : (proximityTestKind guardedProximityTestParts piO : Block T12 Unit).planOk = true := by decide +kernel

theorem piO_pubOk : pubOk piO codesSmall = true := by decide +kernel

theorem piO_own : piO.nums.ownMask = true := rfl

/-- **A member**: the condition at the place of Omega, with no premise. -/
theorem k12Condition_piO : ∃ T, testsSmall[7]? = some T ∧
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (radOf T) piO codesSmall ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_written testsSmall (fun _ h => ok_small h) 7 stOSmall 28 trial_O_small piO
    codesSmall piO_stages piO_work piO_planOk piO_pubOk

theorem piO_rad : ∀ a ∈ piO.nums.stages,
    radOf (testNo testsSmall 7) (sgOf a) = rO (sgOf a).st := by decide +kernel

/-- The same at the closed radii `rO`. -/
theorem k12Condition_piO_r :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => rO s.st) piO codesSmall
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨T, hT, hK⟩ := k12Condition_piO
  obtain rfl := testNo_of hT
  exact k12Condition_congr _ _ _ _ _ _ piO_rad hK

theorem piW_stages : piW.nums.stages = stWSmall := rfl

theorem piW_work : piW.nums.work = 20 := rfl

theorem piW_planOk : (proximityTestKind guardedProximityTestParts piW : Block T12 Unit).planOk = true := by decide +kernel

theorem piW_pubOk : pubOk piW codesSmall = true := by decide +kernel

/-- **A member**: the condition at the place of the own test, with no premise. -/
theorem k12Condition_piW : ∃ T, testsSmall[8]? = some T ∧
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (radOf T) piW codesSmall ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_written testsSmall (fun _ h => ok_small h) 8 stWSmall 20 trial_W_small piW
    codesSmall piW_stages piW_work piW_planOk piW_pubOk

theorem piW_rad : ∀ a ∈ piW.nums.stages,
    radOf (testNo testsSmall 8) (sgOf a) = rW (sgOf a).st := by decide +kernel

/-- The same at the closed radii `rW`. -/
theorem k12Condition_piW_r :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => rW s.st) piW codesSmall
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨T, hT, hK⟩ := k12Condition_piW
  obtain rfl := testNo_of hT
  exact k12Condition_congr _ _ _ _ _ _ piW_rad hK

theorem piL_stages : piL.nums.stages = stLSmall := rfl

theorem piL_work : piL.nums.work = 20 := rfl

theorem piL_planOk : (proximityTestKind guardedProximityTestParts piL : Block T12 Unit).planOk = true := by decide +kernel

theorem piL_pubOk : pubOk piL codesSmall = true := by decide +kernel

/-- **A member**: the condition at the place of the last test behind the links, with no premise. -/
theorem k12Condition_piL : ∃ T, testsSmall[5]? = some T ∧
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (radOf T) piL codesSmall ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_written testsSmall (fun _ h => ok_small h) 5 stLSmall 20 trial_L_small piL
    codesSmall piL_stages piL_work piL_planOk piL_pubOk

theorem piL_rad : ∀ a ∈ piL.nums.stages,
    radOf (testNo testsSmall 5) (sgOf a) = rL (sgOf a).st := by decide +kernel

/-- The same at the closed radii `rL`. -/
theorem k12Condition_piL_r :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => rL s.st) piL codesSmall
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨T, hT, hK⟩ := k12Condition_piL
  obtain rfl := testNo_of hT
  exact k12Condition_congr _ _ _ _ _ _ piL_rad hK

end H2K.Pub

#print axioms H2K.Pub.piL_planOk
#print axioms H2K.Pub.piL_pubOk
#print axioms H2K.Pub.k12Condition_piU
#print axioms H2K.Pub.k12Condition_piO
#print axioms H2K.Pub.k12Condition_piW
#print axioms H2K.Pub.k12Condition_piL
#print axioms H2K.Pub.k12Condition_piU_r
#print axioms H2K.Pub.k12Condition_piO_r
#print axioms H2K.Pub.k12Condition_piW_r
#print axioms H2K.Pub.k12Condition_piL_r
