-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/PlanWrittenDescScope.lean: over Johnson/Goal/Numbers/PlanWrittenScope.lean and
Johnson/Desc/Ok/PlanWritten/Seat.lean: IN THE GOALS' SCOPE A YES OF THE TEST ON A DESCRIPTION's
DECLARED ROUNDS AND DEPTH (Johnson/Desc/Ok/PlanWritten/Test.lean) says: written out, the
description's declared rounds are the full size's written lists, its depth is 32, and the data that
it hands the compiler are the written data. For the form from the public parameter file
(`seatPinnedProof`, `seatPinnedKey`): with no m and no key in the statement. This file reaches
Ladder.lean through its imports.

ROW OR TOOL. EVERY DECLARATION HERE IS A TOOL: a rule for all descriptions F and all files in scope.
No description is named. F IS A FREE LETTER, bound to neither Z nor m.

Definitions, statements and proofs.
  `SeatInScope`, `seat_in_scope`: THE CLOSED RULE and its proof: for every F and every Z with
    `VerifierAndGoals.InScope Z = true`: `seatPinnedProof Z.pol F = true` gives `writtenOf "proof file" F.roundsDeclaredByBlocks
    = .ok dryProofFull`, `F.tableDepth = 32` and `F.data "proof file" = .ok writtenPFull`.
    `SeatInScopeKey`, `seat_in_scope_key`: the key file's like. By `scan_key_in_scope`: in scope the
    scan's key is the full size's (`inScope_policy`, `scan_sizes`,
    Johnson/Goal/PlanValues/ScopeAtPlan.lean): NO PLANNER IS NAMED.
  `DescInScope`, `desc_in_scope`, `DescInScopeKey`, `desc_in_scope_key`: the like for
    `descPinnedProof (keyOf m) F`, `descPinnedKey (keyOf m) F` at every m that `madeOfAt` returns at
    Z and any c. By `key_in_scope` (Johnson/Goal/Numbers/PlanWrittenScope.lean). `AtInScope`,
    `at_in_scope`, `AtInScopeKey`, `at_in_scope_key`: the same under the names `pinnedProofAt m F`,
    `pinnedKeyAt m F`. `at_in_scope_own`: at an m that `madeOf` returned at Z.
  TEETH. `seat_no_in_scope`, `seat_plant_in_scope`: IN SCOPE A PLANT IS REFUSED, whether the scan
    returns or not. `seat_depth_in_scope`: in scope, at another depth than 32: no.
  `rideDescFull note`, `rideDescGap note`: FOR A RUN: `rideDesc`
    (Johnson/Desc/Ok/PlanWritten/AtDesc.lean) at the two named sets of public files: four named
    Bools each, one call of the planner each: to say true, true, true, false.

WHAT THE SHORT RIDES SHOW, AND WHAT NOT (`ridePinnedFull`, `ridePinnedGap`,
Johnson/Goal/Numbers/PlanWrittenScope.lean; `rideDescFull`, `rideDescGap`, here). They evaluate the
tests at THE PLANNER's data: the m, the declared rounds, the depth and the key that are made of the
two named sets at 32 zero bytes. All true where foretold, they show that the tests' bodies are no
"no to all" at what the planner makes. NO DESCRIPTION IS EVALUATED BY THEM: that a description with
the conjunct laid says yes at the two named sets is shown only by a run of that description.

Limits. That a description asks the test, at the parameter file of which the scope was asked, is
shown of no description. ONE DIRECTION: nothing here says that the test says yes anywhere. That the
scan returns in scope is not shown here; where it refuses the test says no. All limits of
Johnson/Goal/Numbers/PlanWrittenScope.lean, Johnson/Desc/Ok/PlanWritten/AtDesc.lean and
Johnson/Desc/Ok/PlanWritten/Seat.lean. Nothing on soundness.


-/
import Johnson.Goal.Numbers.PlanWrittenScope
import Johnson.Desc.Ok.PlanWritten.Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number VerifiableInference.Desc
open OnBytes.Model (polScan PolScan)

variable {Xi : Type}

/-- **THE CLOSED RULE, for a proof file's description.** -/
def DescInScope : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (Z : VerifierAndGoals.PublicFiles) (c : ByteArray) (m : Made),
    VerifierAndGoals.InScope Z = true → madeOfAt Z.pol Z.lay Z.KL c = .ok m →
    descPinnedProof (keyOf m) F = true →
      writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull ∧ F.tableDepth = 32 ∧
        F.data "proof file" = .ok writtenPFull

/-- Its proof. -/
theorem desc_in_scope : DescInScope := fun _ _ Z c m hZ h hy =>
  have hk := key_in_scope Z c m hZ h
  ⟨(descPinned_yes hk hy).1, (descPinned_yes hk hy).2, data_of_pinnedProof hk hy⟩

/-- **THE CLOSED RULE, for a key file's description.** -/
def DescInScopeKey : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (Z : VerifierAndGoals.PublicFiles) (c : ByteArray) (m : Made),
    VerifierAndGoals.InScope Z = true → madeOfAt Z.pol Z.lay Z.KL c = .ok m →
    descPinnedKey (keyOf m) F = true →
      writtenOf "key file" F.roundsDeclaredByBlocks = .ok dryKeyFull ∧ F.tableDepth = 32 ∧
        F.data "key file" = .ok writtenKFull

/-- Its proof. -/
theorem desc_in_scope_key : DescInScopeKey := fun _ _ Z c m hZ h hy =>
  have hk := key_in_scope Z c m hZ h
  ⟨(descPinned_yes hk hy).1, (descPinned_yes hk hy).2, data_of_pinnedKey hk hy⟩

/-! ## The forms to call -/

/-- **THE CLOSED RULE, for a maker's own m: a proof file's description.** -/
def AtInScope : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (Z : VerifierAndGoals.PublicFiles) (c : ByteArray) (m : Made),
    VerifierAndGoals.InScope Z = true → madeOfAt Z.pol Z.lay Z.KL c = .ok m → pinnedProofAt m F = true →
      writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull ∧ F.tableDepth = 32 ∧
        F.data "proof file" = .ok writtenPFull

/-- Its proof. -/
theorem at_in_scope : AtInScope := desc_in_scope

/-- **A key file's description.** -/
def AtInScopeKey : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (Z : VerifierAndGoals.PublicFiles) (c : ByteArray) (m : Made),
    VerifierAndGoals.InScope Z = true → madeOfAt Z.pol Z.lay Z.KL c = .ok m → pinnedKeyAt m F = true →
      writtenOf "key file" F.roundsDeclaredByBlocks = .ok dryKeyFull ∧ F.tableDepth = 32 ∧
        F.data "key file" = .ok writtenKFull

/-- Its proof. -/
theorem at_in_scope_key : AtInScopeKey := desc_in_scope_key

/-- At an m that `madeOf` returned, at the format's own digest: both files' descriptions. -/
theorem at_in_scope_own {Z : VerifierAndGoals.PublicFiles} {m : Made} (hZ : VerifierAndGoals.InScope Z = true)
    (h : madeOf Z.pol Z.lay Z.KL = .ok m) :
    (∀ F : FileDescription Xi, pinnedProofAt m F = true →
        writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull ∧ F.tableDepth = 32 ∧
          F.data "proof file" = .ok writtenPFull) ∧
      ∀ F : FileDescription Xi, pinnedKeyAt m F = true →
        writtenOf "key file" F.roundsDeclaredByBlocks = .ok dryKeyFull ∧ F.tableDepth = 32 ∧
          F.data "key file" = .ok writtenKFull :=
  ⟨fun F hy => at_in_scope Xi F Z _ m hZ (madeOfAt_of_madeOf h) hy,
    fun F hy => at_in_scope_key Xi F Z _ m hZ (madeOfAt_of_madeOf h) hy⟩

/-- **In scope the scan's key is the full size's.** No planner is named. -/
theorem scan_key_in_scope {Z : VerifierAndGoals.PublicFiles} {P : PolScan} (hZ : VerifierAndGoals.InScope Z = true)
    (h : polScan Z.pol = .ok P) : keyOfScan P = fullKey := by
  obtain ⟨v, hv⟩ := Lk6.AtPlan.inScope_policy hZ
  rw [hv] at h
  obtain ⟨_, b1, b2, _, _, _, _, _, _, b9, _⟩ := Lk6.AtPlan.scan_sizes h
  unfold keyOfScan fullKey
  rw [b1, b2, b9]

/-- **THE CLOSED RULE, from the parameter file: a proof file's description.** No m and no key is
named. -/
def SeatInScope : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (Z : VerifierAndGoals.PublicFiles),
    VerifierAndGoals.InScope Z = true → seatPinnedProof Z.pol F = true →
      writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull ∧ F.tableDepth = 32 ∧
        F.data "proof file" = .ok writtenPFull

/-- Its proof. -/
theorem seat_in_scope : SeatInScope := by
  intro Xi F Z hZ h
  cases hP : polScan Z.pol with
  | ok P => exact seat_yes hP (scan_key_in_scope hZ hP) h
  | error e =>
    rw [seat_refusal F hP] at h
    cases h

/-- **A key file's description.** -/
def SeatInScopeKey : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (Z : VerifierAndGoals.PublicFiles),
    VerifierAndGoals.InScope Z = true → seatPinnedKey Z.pol F = true →
      writtenOf "key file" F.roundsDeclaredByBlocks = .ok dryKeyFull ∧ F.tableDepth = 32 ∧
        F.data "key file" = .ok writtenKFull

/-- Its proof. -/
theorem seat_in_scope_key : SeatInScopeKey := by
  intro Xi F Z hZ h
  cases hP : polScan Z.pol with
  | ok P => exact seat_yes_key hP (scan_key_in_scope hZ hP) h
  | error e =>
    unfold seatPinnedKey at h
    rw [hP] at h
    cases h

/-- In scope the test says no wherever the written rounds and the depth are not the written ones,
whether the scan returns or not. -/
theorem seat_no_in_scope {Z : VerifierAndGoals.PublicFiles} {F : FileDescription Xi} (hZ : VerifierAndGoals.InScope Z = true)
    (hn : ¬ (writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull ∧ F.tableDepth = 32)) :
    seatPinnedProof Z.pol F = false := by
  cases h : seatPinnedProof Z.pol F with
  | false => rfl
  | true =>
    obtain ⟨a, b, _⟩ := seat_in_scope Xi F Z hZ h
    exact absurd ⟨a, b⟩ hn

/-- **A tooth: IN SCOPE A PLANT IS REFUSED.** -/
theorem seat_plant_in_scope {Z : VerifierAndGoals.PublicFiles} {F : FileDescription Xi} (hZ : VerifierAndGoals.InScope Z = true)
    (hw : writtenOf "proof file" F.roundsDeclaredByBlocks = .ok plantedProof) : seatPinnedProof Z.pol F = false :=
  seat_no_in_scope hZ fun x => plantedProof_ne (Except.ok.inj (hw.symm.trans x.1))

/-- A tooth: in scope, at another depth than 32. -/
theorem seat_depth_in_scope {Z : VerifierAndGoals.PublicFiles} {F : FileDescription Xi} (hZ : VerifierAndGoals.InScope Z = true)
    (hd : F.tableDepth ≠ 32) : seatPinnedProof Z.pol F = false :=
  seat_no_in_scope hZ fun x => hd x.2

/-! ## For a run -/

/-- FOR A RUN: `rideDesc` (Johnson/Desc/Ok/PlanWritten/AtDesc.lean) at the stored full-size public
files. -/
def rideDescFull (note : String) : List (String × Bool) :=
  rideDesc note VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL

/-- FOR A RUN: at the same three files with the other policy. -/
def rideDescGap (note : String) : List (String × Bool) :=
  rideDesc note VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.lay VerifierAndGoals.zGap.KL

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.desc_in_scope
#print axioms VerifiableInference.PlanWritten.desc_in_scope_key
#print axioms VerifiableInference.PlanWritten.at_in_scope
#print axioms VerifiableInference.PlanWritten.at_in_scope_key
#print axioms VerifiableInference.PlanWritten.at_in_scope_own
#print axioms VerifiableInference.PlanWritten.scan_key_in_scope
#print axioms VerifiableInference.PlanWritten.seat_in_scope
#print axioms VerifiableInference.PlanWritten.seat_in_scope_key
#print axioms VerifiableInference.PlanWritten.seat_no_in_scope
#print axioms VerifiableInference.PlanWritten.seat_plant_in_scope
#print axioms VerifiableInference.PlanWritten.seat_depth_in_scope
