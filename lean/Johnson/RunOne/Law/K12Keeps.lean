-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Keeps.lean: EVERY RELATION ON STATEMENTS THAT THE GROUND's PLAIN FUNCTIONS KEEP (GroundKeeps, Johnson/Desc/GroundKeeps.lean) AND THAT THE BEGINNING OF A TEST KEEPS CROSSES THE PROXIMITY TEST: a yes of its decision keeps it. With three members: "no open row is marked as a sample row" (Means.OpenKinds), "a message that is not marked as sampled has no sample row" (NoneYet), "every member of a group is marked as sampled" (SampledMembers); and, with Johnson/RunOne/Law/K12Order.lean, all four of Means.Tidy one by one. Statements with proofs.
OBJECT. (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide; and the key file's ranges' test's block. USER. Another file's walk along the history of the key file's three chains ("at every record that chain j reaches: OpenKinds"); grows_of_run wants OpenKinds at border 15.
LETTERS. R p t0 tE rs gs | one N s s': free. Premises: GroundKeeps R · hb: the beginning of a test keeps R (it stands outside that record: Johnson/Desc/Means/FrameKeeps.lean's head) · the yes. NO PREMISE ON THE PLAN, THE RECORD OR THE VIEW.
NOT THIS FILE's MATHEMATICS: k12_calls (Johnson/Desc/K12/Law/Calls.lean): a yes of the test is a run of the ground's plain calls; the keepers one storey beneath stand in the library (Means/FrameKeeps.lean · Kinds.lean · BackP.lean · Entry.lean). Here: one induction.

  call_keeps | calls_keeps: a step | a run keeps R. k12_keeps: the test. ranges_keeps: the key file's block.
  k12_openKinds | k12_noneYet | k12_members · ranges_openKinds | ranges_noneYet | ranges_members: the three members.
Limits. A block that says no to all meets every statement. That OpenKinds holds at any record in front is not said here. Nothing on soundness, nothing on hiding.

-/
import Johnson.Desc.K12.Law.Calls
import Johnson.Desc.Means.FrameKeeps
import Johnson.RunOne.Law.RngAtKeyD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Keeps
open OnBytes OnBytes.Params OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open H2K.Out (DS Call Calls dT k12_calls)

variable {ft : Nat} {R : Statement → Statement → Prop}

/-- One step of the ground keeps R. -/
theorem call_keeps (H : GroundKeeps R) (hb : ∀ (d d' : DS) (g : Nat) (run : RunInput), beginRunP d g = some (run, d') → R d.st d'.st)
    (d d' : DS) (h : Call ft d d') : R d.st d'.st := by
  cases h with
  | newGroup h => exact H.newGroup _ _ _ _ _ h
  | recv h => exact H.recv _ _ _ _ _ h
  | admit _ _ _ _ h => exact H.admit _ _ _ _ h
  | join h => exact H.join _ _ _ _ _ h
  | addRow h => exact H.addRow _ _ _ _ h
  | closeLedger h => exact H.closeLedger _ _ _ h
  | spend h => exact H.spendAsMask _ _ _ h
  | begin h => exact hb _ _ _ _ h
  | count t => exact H.refl _
  | cols l => exact H.refl _

/-- A run of the ground's calls keeps R. -/
theorem calls_keeps (H : GroundKeeps R) (hb : ∀ (d d' : DS) (g : Nat) (run : RunInput), beginRunP d g = some (run, d') → R d.st d'.st)
    {d d' : DS} (h : Calls ft d d') : R d.st d'.st := by
  induction h with
  | nil d => exact H.refl _
  | cons s _ ih => exact H.trans (call_keeps H hb _ _ s) ih

/-- **A yes of the proximity test's decision keeps R.** -/
theorem k12_keeps (H : GroundKeeps R) (hb : ∀ (d d' : DS) (g : Nat) (run : RunInput), beginRunP d g = some (run, d') → R d.st d'.st)
    (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t0 rs gs = .ok tE) : R t0.st tE.st :=
  calls_keeps H hb (k12_calls p t0 tE rs gs h [] [])

theorem k12_openKinds (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t0 rs gs = .ok tE) (hK : OpenKinds t0.st) : OpenKinds tE.st :=
  k12_keeps groundKeeps_openKinds (fun _ _ _ _ h => beginRunP_kinds h) p t0 tE rs gs h hK

theorem k12_noneYet (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t0 rs gs = .ok tE) (hK : NoneYet t0.st) : NoneYet tE.st :=
  k12_keeps groundKeeps_noneYet (fun _ _ _ _ h => beginRunP_none h) p t0 tE rs gs h hK

theorem k12_members (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t0 rs gs = .ok tE) (hK : SampledMembers t0.st) : SampledMembers tE.st :=
  k12_keeps groundKeeps_members (fun _ _ _ _ h => beginRunP_members h) p t0 tE rs gs h hK

open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState Claim enterRanges leaveRanges)
open Johnson.RunOne.Law.RngAsked Johnson.RunOne.Law.RngAnyCl Johnson.RunOne.Law.RngAtKeyD

/-- **The key file's ranges' test keeps R.** -/
theorem ranges_keeps (H : GroundKeeps R) (hb : ∀ (d d' : DS) (g : Nat) (run : RunInput), beginRunP d g = some (run, d') → R d.st d'.st)
    (one : OneTime) (N : H2U.PlaceNums) (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s') : R s.d.st s'.d.st := by
  obtain ⟨tE, _, _, _, hd, _, e⟩ := keyD_yes h
  have hd' : (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).decide (recD s) rs gs = .ok tE := by
    rw [(same_k12 (A := Unit) (B := Claim) guardedProximityTestParts (rangesParams N)).decide]
    exact hd
  have e' : s'.d.st = tE.st := by rw [e]
  rw [e']
  exact k12_keeps H hb _ _ _ _ _ hd'

theorem ranges_openKinds (one : OneTime) (N : H2U.PlaceNums) (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s') (hK : OpenKinds s.d.st) : OpenKinds s'.d.st :=
  ranges_keeps groundKeeps_openKinds (fun _ _ _ _ h => beginRunP_kinds h) one N s s' rs gs h hK

theorem ranges_noneYet (one : OneTime) (N : H2U.PlaceNums) (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s') (hK : NoneYet s.d.st) : NoneYet s'.d.st :=
  ranges_keeps groundKeeps_noneYet (fun _ _ _ _ h => beginRunP_none h) one N s s' rs gs h hK

theorem ranges_members (one : OneTime) (N : H2U.PlaceNums) (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s') (hK : SampledMembers s.d.st) : SampledMembers s'.d.st :=
  ranges_keeps groundKeeps_members (fun _ _ _ _ h => beginRunP_members h) one N s s' rs gs h hK

end Johnson.RunOne.Law.K12Keeps

#print axioms Johnson.RunOne.Law.K12Keeps.calls_keeps
#print axioms Johnson.RunOne.Law.K12Keeps.k12_keeps
#print axioms Johnson.RunOne.Law.K12Keeps.k12_openKinds
#print axioms Johnson.RunOne.Law.K12Keeps.k12_noneYet
#print axioms Johnson.RunOne.Law.K12Keeps.k12_members
#print axioms Johnson.RunOne.Law.K12Keeps.ranges_keeps
#print axioms Johnson.RunOne.Law.K12Keeps.ranges_openKinds
#print axioms Johnson.RunOne.Law.K12Keeps.ranges_noneYet
#print axioms Johnson.RunOne.Law.K12Keeps.ranges_members
