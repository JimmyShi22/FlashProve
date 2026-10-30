-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineSharedTestsTies.lean: THE TIES OF LETTERS at the shared chain's two proximity tests of the key file: the test on
G_u at ⟨2, –, 9⟩ and the test on G_omega at ⟨2, –, 10⟩: closed lines on written public values; what the prover's shared
list holds at the two places; which sub-protocols the description's shared list has there.
No run, no play, no thread. It imports nothing on the guard's lift, so that it can stand under either text on it.

  `foldedMembers_written`, `omegaMembers_written`, `foldedFresh_written`, `omegaNumbers_written`, `foldedStages_two`,
  `omegaStages_two`, `omegaFirst_splits`, `omegaEnough_written`, `writtenShape_splits`   closed lines, by the kernel
  `shared_nodup`, `shared_finds`, `half_at_omegaTest`   the prover's shared list: no two halves at one place; it finds its
                            two last halves at their places; the half at ⟨2, –, 10⟩ is the letter `onOmega`
  `sharedBlock_folded`, `sharedBlock_omega`   in scope the description's shared list has at these places these blocks alone
  `sharedTests_there`       a test of emptiness: in scope the list has a sub-protocol at each of the two places

Limits. At the written sizes, under `KeySourced` and `InScope`. Nothing on any property.
-/
import E2E.KeyValueHolds
import E2E.KeyNineClosed
import E2E.KeyShapeSharedTies
import E2E.KeyPlacesNamed
import Johnson.SendSim.Seat.LotsGuardTie
import Johnson.Desc.ProofFile.Honest.K12.AgreeAtKey
import Johnson.Desc.ProofFile.Honest.K12.PlanAtKeyKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K14 (SendPub sendPlace)
open OnBytes (TableKey)
open OnBytes.Slice (GF)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.K12 (P12 T12 Seat.enter Seat.leave)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open _root_.Desc.K14 (St)
open H2K.Pub (sgOf)
open H2K.Member (piKUFull piKOFull)
open H2K.JointK (keyGu keyOmega keyShared_cut keyShared_cut_omega)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription flat₂ flat₂_tie)
open AtPublicFiles.AtFiles.Full (QK PF later_sourced par_sourced omega_full)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace fullShared places_named)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver keyProver_shared)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeyLay (jobKU jobKO proverSideOfTestOnU proverSideOfTestOnOmega bsOf stOf wtOf rdOf)
open AtPublicFiles.KeyNineClosed (place_full)
open AtPublicFiles.KeyValues (WitK)
open AtPublicFiles.KeyValueHolds (valueAt place_p12At)
open Johnson.RunOne.Sound (rowsOf)
open VerifierAndGoals (PublicFiles InScope)

/-! ## Closed lines on written public values -/

/-- The members of the test on G_u at the written parameters. -/
def foldedMembers : List (Addr × Nat × Due) :=
  [(⟨sendPlace 2, 0⟩, 0, ⟨0, K14.dueOf (K14.jobU ⟨QK, 0⟩).Q.codes
      ((K14.jobU ⟨QK, 0⟩).Q.sent.getD 0 default).shape ((K14.jobU ⟨QK, 0⟩).sort 0)⟩),
   (⟨sendPlace 5, 0⟩, 1, ⟨0, K14.dueOf (K14.jobOmega ⟨QK, 0⟩).Q.codes
      ((K14.jobOmega ⟨QK, 0⟩).Q.sent.getD 1 default).shape ((K14.jobOmega ⟨QK, 0⟩).sort 1)⟩)]

/-- The members of the test on G_omega at the written parameters. -/
def omegaMembers : List (Addr × Nat × Due) :=
  [(⟨sendPlace 5, 0⟩, 0, ⟨0, K14.dueOf (K14.jobOmega ⟨QK, 0⟩).Q.codes
      ((K14.jobOmega ⟨QK, 0⟩).Q.sent.getD 0 default).shape ((K14.jobOmega ⟨QK, 0⟩).sort 0)⟩),
   (⟨sendPlace 5, 0⟩, 1, ⟨0, K14.dueOf (K14.jobOmega ⟨QK, 0⟩).Q.codes
      ((K14.jobOmega ⟨QK, 0⟩).Q.sent.getD 1 default).shape ((K14.jobOmega ⟨QK, 0⟩).sort 1)⟩)]

theorem foldedMembers_written : foldedMembers = AtPublicFiles.KeyTest.jobFolded.members := by decide +kernel

theorem omegaMembers_written : omegaMembers = AtPublicFiles.KeyTest.jobOmega.members := by decide +kernel

theorem foldedFresh_written : AtPublicFiles.KeyTest.jobFolded.fresh = some (⟨sendPlace 2, 0⟩, 1) := by
  decide +kernel

/-- The numbers of the place of the test on G_omega are the written ones. -/
theorem omegaNumbers_written : H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (PF.O.getD PF.U) = piKOFull := rfl

theorem foldedStages_two : 2 ≤ piKUFull.nums.stages.length := by decide +kernel

theorem omegaStages_two : 2 ≤ piKOFull.nums.stages.length := by decide +kernel

/-- k = h + g at the first stage of the test on G_omega. -/
theorem omegaFirst_splits : (piKOFull.nums.stages.headD default).k =
    (sgOf (piKOFull.nums.stages.headD default)).h + (sgOf (piKOFull.nums.stages.headD default)).g := by
  decide +kernel

/-- The place declares rounds enough for the first part. -/
theorem omegaEnough_written :
    firstLen piKOFull.nums.stages ≤ (H2K.JointK.laidOf piKOFull).length := by decide +kernel

theorem writtenShape_splits : QK.S.sharedSplitNeeded = true := by decide +kernel

/-- A list of two or more begins with two. -/
theorem two_in_front {α : Type} {l : List α} (h : 2 ≤ l.length) : ∃ a b r, l = a :: b :: r := by
  match l, h with
  | a :: b :: r, _ => exact ⟨a, b, r, rfl⟩

/-! ## The prover's list and the description's list -/

/-- No two halves of the prover's shared list stand at one place. -/
theorem shared_nodup {W₀ Rc X₀ X Wk : Type} (K : KeyParts W₀ Rc X₀ X Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace)
    (hO : K.onOmega.place = omegaTestPlace) : ((keyProver K).shared.map (·.place)).Nodup := by
  rw [keyProver_shared K hsp, hU, hO]
  decide

/-- The half of the shared list at ⟨2, –, 10⟩ is the letter `onOmega`. -/
theorem half_at_omegaTest {W₀ Rc X₀ X Wk : Type} (K : KeyParts W₀ Rc X₀ X Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace)
    (hO : K.onOmega.place = omegaTestPlace) {g : Placed Empty (Common W₀ Rc TableKey) X₀}
    (hg : g ∈ (keyProver K).shared) (hp : g.place = omegaTestPlace) : g = K.onOmega :=
  List.inj_on_of_nodup_map (shared_nodup K hsp hU hO) hg
    (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)) (hp.trans hO.symm)

/-- **The prover's shared list finds its two last halves at their places.** -/
theorem shared_finds {W₀ Rc X₀ X Wk : Type} (K : KeyParts W₀ Rc X₀ X Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace)
    (hO : K.onOmega.place = omegaTestPlace) :
    ((keyProver K).shared.find? fun g => g.place == foldedTestPlace) = some K.onU ∧
      ((keyProver K).shared.find? fun g => g.place == omegaTestPlace) = some K.onOmega := by
  have hn := shared_nodup K hsp hU hO
  have mU : K.onU ∈ (keyProver K).shared := List.mem_append_right _ List.mem_cons_self
  have mO : K.onOmega ∈ (keyProver K).shared :=
    List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have fU : ((keyProver K).shared.find? fun g => g.place == K.onU.place) = some K.onU :=
    OnBytes.SendSim.Seat.find_of_nodup
      (fun g : Placed Empty (Common W₀ Rc TableKey) X₀ => g.place) _ hn _ mU
  have fO : ((keyProver K).shared.find? fun g => g.place == K.onOmega.place) = some K.onOmega :=
    OnBytes.SendSim.Seat.find_of_nodup
      (fun g : Placed Empty (Common W₀ Rc TableKey) X₀ => g.place) _ hn _ mO
  rw [hU] at fU
  rw [hO] at fO
  exact ⟨fU, fO⟩

section Scope
variable {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums}

/-- In scope no two sub-protocols of the shared list stand at one place. -/
theorem sharedPlaces_nodup (hs : KeySourced Z Xs N PF) (scope : InScope Z = true) :
    ((flat₂ Xs.chains PF).map (·.place)).Nodup := by
  have h : rowsOf (flat₂ Xs.chains PF) = fullShared := (places_named scope hs.named).2.1
  have e : (flat₂ Xs.chains PF).map (·.place) = fullShared.map (·.1) := by
    rw [← h]
    unfold rowsOf
    rw [List.map_map]
    rfl
  rw [e]
  decide

theorem keyGu_place : (keyGu PF).place = foldedTestPlace :=
  (seatOf_inside (Cl := Unit) (jobKU (W₀ := Unit) (Rc := Unit) (X := Unit) ⟨QK, 0⟩
    (H2U.proximityTestParametersAt foldedTestPlace PF.U) [] (fun _ _ _ _ => none) (fun _ => ⟨fun _ _ => 0⟩)
    (fun _ => ⟨fun _ _ => 0, fun _ _ => 0⟩)).toRun.toTest (Seat.enter (·.gU) (·.firstMask))
    Seat.leave).place.trans (place_p12At _ _)

theorem keyOmega_place : (keyOmega (PF.O.getD PF.U)).place = omegaTestPlace :=
  (seatOf_inside (Cl := Unit) (jobKO (W₀ := Unit) (Rc := Unit) (X := Unit) ⟨QK, 0⟩
    (H2U.proximityTestParametersAt foldedTestPlace PF.U) (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) []
    (fun _ => ⟨fun _ _ => 0⟩) (fun _ => ⟨fun _ _ => 0, fun _ _ => 0⟩)).toRun.toTest
    (Seat.enter (·.gOmega) fun _ => none) Seat.leave).place.trans (place_p12At _ _)

theorem keyGu_member (c : OnBytes.Model.Verify.Chains) : keyGu PF ∈ flat₂ c PF := by
  show keyGu PF ∈ ((VerifiableInference.Desc.Key.sharedChain c PF).retype
    (Cl' := VerifiableInference.Desc.Key.Claim)).blocksInOrder
  rw [keyShared_cut]
  exact List.mem_append_right _ List.mem_cons_self

theorem keyOmega_member (c : OnBytes.Model.Verify.Chains) :
    keyOmega (PF.O.getD PF.U) ∈ flat₂ c PF := by
  show keyOmega (PF.O.getD PF.U) ∈ ((VerifiableInference.Desc.Key.sharedChain c PF).retype
    (Cl' := VerifiableInference.Desc.Key.Claim)).blocksInOrder
  rw [keyShared_cut_omega c PF _ omega_full]
  exact List.mem_append_right _ List.mem_cons_self

/-- **In scope the sub-protocol at ⟨2, –, 9⟩ is the seat of the test on G_u.** -/
theorem sharedBlock_folded (hs : KeySourced Z Xs N PF) (scope : InScope Z = true)
    (b : Block St VerifiableInference.Desc.Key.Claim) (hb : b ∈ flat₂ Xs.chains PF)
    (hp : b.place = foldedTestPlace) : b = keyGu PF :=
  List.inj_on_of_nodup_map (sharedPlaces_nodup hs scope) hb (keyGu_member _)
    (hp.trans keyGu_place.symm)

/-- **In scope the sub-protocol at ⟨2, –, 10⟩ is the seat of the test on G_omega.** -/
theorem sharedBlock_omega (hs : KeySourced Z Xs N PF) (scope : InScope Z = true)
    (b : Block St VerifiableInference.Desc.Key.Claim) (hb : b ∈ flat₂ Xs.chains PF)
    (hp : b.place = omegaTestPlace) : b = keyOmega (PF.O.getD PF.U) :=
  List.inj_on_of_nodup_map (sharedPlaces_nodup hs scope) hb (keyOmega_member _)
    (hp.trans keyOmega_place.symm)

end Scope

/-- **A TEST OF EMPTINESS.** In scope the shared list has a sub-protocol at each of the two places. -/
theorem sharedTests_there {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    (∃ b ∈ (keyFileDescription Xs N Pl).shared.blocksInOrder, b.place = foldedTestPlace) ∧
      ∃ b ∈ (keyFileDescription Xs N Pl).shared.blocksInOrder, b.place = omegaTestPlace := by
  have hPl : Pl = PF := later_sourced hs scope
  subst hPl
  exact ⟨⟨keyGu PF, keyGu_member _, keyGu_place⟩,
    ⟨keyOmega (PF.O.getD PF.U), keyOmega_member _, keyOmega_place⟩⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.foldedMembers_written
#print axioms AtPublicFiles.OfflineRows.omegaMembers_written
#print axioms AtPublicFiles.OfflineRows.foldedFresh_written
#print axioms AtPublicFiles.OfflineRows.omegaNumbers_written
#print axioms AtPublicFiles.OfflineRows.foldedStages_two
#print axioms AtPublicFiles.OfflineRows.omegaStages_two
#print axioms AtPublicFiles.OfflineRows.omegaFirst_splits
#print axioms AtPublicFiles.OfflineRows.omegaEnough_written
#print axioms AtPublicFiles.OfflineRows.writtenShape_splits
#print axioms AtPublicFiles.OfflineRows.two_in_front
#print axioms AtPublicFiles.OfflineRows.shared_nodup
#print axioms AtPublicFiles.OfflineRows.half_at_omegaTest
#print axioms AtPublicFiles.OfflineRows.shared_finds
#print axioms AtPublicFiles.OfflineRows.sharedPlaces_nodup
#print axioms AtPublicFiles.OfflineRows.keyGu_place
#print axioms AtPublicFiles.OfflineRows.keyOmega_place
#print axioms AtPublicFiles.OfflineRows.keyGu_member
#print axioms AtPublicFiles.OfflineRows.keyOmega_member
#print axioms AtPublicFiles.OfflineRows.sharedBlock_folded
#print axioms AtPublicFiles.OfflineRows.sharedBlock_omega
#print axioms AtPublicFiles.OfflineRows.sharedTests_there
