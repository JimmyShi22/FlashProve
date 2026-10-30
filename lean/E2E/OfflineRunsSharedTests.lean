-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsSharedTests.lean: WHAT ONE SUB-PROTOCOL OWES for "every run returns" (`BlockPlays`, E2E/OfflineRunsForm.lean)
AT THE SHARED CHAIN's TWO PROXIMITY TESTS of the key file: the test on G_u at ⟨2, –, 9⟩ and the test on G_omega at
⟨2, –, 10⟩, at the written book and at the offline prover's own senders (`valueAt`, E2E/KeyValueHolds.lean).

The two general laws are E2E/OfflineRunsK12.lean's; the ties of letters are E2E/OfflineSharedTestsTies.lean's. No thread is named.

  `foldedTest_blockPlays`   at the block `keyGu PF`, at every list of halves that finds `proverSideOfTestOnU` at the place,
                            at every eight, stored columns and readers, from every form of the state
  `omegaTest_blockPlays`    at the block `keyOmega …`, the half being `proverSideOfTestOnOmega` (behind the guard), from every form that says
                            that columns are handed
  `sharedTests_blockPlays_at_value`   the two joined, at `valueAt`
  `sharedTests_shared_at_value`       in the form of the field `BlocksPlay.shared`: from `MidForm`

By what. That each message has its declared shape is `fits_all` under the plan's two clauses (`planPlays_KU`,
`planPlays_KO`: the kernel on the written numbers); that the two parts' readers agree at the coins that the book lends is
`agree_at_U`, `agree_at_O` (the book's ties, at every input and front). These four stand in
Johnson/Desc/ProofFile/Honest/K12/PlanAtKeyKernel.lean and AgreeAtKey.lean. The guard's one fault is paid by the form's
clause that columns are handed.

Limits. At the written sizes, under `fullPub = some K₀`, `KeySourced` and `InScope`. `BlockPlays` holds for nothing where
`chainSteps` at the block does not return: that it returns is not said here. What is played is not said: the jobs'
states on entry may be their fall-backs. Nothing is assumed on fresh coins and no law over coins is stated. Nothing on
the columns, on a decision, on completeness, on soundness or on what is hidden.
-/
import E2E.OfflineRunsK12
import E2E.OfflineSharedTestsTies

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

/-! ## The two tests, at letters -/

section Letters
variable {W₀ Rc X₀ : Type} (K₀ : KeyPub) (hK₀ : fullPub = some K₀)

include hK₀ in
/-- **`play` returns at the test on G_u**, from every form of the state. -/
theorem foldedTest_blockPlays (A : SendPub) (hA : A = ⟨QK, 0⟩)
    (hs : List (Placed Empty (Common W₀ Rc TableKey) X₀)) (bs : List (Block St Unit))
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64)) (weights : Common W₀ Rc TableKey → Weights)
    (rand : Common W₀ Rc TableKey → TableRand)
    (hf : (hs.find? fun g => g.place == foldedTestPlace) =
      some (proverSideOfTestOnU A (H2U.proximityTestParametersAt foldedTestPlace PF.U) bs st weights rand))
    (Pre : Mid (Common W₀ Rc TableKey) X₀ → Prop) :
    BlockPlays .shared (keyBook K₀) 1 hs (keyGu PF) Pre := by
  subst hA
  have hp : (jobKU (X := X₀) ⟨QK, 0⟩ (H2U.proximityTestParametersAt foldedTestPlace PF.U) bs st weights
      rand).toRun.toTest.p = piKUFull := place_full
  have hseat : SeatOf (keyGu PF) (jobKU (X := X₀) ⟨QK, 0⟩ (H2U.proximityTestParametersAt foldedTestPlace PF.U) bs st weights
      rand).toRun.toTest (Seat.enter (·.gU) (·.firstMask)) Seat.leave := by
    have h := seatOf_inside (Cl := Unit) (jobKU (X := X₀) ⟨QK, 0⟩ (H2U.proximityTestParametersAt foldedTestPlace PF.U) bs st
      weights rand).toRun.toTest (Seat.enter (·.gU) (·.firstMask)) Seat.leave
    exact ⟨h.place, h.rounds, h.oracles, h.decide⟩
  obtain ⟨s, t, rest, hst⟩ := two_in_front (l := (jobKU (X := X₀) ⟨QK, 0⟩
      (H2U.proximityTestParametersAt foldedTestPlace PF.U) bs st weights rand).toRun.toTest.p.nums.stages) (by
                        rw [hp]
                        exact foldedStages_two)
  have hk : s.k = (sgOf s).h + (sgOf s).g := by
    have h := first_k_U
    rw [← hp, hst] at h
    exact h
  have P := PlanAtKey.planPlays_KU _ hp rfl s (t :: rest) hst
  have hpl : (jobKU (X := X₀) ⟨QK, 0⟩ (H2U.proximityTestParametersAt foldedTestPlace PF.U) bs st weights
      rand).toRun.toTest.p.place = foldedTestPlace := place_p12At _ _
  refine blockPlays_k12 .shared (keyBook K₀) 1 hs (keyGu PF) _ _ _ hseat Pre s t rest hst hk ?_
    P.plan P.sorts P.tables ?_
  · rw [hpl]
    exact hf
  · intro k m c _ hc
    exact agree_at_U K₀ hK₀ (jobKU (X := X₀) ⟨QK, 0⟩ (H2U.proximityTestParametersAt foldedTestPlace PF.U) bs st weights rand)
      hp foldedMembers_written foldedFresh_written.symm _ _ c hc _ _

include hK₀ in
/-- **`play` returns at the test on G_omega**, from every form that says that columns are handed. -/
theorem omegaTest_blockPlays (A : SendPub) (hA : A = ⟨QK, 0⟩)
    (hs : List (Placed Empty (Common W₀ Rc TableKey) X₀)) (pU : P12) (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (hf : (hs.find? fun g => g.place == omegaTestPlace) =
      some (proverSideOfTestOnOmega A pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand))
    (Pre : Mid (Common W₀ Rc TableKey) X₀ → Prop) (hopen : ∀ m, Pre m → m.opened.isSome = true) :
    BlockPlays .shared (keyBook K₀) 1 hs (keyOmega (PF.O.getD PF.U)) Pre := by
  subst hA
  have hp : (jobKO (X := X₀) ⟨QK, 0⟩ pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights
      rand).toRun.toTest.p = piKOFull := omegaNumbers_written
  have hseat : SeatOf (keyOmega (PF.O.getD PF.U)) (jobKO (X := X₀) ⟨QK, 0⟩ pU
      (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand).toRun.toTest
      (Seat.enter (·.gOmega) fun _ => none) Seat.leave := by
    have h := seatOf_inside (Cl := Unit) (jobKO (X := X₀) ⟨QK, 0⟩ pU
      (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand).toRun.toTest
      (Seat.enter (·.gOmega) fun _ => none) Seat.leave
    exact ⟨h.place, h.rounds, h.oracles, h.decide⟩
  obtain ⟨s, t, rest, hst⟩ := two_in_front (l := (jobKO (X := X₀) ⟨QK, 0⟩ pU
      (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand).toRun.toTest.p.nums.stages) (by
                        rw [hp]
                        exact omegaStages_two)
  have hk : s.k = (sgOf s).h + (sgOf s).g := by
    have h := omegaFirst_splits
    rw [← hp, hst] at h
    exact h
  have P := PlanAtKey.planPlays_KO _ hp rfl s (t :: rest) hst
  have hpl : (jobKO (X := X₀) ⟨QK, 0⟩ pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights
      rand).toRun.toTest.p.place = omegaTestPlace := place_p12At _ _
  refine blockPlays_k12_guarded .shared (keyBook K₀) 1 hs (keyOmega (PF.O.getD PF.U)) _ _ _ hseat Pre s t
    rest hst hk ?_ P.plan P.sorts P.tables hopen ?_
  · rw [hpl]
    exact hf
  · intro k m c _ hc
    exact agree_at_O K₀ hK₀ (jobKO (X := X₀) ⟨QK, 0⟩ pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs
      weights rand) hp omegaMembers_written fresh_none_O.symm _ _ c hc _ _

end Letters

/-! ## At the offline prover's own senders -/

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- **`BlockPlays` at the shared chain's two proximity tests, at the offline prover's own senders**, at the written
book, from every form of the state that says that columns are handed. -/
theorem sharedTests_blockPlays_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) {K₀ : KeyPub} (hK₀ : fullPub = some K₀)
    (b : Block (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl) (hb : b ∈ (keyFileDescription Xs N Pl).shared.blocksInOrder)
    (hp : b.place = foldedTestPlace ∨ b.place = omegaTestPlace)
    (Pre : Mid (Common W₀ Rc TableKey) Unit → Prop) (hopen : ∀ m, Pre m → m.opened.isSome = true) :
    BlockPlays .shared (keyBook K₀) 1
      (keyProver (valueAt K' Xs N Pl f g inR d (H2U.proximityTestParametersAt foldedTestPlace Pl.U)
        (H2U.proximityTestParametersAt omegaTestPlace (Pl.O.getD Pl.U)) ent groups first)).shared b Pre := by
  have hPl : Pl = PF := later_sourced hs scope
  subst hPl
  have e : parKey Xs PF = QK := par_sourced hs scope
  have hA : (⟨parKey Xs PF, 0⟩ : SendPub) = ⟨QK, 0⟩ := by rw [e]
  have hsp : (valueAt K' Xs N PF f g inR d (H2U.proximityTestParametersAt foldedTestPlace PF.U)
      (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) ent groups first).lin.S.sharedSplitNeeded = true := by
    show (parKey Xs PF).S.sharedSplitNeeded = true
    rw [e]
    exact writtenShape_splits
  obtain ⟨fU, fO⟩ := shared_finds (valueAt K' Xs N PF f g inR d (H2U.proximityTestParametersAt foldedTestPlace PF.U)
    (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) ent groups first) hsp (place_p12At _ _)
    (place_p12At _ _)
  rcases hp with hp | hp
  · obtain rfl := sharedBlock_folded hs scope b hb hp
    exact foldedTest_blockPlays K₀ hK₀ _ hA _ _ _ _ _ fU Pre
  · obtain rfl := sharedBlock_omega hs scope b hb hp
    exact omegaTest_blockPlays K₀ hK₀ _ hA _ _ _ _ _ fO Pre hopen

/-- **The two tests' share of `BlocksPlay.shared`** (E2E/OfflineRunsForm.lean), from that field's own form of the
state. -/
theorem sharedTests_shared_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) {K₀ : KeyPub} (hK₀ : fullPub = some K₀)
    (common : Common W₀ Rc TableKey) :
    ∀ j b, (keyFileDescription Xs N Pl).shared.blocksInOrder[j]? = some b →
      (b.place = foldedTestPlace ∨ b.place = omegaTestPlace) →
      BlockPlays .shared (keyBook K₀) 1
        (keyProver (valueAt K' Xs N Pl f g inR d (H2U.proximityTestParametersAt foldedTestPlace Pl.U)
          (H2U.proximityTestParametersAt omegaTestPlace (Pl.O.getD Pl.U)) ent groups first)).shared b
        (MidForm startNone (roundsIn (keyFileDescription Xs N Pl).shared.blocksInOrder j) common) :=
  fun _ b hj hp => sharedTests_blockPlays_at_value K' Xs N Pl f g inR d ent groups first hs scope hK₀ b
    (List.mem_of_getElem? hj) hp _ fun _ h => h.opened

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.foldedTest_blockPlays
#print axioms AtPublicFiles.OfflineRows.omegaTest_blockPlays
#print axioms AtPublicFiles.OfflineRows.sharedTests_blockPlays_at_value
#print axioms AtPublicFiles.OfflineRows.sharedTests_shared_at_value
