-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineSharedTestsAtBlocks.lean: WHAT IS ASKED OF THE PLACE (`TestAtBlock`, E2E/OfflineSayOfThreads.lean) at the shared chain's two
proximity tests: the sub-protocol's rounds are the job's, the job's public part is as the text asks, and its two
parts have as many moves as the sub-protocol has rounds, the second at least one.

  `foldedCounts_written`, `omegaCounts_written`   the written numbers: rounds, the first part's, the second part's. By evaluation
  `testAtBlock_of_seat`   general: from the seat (`SeatOf`), the plan's three clauses, two stages in front, the counts
  `foldedTest_atBlock`    at the seat of the test on G_u and every job at the written place whose first fold rides
  `omegaTest_atBlock`     at the seat of the test on G_omega and every job at the written place with its own table

Public numbers and shapes alone: no run, no coin, no input. Nothing on any property.
-/
import E2E.OfflineSayOfThreads
import E2E.OfflineSharedTestsTies
import Johnson.Desc.ProofFile.Honest.K12.PlaysK12

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K14 (SendPub)
open OnBytes (TableKey)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.enter Seat.leave)
open Johnson.Prover.Link (asked bodyItems)
open _root_.Desc.K14 (St)
open H2K.Pub (sgOf)
open H2K.Member (piKUFull piKOFull)
open H2K.JointK (keyGu keyOmega laidOf)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.KeyBook (foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyLay (jobKU jobKO)
open AtPublicFiles.KeyNineClosed (place_full)

/-- The written numbers at the test on G_u. By evaluation. -/
theorem foldedCounts_written :
    (laidOf piKUFull).length = firstLen piKUFull.nums.stages + restLen piKUFull.nums.stages ∧
      restLen piKUFull.nums.stages ≠ 0 := by decide +kernel

/-- The written numbers at the test on G_omega. By evaluation. -/
theorem omegaCounts_written :
    (laidOf piKOFull).length = firstLen piKOFull.nums.stages + restLen piKOFull.nums.stages ∧
      restLen piKOFull.nums.stages ≠ 0 := by decide +kernel

section General
variable {S Cl W X : Type}

/-- **`TestAtBlock` from the seat, the plan's clauses and the counts.** -/
theorem testAtBlock_of_seat {b : Block S Cl} {J : TestJob W X} {enter : S → Except String T12}
    {leave : S → T12 → Except String S} (hb : SeatOf b J enter leave) {s t : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} (hst : J.p.nums.stages = s :: t :: rest)
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (plan : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).planOk = true)
    (sorts : (laidOf J.p).map asked = [] :: bodyItems s (t :: rest)) (tables : tablesFitB J = true)
    (lists : b.oracles.length = b.rounds.length)
    (count : (laidOf J.p).length = firstLen J.p.nums.stages + restLen J.p.nums.stages)
    (second : restLen J.p.nums.stages ≠ 0) : TestAtBlock J b s t rest where
  pub := ⟨hst, hk, by omega, sorts, tables⟩
  laid := by
    rw [hb.rounds, hb.oracles]
    exact zip_laid J.p plan
  lists := lists
  count := count
  second := second

end General

variable {W₀ Rc X₀ : Type}

/-- **At the seat of the test on G_u.** -/
theorem foldedTest_atBlock (A : SendPub) (hA : A = ⟨QK, 0⟩) (bs : List (Block St Unit))
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64)) (weights : Common W₀ Rc TableKey → Weights)
    (rand : Common W₀ Rc TableKey → TableRand)
    (lists : (keyGu PF).oracles.length = (keyGu PF).rounds.length) :
    ∃ s t rest, TestAtBlock (jobKU (X := X₀) A (H2U.proximityTestParametersAt foldedTestPlace PF.U) bs st weights
      rand).toRun.toTest (keyGu PF) s t rest := by
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
  exact ⟨s, t, rest, testAtBlock_of_seat hseat hst hk P.plan P.sorts P.tables lists
    (by rw [hp]; exact foldedCounts_written.1) (by rw [hp]; exact foldedCounts_written.2)⟩

/-- **At the seat of the test on G_omega.** -/
theorem omegaTest_atBlock (A : SendPub) (hA : A = ⟨QK, 0⟩) (pU : P12) (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (lists : (keyOmega (PF.O.getD PF.U)).oracles.length = (keyOmega (PF.O.getD PF.U)).rounds.length) :
    ∃ s t rest, TestAtBlock (jobKO (X := X₀) A pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs
      weights rand).toRun.toTest (keyOmega (PF.O.getD PF.U)) s t rest := by
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
  exact ⟨s, t, rest, testAtBlock_of_seat hseat hst hk P.plan P.sorts P.tables lists
    (by rw [hp]; exact omegaCounts_written.1) (by rw [hp]; exact omegaCounts_written.2)⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.foldedCounts_written
#print axioms AtPublicFiles.OfflineRows.omegaCounts_written
#print axioms AtPublicFiles.OfflineRows.testAtBlock_of_seat
#print axioms AtPublicFiles.OfflineRows.foldedTest_atBlock
#print axioms AtPublicFiles.OfflineRows.omegaTest_atBlock
