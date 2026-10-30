-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnLines.lean: CAN THE PREMISES OF THE TIE BE MET: the public ones, at the
written sizes of a key: `BookAtOwnTest` at the key file's book and `SharedPlanAtOwnTest` at the written plan
(LotOwnWords.lean), by closed lines that Lean's kernel evaluates, each with a control that says no.

  `bookLinesAtOwnTest`     `BookAtOwnTest`'s twelve clauses as one Bool, at the written sendings
  `book_lines_full`        it is true at the key file's book at the written sizes. By the kernel
  `book_lines_bare`, `book_lines_other_place`   controls: false at the book without its carried entries, and at the
                           place of the test on the ranges
  `counts_of_alike`, `carries_of_alike`   of a sending's parameters the counts and the test on a carried message read
                           the notices and the codes alone
  `book_at_own_test`       so `BookAtOwnTest` at `keyBook K₀`, at parts under `OwnSenders` (OwnJob.lean: the notices, the
                           codes and the rides of the two sendings; the shared chain's parameters)
  `plan_at_own_test`       `SharedPlanAtOwnTest` at parts under `OwnSenders`
  `numbersAtFullSize`      the six numbers at the full size, but for the two counts of challenges, which are letters

Limits.
- At written values: `fullPub`, `parIK`, `parWK`, `rideW`, `QK`, `piKWFull`. That a run's book is this one is the caller's.
- `SendersReadInFront`, `StatementAtOwnTest`, `HeardAtOwnTest` are not treated here.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnWords
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnJob
import E2E.KeyDoorUClosedKernel
import E2E.KeyShapeSharedTies
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapesLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (LaterPlaces)
open H2K.Member (piKWFull)
open AtPublicFiles.KeyBook (KeyPub keyBook atFull fullPub rideW)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyTest (sIdx sW jobRanges)
open AtPublicFiles.KeyLay (parIK parWK pWK)
open AtPublicFiles.AtFiles.Full (QK)
open ProofFile.Honest.K12.Light (cutFits)
open ProofFile.Honest.K12.AtFile (ellOmegaB)

/-- **`BookAtOwnTest`'s clauses as one Bool, at the written sendings.** -/
def bookLinesAtOwnTest (Bk : ProverCoinCounts) (place : Place) : Bool :=
  carriesMessage Bk ⟨place, 1⟩ 0 sIdx parIK (fun _ => none) (parIK.sent.size - 1) &&
    carriesMessage Bk ⟨place, 1⟩ 1 sW parWK rideW 0 &&
    cutFits Bk ⟨place, 1⟩ 2 ⟨K14.sendPlace 5, 0⟩ (K14.jobOmega ⟨QK, 0⟩) 0 &&
    (dueAt Bk.first sIdx == K1.dueR parIK fun _ => none) &&
    (dueAt Bk.first sW == K1.dueR parWK rideW) &&
    (dueAt Bk.shared ⟨K14.sendPlace 5, 0⟩ == (K14.sendingPart (K14.jobOmega ⟨QK, 0⟩)).takes) &&
    !(Bk.shared.any fun r => r.1 == sIdx) && !(Bk.second.any fun r => r.1 == sIdx) &&
    !(Bk.shared.any fun r => r.1 == sW) && !(Bk.second.any fun r => r.1 == sW) &&
    !(Bk.first.any fun r => r.1 == (⟨K14.sendPlace 5, 0⟩ : Addr)) &&
    !(Bk.second.any fun r => r.1 == (⟨K14.sendPlace 5, 0⟩ : Addr))

/-- **The lines hold at the key file's book at the written sizes.** By the kernel. -/
theorem book_lines_full :
    atFull (fun K => bookLinesAtOwnTest (keyBook K) piKWFull.place) = true := by
  decide +kernel

/-- Control: the book without its carried entries. -/
theorem book_lines_bare :
    atFull (fun K => !bookLinesAtOwnTest (keyBook K false) piKWFull.place) = true := by
  decide +kernel

/-- Control: another test's place. -/
theorem book_lines_other_place :
    atFull (fun K => !bookLinesAtOwnTest (keyBook K) jobRanges.p.place) = true := by
  decide +kernel

/-- Of a sending's parameters the counts read the codes and the notices alone. -/
theorem counts_of_alike {P Q : VerifiableInference.Desc.K1.Par} (hs : P.sent = Q.sent)
    (hc : P.codes = Q.codes) (ride : ℕ → Option K1.Ride) :
    K1.dueR P ride = K1.dueR Q ride ∧ (∀ k, K1.startR P ride k = K1.startR Q ride k) ∧
      ∀ k, Johnson.Prover.Send.shapeAt P k = Johnson.Prover.Send.shapeAt Q k := by
  refine ⟨?_, fun k => ?_, fun k => ?_⟩
  · unfold K1.dueR K1.startR Johnson.Prover.Send.shapeAt
    rw [hs, hc]
  · unfold K1.startR Johnson.Prover.Send.shapeAt
    rw [hs, hc]
  · unfold Johnson.Prover.Send.shapeAt
    rw [hs]

/-- The test on a carried message reads them alone. -/
theorem carries_of_alike {P Q : VerifiableInference.Desc.K1.Par} (hs : P.sent = Q.sent)
    (hc : P.codes = Q.codes) (Bk : ProverCoinCounts) (spender : Addr) (n : ℕ) (sender : Addr)
    (ride : ℕ → Option K1.Ride) (message : ℕ) :
    carriesMessage Bk spender n sender P ride message =
      carriesMessage Bk spender n sender Q ride message := by
  obtain ⟨-, h2, h3⟩ := counts_of_alike hs hc ride
  unfold carriesMessage
  rw [h2 message, h3 message, hc]

variable {W₀ Rc X₀ X Wk : Type} {K : KeyParts W₀ Rc X₀ X Wk}

/-- **`BookAtOwnTest` at the key file's book.** -/
theorem book_at_own_test {K₀ : KeyPub} (hK₀ : fullPub = some K₀) (h : OwnSenders K)
    {Pl : LaterPlaces} (hPl : pWK Pl = piKWFull) :
    BookAtOwnTest (keyBook K₀) K (pWK Pl).place := by
  have b := book_lines_full
  unfold atFull at b
  rw [hK₀] at b
  have b' : bookLinesAtOwnTest (keyBook K₀) piKWFull.place = true := b
  unfold bookLinesAtOwnTest at b'
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at b'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, r0⟩, r1⟩, r2⟩, n0⟩, n1⟩, n2⟩, n3⟩, n4⟩, n5⟩ := b'
  rw [hPl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, n0, n1, n2, n3, n4, n5⟩
  · rw [carries_of_alike h.idxSent h.idxCodes, h.idxRide, h.idxSent]
    exact c0
  · rw [carries_of_alike h.wSent h.wCodes, h.wRide]
    exact c1
  · rw [h.sendPar]
    exact c2
  · rw [(counts_of_alike h.idxSent h.idxCodes _).1, h.idxRide]
    exact r0
  · rw [(counts_of_alike h.wSent h.wCodes _).1, h.wRide]
    exact r1
  · rw [h.sendPar]
    exact r2

/-- The code of Omega's main rows at the written plan. By the kernel. -/
theorem length_full : ellOmegaB ⟨QK, 0⟩ = true := by decide +kernel

/-- **`SharedPlanAtOwnTest` at the written plan.** -/
theorem plan_at_own_test (h : OwnSenders K) : SharedPlanAtOwnTest K.send.P := by
  rw [h.sendPar]
  exact ⟨ProofFile.Honest.K12.Light.KeyDoorUClosed.sendings_U, length_full,
    AtPublicFiles.AtFiles.Full.plan2_full,
    K14.sendShapes_of_fit ProofFile.Honest.K12.Light.KeyDoorUClosed.sendings_U⟩

/-- **The numbers at the full size.** The two counts of challenges in front of W's sending and of the first chain
are arguments. -/
def numbersAtFullSize (challengesBeforeVectorW challengesOfFirstChain : ℕ) : OwnTestNumbers :=
  { indexMasksFirst := 0, vectorWFirst := 9, omegaCopy := 11, challengesBeforeIndexMasks := 0
    challengesBeforeVectorW := challengesBeforeVectorW
    challengesOfFirstChain := challengesOfFirstChain }

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.bookLinesAtOwnTest
#print axioms ProofFile.Honest.K12.AtKey.book_lines_full
#print axioms ProofFile.Honest.K12.AtKey.book_lines_bare
#print axioms ProofFile.Honest.K12.AtKey.book_lines_other_place
#print axioms ProofFile.Honest.K12.AtKey.counts_of_alike
#print axioms ProofFile.Honest.K12.AtKey.carries_of_alike
#print axioms ProofFile.Honest.K12.AtKey.book_at_own_test
#print axioms ProofFile.Honest.K12.AtKey.length_full
#print axioms ProofFile.Honest.K12.AtKey.plan_at_own_test
#print axioms ProofFile.Honest.K12.AtKey.numbersAtFullSize
