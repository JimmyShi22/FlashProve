-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/OwnProofBook.lean: row W's tests on the book, at the written entries
rawAheadW, by Lean's kernel: the entries that the own test's second part carries: number 0 is the
index-mask message of the opening, 1 and 3 W's two messages, 2 Omega's message; and Omega's sender has no
row of the first chain. The twin of OwnKeyBook.lean at the proof file.

  own_proof_short   the four at the written pieces of the entries, and the rows
  carried_own       the part's carried entries are those of the written pieces
  own_proof_at      at any book with these entries and first rows, at plans by codes and messages

Limits: written values. No property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowFoldedPub
import AtFullSide.K12.TiesAtLaid
import Johnson.HB.LLHARD.PlanAtQFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Sim2
open ProofFile.Honest ProofFile.Honest.K12 AtFullSide.K14
open ProofFile.Honest.K12.AtProof (placeW senderI senderW senderO)
open VerifiableInference.Desc.K1 (qFull firstPar parW)
open VerifiableInference.Desc.K13.Law (gpFull wMsgFull)

/-- The plans at the written values. -/
abbrev planW : K14.SendPub := Light.planOf qFull.codes qFull.lin
abbrev P0W : VerifiableInference.Desc.K1.Par := firstPar qFull gpFull
abbrev PWW : VerifiableInference.Desc.K1.Par := parW qFull gpFull 4 wMsgFull
abbrev rideI := K1.rideOf (K1.firstFold qFull)
abbrev rideWW := K1.rideOf (K1.wFold qFull.lin)

/-- A book of the written pieces alone. -/
abbrev bkS : ProverCoinCounts := ⟨[], [], [], rawShortW, []⟩

set_option maxHeartbeats 0 in
theorem own_proof_short :
    (k1CutFits bkS ⟨placeW, 1⟩ 0 senderI P0W rideI 4 &&
      k1CutFits bkS ⟨placeW, 1⟩ 1 senderW PWW rideWW 0 &&
      k1CutFits bkS ⟨placeW, 1⟩ 3 senderW PWW rideWW 1 &&
      Light.cutFits bkS ⟨placeW, 1⟩ 2 senderO (K14.jobOmega planW) 0 &&
      rawRowsFirstW.all fun r => r.1 != senderO) = true := by
  decide +kernel

theorem carried_own {Bk : ProverCoinCounts} (hA : Bk.ahead = rawAheadW) :
    Light.carriedOf Bk ⟨placeW, 1⟩ = Light.carriedOf bkS ⟨placeW, 1⟩ := by
  unfold Light.carriedOf
  rw [hA]
  show ((rawAheadW.filter fun e => e.spender == ⟨placeW, 1⟩).filter _) = _
  rw [AtFullSide.K12.ahead_at ⟨placeW, 1⟩ (by decide)]

theorem k1CutFits_carried {B B' : ProverCoinCounts} {a : Addr} (h : Light.carriedOf B a = Light.carriedOf B' a)
    (n : ℕ) (s : Addr) (Q : VerifiableInference.Desc.K1.Par) (ride : ℕ → Option K1.Ride) (kk : ℕ) :
    k1CutFits B a n s Q ride kk = k1CutFits B' a n s Q ride kk := by
  unfold k1CutFits
  rw [h]

theorem cutFits_carried {B B' : ProverCoinCounts} {a : Addr} (h : Light.carriedOf B a = Light.carriedOf B' a)
    (n : ℕ) (s : Addr) (J : _) (k : ℕ) :
    Light.cutFits B a n s J k = Light.cutFits B' a n s J k := by
  unfold Light.cutFits
  rw [h]

/-- **Row W's tests on the book, at any book with these entries and first rows.** -/
theorem own_proof_at {Bk : ProverCoinCounts} (hA : Bk.ahead = rawAheadW) (hF : Bk.first = rawRowsFirstW)
    {PI PW : VerifiableInference.Desc.K1.Par}
    (hIc : PI.codes = P0W.codes) (hIs : PI.sent = P0W.sent)
    (hWc : PW.codes = PWW.codes) (hWs : PW.sent = PWW.sent) (A : K14.SendPub)
    (hAc : A.P.codes = qFull.codes) (hAS : A.P.S = qFull.lin) :
    k1CutFits Bk ⟨placeW, 1⟩ 0 senderI PI rideI 4 = true ∧
      k1CutFits Bk ⟨placeW, 1⟩ 1 senderW PW rideWW 0 = true ∧
      k1CutFits Bk ⟨placeW, 1⟩ 3 senderW PW rideWW 1 = true ∧
      Light.cutFits Bk ⟨placeW, 1⟩ 2 senderO (K14.jobOmega A) 0 = true ∧
      ∀ r ∈ Bk.first, r.1 ≠ senderO := by
  have e := own_proof_short
  simp only [Bool.and_eq_true] at e
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := e
  have hc := carried_own hA
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [k1CutFits_carried hc, k1CutFits_congr _ _ _ _ hIc hIs]
    exact h1
  · rw [k1CutFits_carried hc, k1CutFits_congr _ _ _ _ hWc hWs]
    exact h2
  · rw [k1CutFits_carried hc, k1CutFits_congr _ _ _ _ hWc hWs]
    exact h3
  · rw [cutFits_carried hc]
    show Light.cutFits bkS ⟨placeW, 1⟩ 2 senderO (K14.jobOmega (Light.planOf A.P.codes A.P.S)) 0 = true
    rw [hAc, hAS]
    exact h4
  · rw [hF] at hr
    have := List.all_eq_true.1 h5 r hr
    simpa using this

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.own_proof_at
