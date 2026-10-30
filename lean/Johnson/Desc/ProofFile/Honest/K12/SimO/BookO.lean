-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the proximity test on G_omega: the tests on the book at the maker's book.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/BookO.lean: the two public tests on the book at the test on G_omega: `tiesOB` (K12/Own/AgreeOwn.lean) and `bookCutsOmega` (K12/CutOfBookAt.lean), at the written list of the book's entries, by Lean's kernel behind `ahead_at`; so at whatever book the maker returns, under the head. The road of AtFullSide/K12/CutsAtLaid.lean and CutsAtHead.lean.

  `tiesO_written`, `carried_O_written`   at `rawAheadW`
  `omegaNumbersB`, `omegaNumbers_real`, `omegaNumbers_head`   two numbers of the sending of o_omega
  `bookCutsOmega_of_numbers`, `ahead_of_laid`, `bookCutsOmega_head`, `tiesO_head`   at the maker's book

Limits. The full size alone. That the maker returns a book is a premise (hB). No property of the protocol is claimed.
-/
import AtFullSide.K12.CutsAtHead
import Johnson.Desc.ProofFile.Honest.K12.Own.AgreeOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block Chain K1.qAt)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K12 (P12)
open ProofFile.Honest (ProverCoinCounts Addr Ahead Due bookWhole mergesByName carryE)
open ProofFile.Honest.K14 (SendPub jobOmega offsetOf dueOf takesOf sendPlace)
open AtFullSide.K14 (rawAheadW)
open AtFullSide.K12 (ahead_at)
open Johnson.G (proofSendsFull codesFull2)
open ProofFile.Honest.K12.Own (tiesOB)
open ProofFile.Honest.K12.AtProof (fourOf)

theorem tiesO_written :
    tiesOB { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] }
      ⟨2, none, 10, .K12⟩ 2 = true := by
  unfold tiesOB carryE
  dsimp only
  rw [ahead_at ⟨⟨2, none, 10, .K12⟩, 0⟩ (by decide), ahead_at ⟨⟨2, none, 10, .K12⟩, 0 + 1⟩ (by decide)]
  decide +kernel

theorem carried_O_written :
    ((rawAheadW.filter fun e => e.spender == ⟨⟨2, none, 10, .K12⟩, 1⟩).filter (!·.once)).map
        (fun e => (e.owner, e.start, e.count)) =
      [(⟨sendPlace 5, 0⟩, ⟨0, 0⟩, ⟨0, 42853⟩), (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩),
        (⟨⟨2, none, 10, .K12⟩, 0⟩, ⟨0, 0⟩, ⟨0, 161⟩)] := by
  rw [ahead_at ⟨⟨2, none, 10, .K12⟩, 1⟩ (by decide)]
  decide +kernel

/-- Two numbers of the sending of o_omega. -/
def omegaNumbersB (A : SendPub) : Bool :=
  (offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 0 == 0) &&
  (dueOf (jobOmega A).Q.codes (shapeAt (jobOmega A) 0) ((jobOmega A).sort 0) == 42853)

theorem omegaNumbers_real : (realSized.all fun q => omegaNumbersB (planOf q.2 q.1.shape)) = true := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

theorem omegaNumbers_head (h : P5J.AtMg o Z D r₀ Zp Np cF) : omegaNumbersB ⟨K1.qAt Zp Np, 0⟩ = true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have k := omegaNumbers_real
  rw [hx] at k
  have k' : omegaNumbersB (planOf codesFull2 x.shape) = true := k
  have e : omegaNumbersB ⟨K1.qAt Zp Np, 0⟩ = omegaNumbersB (planOf (K1.qAt Zp Np).codes (K1.qAt Zp Np).S) := rfl
  rw [e, qAt_written Wr Np]
  exact k'

/-- **`bookCutsOmega` from the entries and the numbers.** -/
theorem bookCutsOmega_of_numbers (Bk : ProverCoinCounts)
    (hc : (carriedOf Bk ⟨⟨2, none, 10, .K12⟩, 1⟩).map (fun e => (e.owner, e.start, e.count)) =
      [(⟨sendPlace 5, 0⟩, ⟨0, 0⟩, ⟨0, 42853⟩), (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩),
        (⟨⟨2, none, 10, .K12⟩, 0⟩, ⟨0, 0⟩, ⟨0, 161⟩)])
    (A : SendPub) (p : P12) (hp : p.place = ⟨2, none, 10, .K12⟩)
    (o0 : offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 0 = 0)
    (d0 : dueOf (jobOmega A).Q.codes (shapeAt (jobOmega A) 0) ((jobOmega A).sort 0) = 42853)
    (o1 : offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 1 = 42853)
    (d1 : dueOf (jobOmega A).Q.codes (shapeAt (jobOmega A) 1) ((jobOmega A).sort 1) = 216)
    (tO : 43069 ≤ (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort).e) :
    bookCutsOmega Bk A p = true := by
  obtain ⟨e0, l1, hl, h0, hc⟩ := List.map_eq_cons_iff.1 hc
  obtain ⟨e1, l2, hl1, h1, hc⟩ := List.map_eq_cons_iff.1 hc
  subst hl1
  have a0 := congrArg (·.1) h0
  have b0 := congrArg (·.2.1) h0
  have c0 := congrArg (·.2.2) h0
  have a1 := congrArg (·.1) h1
  have b1 := congrArg (·.2.1) h1
  have c1 := congrArg (·.2.2) h1
  dsimp only at a0 b0 c0 a1 b1 c1
  unfold bookCutsOmega cutFits
  rw [hp, hl]
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, a0, b0, c0, a1, b1, c1,
    o0, d0, o1, d1, beq_self_eq_true, Bool.and_true, Bool.true_and, decide_eq_true_eq,
    Bool.and_eq_true]
  omega

section Laid
variable {Bk : ProverCoinCounts}

theorem ahead_of_laid {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF)
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk) : Bk.ahead = rawAheadW := by
  obtain ⟨B₀, h₀, hA⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  obtain rfl : B₀ = Bk :=
    Except.ok.inj ((ProofFile.Honest.K14.bookWhole_same_at_laid h₀ scope L).symm.trans hB)
  exact hA

end Laid

/-- **`bookCutsOmega` under the head, at whatever book the maker returns.** -/
theorem bookCutsOmega_head (h : P5J.AtMg o Z D r₀ Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (p : P12) (hp : p.place = ⟨2, none, 10, .K12⟩) : bookCutsOmega Bk ⟨K1.qAt Zp Np, 0⟩ p = true := by
  obtain ⟨-, -, a3, a4, -, -, -, a8⟩ := sendNumbers_of _ (sendNumbers_head h)
  have k := omegaNumbers_head h
  unfold omegaNumbersB at k
  simp only [Bool.and_eq_true, beq_iff_eq] at k
  refine bookCutsOmega_of_numbers Bk ?_ _ p hp k.1 k.2 a3 a4 a8
  unfold carriedOf
  rw [ahead_of_laid h.scope h.laid hB]
  exact carried_O_written

/-- **`tiesOB` under the head, at whatever book the maker returns.** -/
theorem tiesO_head (h : P5J.AtMg o Z D r₀ Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk) :
    tiesOB Bk ⟨2, none, 10, .K12⟩ 2 = true := by
  have k := tiesO_written
  unfold tiesOB carryE at k ⊢
  rw [ahead_of_laid h.scope h.laid hB]
  exact k

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.tiesO_written
#print axioms ProofFile.Honest.K12.Light.carried_O_written
#print axioms ProofFile.Honest.K12.Light.omegaNumbers_head
#print axioms ProofFile.Honest.K12.Light.bookCutsOmega_of_numbers
#print axioms ProofFile.Honest.K12.Light.ahead_of_laid
#print axioms ProofFile.Honest.K12.Light.bookCutsOmega_head
#print axioms ProofFile.Honest.K12.Light.tiesO_head
