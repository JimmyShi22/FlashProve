-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/LettersTwelve.lean: under the library's head, where onlineProverFromPublicFiles returns at any filling:
the lending of the last two chains' proximity tests at the book that onlineProverFromPublicFiles returns: owner, start
and count of what the tests on G_u and on G_omega carry, and of the seven entries at the last
chain's test; and the tests on the book that the laws on the two shared tests take.

  book_laid           the book at the letters of TiesAtLaid.lean and CutsAtLaid.lean
  he_at_filling       the premise he of coin_at_lendings and spOneCoin_of_book, at that book
  cutsU_at_filling    bookCutsU at that book
  cutsO_at_filling    bookCutsOmega at that book
  carried_at_filling  what the four parts of the two shared tests carry: owner, start, count
  seven_written, seven_counts_at_filling   the seven entries at the last chain's test, with counts
  no_base_coins       the two K1 members take no coin of the base field

By what. book_at_filling (LettersAtHead.lean); he_at_laid, bookCutsU_head, bookCutsOmega_at_laid,
carried_written (CutsAtLaid.lean, CutsAtHead.lean, CutsOmegaAtLaid.lean); sendNumbers_head;
omegaDue_head (StatedAtHeadW.lean); carryE_at_W.

Limits.
- General in the filling: the statements hold at the term's filling where onlineProverFromPublicFiles returns there.
- That the frame lends is a premise of the laws that read these entries.
- At the full size and the format's second hash function.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.LettersAtHead
import AtFullSide.K12.CutsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.K1 (parWF)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K12.Light (carriedOf bookCutsU bookCutsOmega sendNumbers_of sendNumbers_head)
open ProofFile.Honest.K14 (SendPub jobOmega sendPlace dueOf offsetOf)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open Johnson.Prover.Send (shapeAt)
open P5J (AtMgA TS)
open AtFullSide.K14 (rawCarriesWW)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- The book at the letters of the laws on the full size. -/
theorem book_laid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok A.B :=
  ProofFile.Honest.K14.bookWhole_same_at_laid (book_at_filling h hA) h.scope h.laid

/-- **The premise he, at the book that onlineProverFromPublicFiles returns.** -/
theorem he_at_filling (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ e ∈ A.B.ahead, e.spender = ⟨ProofFile.Honest.K14.place 8, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, 42853⟩ :=
  he_at_laid h.scope h.laid (book_laid h hA)

/-- **The public test on G_u's entries, at that book.** -/
theorem cutsU_at_filling (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    bookCutsU A.B ⟨VerifiableInference.Desc.K1.qAt Zp Np, 0⟩ (fourOf Np).U = true :=
  bookCutsU_head h.toAtMg (book_laid h hA)

/-- **The public test on G_omega's entries, at that book.** -/
theorem cutsO_at_filling (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (p : P12) (hp : p.place = placeO) :
    bookCutsOmega A.B ⟨VerifiableInference.Desc.K1.qAt Zp Np, 0⟩ p = true := by
  obtain ⟨-, -, a3, a4, -, -, -, a8⟩ := sendNumbers_of _ (sendNumbers_head h.toAtMg)
  have d0 : dueOf (jobOmega ⟨VerifiableInference.Desc.K1.qAt Zp Np, 0⟩).Q.codes
      (ProofFile.Honest.K12.Light.shapeAt (jobOmega ⟨VerifiableInference.Desc.K1.qAt Zp Np, 0⟩) 0)
      ((jobOmega ⟨VerifiableInference.Desc.K1.qAt Zp Np, 0⟩).sort 0) = 42853 :=
    beq_iff_eq.1 (omegaDue_head h.toAtMg 0)
  exact bookCutsOmega_at_laid h.scope h.laid (book_laid h hA) _ p hp rfl d0 a3 a4 a8

/-- **What the four parts of the two shared tests carry, at that book**: owner, start, count. -/
theorem carried_at_filling (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    (carriedOf A.B ⟨placeU, 0⟩).map (fun e => (e.owner, e.start, e.count)) =
      [(⟨sendPlace 2, 0⟩, ⟨0, 0⟩, ⟨0, 10808⟩), (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩)] ∧
    (carriedOf A.B ⟨placeU, 1⟩).map (fun e => (e.owner, e.start, e.count)) =
      [(⟨sendPlace 2, 0⟩, ⟨0, 0⟩, ⟨0, 10808⟩), (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩),
        (⟨sendPlace 2, 0⟩, ⟨0, 10808⟩, ⟨0, 167⟩)] ∧
    (carriedOf A.B ⟨placeO, 0⟩).map (fun e => (e.owner, e.start, e.count)) =
      [(⟨sendPlace 5, 0⟩, ⟨0, 0⟩, ⟨0, 42853⟩), (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩)] ∧
    (carriedOf A.B ⟨placeO, 1⟩).map (fun e => (e.owner, e.start, e.count)) =
      [(⟨sendPlace 5, 0⟩, ⟨0, 0⟩, ⟨0, 42853⟩), (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩),
        (⟨placeO, 0⟩, ⟨0, 0⟩, ⟨0, 161⟩)] :=
  ⟨carried_written h.scope h.laid (book_laid h hA) _ _ _ carried_U0_written,
    carried_U_at_laid h.scope h.laid (book_laid h hA),
    carried_written h.scope h.laid (book_laid h hA) _ _ _ carried_O0_written,
    carried_written h.scope h.laid (book_laid h hA) _ _ _ carried_O1_written⟩

set_option maxRecDepth 1000000 in
/-- **The seven written entries with their counts.** An evaluation in Lean's kernel. -/
theorem seven_written :
    (rawCarriesWW.filter fun e => e.spender == ⟨placeW, 0⟩).map
        (fun e => (e.owner, e.start, e.count)) =
      [(senderI, startI, rowIF.2.2), (senderW, startW 0, rowWF.2.2), (senderO, ⟨0, 0⟩, rowOF.2.2)] ∧
    (rawCarriesWW.filter fun e => e.spender == ⟨placeW, 1⟩).map
        (fun e => (e.owner, e.start, e.count)) =
      [(senderI, startI, rowIF.2.2), (senderW, startW 0, rowWF.2.2), (senderO, ⟨0, 0⟩, rowOF.2.2),
        (senderW, startW 1, K1.dueMsg parWF.codes (shapeAt parWF 1) (rideWF 1))] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The two K1 members take no coin of the base field**: the premise on the base field's coins at
the written rows is met for nothing. An evaluation in Lean's kernel. -/
theorem no_base_coins : rowIF.2.2.f = 0 ∧ rowWF.2.2.f = 0 := by
  decide +kernel

/-- **The seven entries at the last chain's test, at the book that onlineProverFromPublicFiles returns.** -/
theorem seven_counts_at_filling (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    (carryE A.B ⟨placeW, 0⟩).map (fun e => (e.owner, e.start, e.count)) =
      [(senderI, startI, rowIF.2.2), (senderW, startW 0, rowWF.2.2), (senderO, ⟨0, 0⟩, rowOF.2.2)] ∧
    (carryE A.B ⟨placeW, 1⟩).map (fun e => (e.owner, e.start, e.count)) =
      [(senderI, startI, rowIF.2.2), (senderW, startW 0, rowWF.2.2), (senderO, ⟨0, 0⟩, rowOF.2.2),
        (senderW, startW 1, K1.dueMsg parWF.codes (shapeAt parWF 1) (rideWF 1))] := by
  have hB := book_at_filling h hA
  rw [carryE_at_W hB (Or.inl rfl), carryE_at_W hB (Or.inr rfl)]
  exact seven_written

end AtFullSide.K12

#print axioms AtFullSide.K12.book_laid
#print axioms AtFullSide.K12.he_at_filling
#print axioms AtFullSide.K12.cutsU_at_filling
#print axioms AtFullSide.K12.cutsO_at_filling
#print axioms AtFullSide.K12.carried_at_filling
#print axioms AtFullSide.K12.seven_written
#print axioms AtFullSide.K12.no_base_coins
#print axioms AtFullSide.K12.seven_counts_at_filling
