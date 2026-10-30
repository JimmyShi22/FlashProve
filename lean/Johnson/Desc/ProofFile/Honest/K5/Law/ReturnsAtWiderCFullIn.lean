-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReturnsAtWiderCFullIn.lean: LAWS AT ONE WRITTEN FILLING; NO
THREAD STANDS IN EITHER. THE FRAME's MAKER onlineProverFromPublicFiles RETURNS AT `widerFillAtC fullIn o' S O`
(Honest/AtPureWiderK10.lean: `widerFillAt` with the closings of the segments, the kind K10, as an
eleventh list): UNDER THE LIBRARY's HEAD, ITS TEST protocolDataWellFormed AND ONE CLOSED SENTENCE ON THE WRITTEN
BOOK (hB). Two theorems; no definition.

  `makerAsks_widerC_fullIn`      h, hl, hB ⊢ what the maker asks, at `widerFillAtC fullIn o' S O`
  `atPure_returns_widerC_fullIn` h, hl, hB ⊢ there is an A that onlineProverFromPublicFiles returns at that filling, with
                                 A.Z = Zp, A.F the head's description, A.G the ground

How. `makerAsks_ownC_of_own` (ReturnsAtWiderC.lean) at the opening `h.laid.opened` and at the elder
filling's four (`makerAsks_wider_fullIn`, MakerAsksWiderFullIn.lean); the return is
`atPure_returns_fill` (ReturnsFill.lean) at that filling.

Limits. THEY NAME ONE WRITTEN FILLING. hB is a premise: neither this file nor a file beneath it
proves it. THAT THE MAKER RETURNS AT A FILLING IS NO WORD ON WHETHER ITS PROVER CAN PLAY: what it
asks of a filling forbids halves that stray, it asks for none. Nothing here says that `ready`
returns at that filling (it refuses where two sides stand at one place), that a closing's part plays
or is accepted, or at which tables it speaks. By its authors' own Limits
(Honest/AtPureWiderK10.lean): the first chain has no side at the proximity test (the kind K12) and
at K1's message "W"; the second chain has no side at all; `shared` is the empty list where its maker
returns an error. Where the library's first chain is not made the closings' list lays no side, in
silence: under the head, and wherever onlineProverFromPublicFiles returns, that arm is not met (`closeLotAt_of_open`,
`atPure_closings`, in that file). All limits of ReturnsAtWiderC.lean, MakerAsksWiderFullIn.lean and
ReturnsFill.lean hold. The head is a hypothesis, and so is the library's test.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsAtWiderC
import Johnson.Desc.ProofFile.Honest.K5.Law.MakerAsksWiderFullIn
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **WHAT THE MAKER ASKS, AT `widerFillAtC fullIn o' S O`.** CONDITIONAL: h, hl, hB. -/
theorem makerAsks_widerC_fullIn (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hB : ∃ B, bookWhole P2Law.ProofPlan.WP Johnson.G.proofSendsFull.1
      Johnson.G.proofSendsFull.2.1 Johnson.G.proofSendsFull.2.2
      (mergesByName P2Law.ProofPlan.WP.first.blocksInOrder) = .ok B)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∀ G, blankBy pureRoad.links Zp = some G →
      MakerAsks (widerFillAtC fullIn o' S O) Zp G (P5J.F0T OnBytes.secondHashFunction Zp Np cF) := by
  intro G hG
  obtain ⟨Bs, base, Op⟩ := h.laid.opened
  exact makerAsks_ownC_of_own () (LongLots.plain o' S O) fullIn o' S O Op
    (makerAsks_wider_fullIn h hl hB o' S O G hG)

/-- **onlineProverFromPublicFiles RETURNS AT `widerFillAtC fullIn o' S O`.** CONDITIONAL: h, hl, hB. -/
theorem atPure_returns_widerC_fullIn (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hB : ∃ B, bookWhole P2Law.ProofPlan.WP Johnson.G.proofSendsFull.1
      Johnson.G.proofSendsFull.2.1 Johnson.G.proofSendsFull.2.2
      (mergesByName P2Law.ProofPlan.WP.first.blocksInOrder) = .ok B)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAtC fullIn o' S O) = .ok A ∧ A.Z = Zp ∧
      A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧ blankBy pureRoad.links Zp = some A.G :=
  atPure_returns_fill h hl hB _ (makerAsks_widerC_fullIn h hl hB o' S O)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.makerAsks_widerC_fullIn
#print axioms ProofFile.Honest.K5.atPure_returns_widerC_fullIn
