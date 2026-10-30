-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MakerAsksWiderFullIn.lean: A LAW AT ONE WRITTEN FILLING; NO
THREAD STANDS IN IT. WHAT THE FRAME's MAKER onlineProverFromPublicFiles ASKS OF A FILLING (`MakerAsks`, ReturnsOf.lean)
HOLDS OF `widerFillAt fullIn o' S O`: UNDER THE LIBRARY's HEAD, ITS TEST protocolDataWellFormed AND ONE CLOSED
SENTENCE ON THE WRITTEN BOOK (hB). One theorem; no definition.

  `makerAsks_wider_fullIn`  h, hl, hB ⊢ at the ground of the head's public part, `MakerAsks` at that
                            filling and the head's description

What it is for. It is the premise f of `atPure_returns_fill` (ReturnsFill.lean) at that filling: so
that premise can be met; and it is what a filling that lays more lists behind these ten hands on
(ReturnsAtWiderC.lean).

By: the return at that filling (`atPure_returns_fullIn_of_written`, ReturnsFromWritten.lean) opened
by `parts_of_atPure` (ReturnsOf.lean): that return comes by another road, lot by lot.

Limits. IT NAMES ONE WRITTEN FILLING. `MakerAsks` forbids halves that stray, it does not ask for
halves: AT THAT FILLING THE FIRST CHAIN OF THE PROVER THAT onlineProverFromPublicFiles RETURNS HAS NO HALF AT A PLACE
WHOSE KIND IS NONE OF ITS TEN LOTS', NOR AT A PLACE OF K1 BEHIND THE SEGMENTS (`first_none_all`,
`k1_none_behind_all`, Honest/Thread/FirstFillAll.lean). hB is a premise: neither this file nor a
file beneath it proves it. All limits of ReturnsFromWritten.lean hold. The head is a hypothesis, and
so is the library's test.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsFromWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE PREMISE f CAN BE MET**: at `widerFillAt fullIn o' S O`. Conditional: h, hl, hB. -/
theorem makerAsks_wider_fullIn (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hB : ∃ B, bookWhole P2Law.ProofPlan.WP Johnson.G.proofSendsFull.1
      Johnson.G.proofSendsFull.2.1 Johnson.G.proofSendsFull.2.2
      (mergesByName P2Law.ProofPlan.WP.first.blocksInOrder) = .ok B)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∀ G, blankBy pureRoad.links Zp = some G →
      MakerAsks (widerFillAt fullIn o' S O) Zp G (P5J.F0T OnBytes.secondHashFunction Zp Np cF) := by
  intro G hG
  obtain ⟨A, hA, eZ, eF⟩ := atPure_returns_fullIn_of_written h hl hB o' S O
  obtain ⟨m, a⟩ := parts_of_atPure hA
  have eG : A.G = G := by
    have g := m.ground
    rw [eZ, hG] at g
    exact (Option.some.inj g).symm
  rw [eZ, eG, eF] at a
  exact a

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.makerAsks_wider_fullIn
