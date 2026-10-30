-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Book/EndTwoAtHead.lean: two facts on every reached last state of the first chain that
bears no mark, FROM THE ONE HEAD (`P5J.AtMg`, Johnson/P5J/AtMg.lean) at the concrete second hash
function: the book's places and shapes are the first of the listed ones (`K12.Door.seatsCarriedB L`)
· the statement's messages have the first of the listed shapes (`K12.Door.msgShapesB` at the chain
of sendings' own list). Three theorems. Joinings: each is one call through the head's opening.

  `hEnd_at_head`: both, at border 358: `IM.hEnd_paid` (Johnson/IMR/EndTwoPaid.lean).
  `hEnd_at_head_under`: the same behind any condition T on the public part (a caller's binder may
    bear one: it is not spent).
  `hMsg_at_head`: the second alone: `IM.shapesEnd_paid`: no list L is asked.
    OFF THE HEAD: the scope · the files' reading · an opening · the test on the list of rounds.
    WHAT STAYS, BY NAME:
      hB: `K12.Door.sendsAreB`, a test with code on the list of rounds, at every opening
      hL: the list of places and shapes can be laid at the first chain's codes: it names L
        (not in `hMsg_at_head`)

Limits. The premises that stay are shown nowhere here. Where hB is met by a lemma under a test on
written values, that test stands in front again. At `OnBytes.secondHashFunction` alone; in scope alone. That a
state is reached is not said. No example. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.IMR.EndTwoPaid
import Johnson.P5J.AtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Book
open OnBytes
open Johnson.Desc.First.Walk.Tied (Reach)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain First.S ProofFile.Cl}

/-- **The two facts at the first chain's reached end, from the one head.** -/
theorem hEnd_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hB : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A B →
      K12.Door.sendsAreB Zp.made.proof.1 358 (K12.Door.snAt Zp Bs.G₀ IM.placesW) = true)
    {L : K12.Door.Laid} (hL : K12.Door.laidAtCodes Zp.first.codes Zp.made.proof.1 = some L) :
    ∀ z s, Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) 358 (z, s) → s.failed = none →
      K12.Door.seatsCarriedB L s.book = true ∧
        K12.Door.msgShapesB (K12.Door.msgsOfChain Zp.made.proof.1) s.st = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact IM.hEnd_paid h.scope h.reads O h.laid.planOk (hB Bs base _ _ O) hL

/-- The same behind a condition on the public part, which is not spent. -/
theorem hEnd_at_head_under (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hB : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A B →
      K12.Door.sendsAreB Zp.made.proof.1 358 (K12.Door.snAt Zp Bs.G₀ IM.placesW) = true)
    {L : K12.Door.Laid} (hL : K12.Door.laidAtCodes Zp.first.codes Zp.made.proof.1 = some L)
    (T : ProofFile.InstPub → Prop) :
    ∀ z s, T z → Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) 358 (z, s) →
      s.failed = none → K12.Door.seatsCarriedB L s.book = true ∧
        K12.Door.msgShapesB (K12.Door.msgsOfChain Zp.made.proof.1) s.st = true :=
  fun z s _ => hEnd_at_head h hB hL z s

/-- **The messages' shapes alone.** -/
theorem hMsg_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hB : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A B →
      K12.Door.sendsAreB Zp.made.proof.1 358 (K12.Door.snAt Zp Bs.G₀ IM.placesW) = true) :
    ∀ z s, Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) 358 (z, s) → s.failed = none →
      K12.Door.msgShapesB (K12.Door.msgsOfChain Zp.made.proof.1) s.st = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact fun z s hr hu => IM.shapesEnd_paid h.scope h.reads O h.laid.planOk (hB Bs base _ _ O) hr hu

end VerifiableInference.Desc.Book

#print axioms VerifiableInference.Desc.Book.hEnd_at_head
#print axioms VerifiableInference.Desc.Book.hEnd_at_head_under
#print axioms VerifiableInference.Desc.Book.hMsg_at_head
