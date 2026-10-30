-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/LendAtPure.lean: the kind "the code switch" (K2): ONE BOOK: under the library's head
the book that `onlineProverFromPublicFiles` returns is the book that `bookWhole` returns at the written sendings; so the
frame lends each switch of the plan its coins at the book of `onlineProverFromPublicFiles`: the premise hlend of
`widths_at_switch` (Honest/K2/Law/WidthsAtSwitch.lean), at the very book at which `coins_at_head`
(Honest/Thread/JoinAtHead.lean) pays hcoins. It lies in the side library because it imports files of
it. Two laws: joins of calls; no definition; nothing is evaluated here.

  `pure_book_written`   A.B is what bookWhole returns at F0T at the written sendings
  `lend_at_pure`    THE PREMISE hlend, at A.B

By, sealed: `atPure_book_at_head` (Honest/K14/AtPureBookAtHead.lean) · `sends_in_scope`
(Johnson/Goal/Numbers/MadeInScope.lean) · `pin1_atAll` (Johnson/Desc/K1/Law/PinsAtHead.lean); ours:
`own_hands_at_book` (AtFullSide/K2/OwnHandsAtTheBook.lean). Kin:
`bookWhole_same_at_made`, `book_for_atPure_of_written` (Honest/K14/BookForAtPure.lean): they join
the made and the written sendings without any A.

Limits. THE HEAD AND THE OPENING ARE HYPOTHESES, AND hA, THAT `onlineProverFromPublicFiles` YIELDS, IS THE HEAVY ONE:
THIS FILE SHOWS THEM MET BY NOTHING: WHERE NOTHING MEETS THEM THESE LAWS HOLD EMPTILY. It says that
a part is lent its coins, at every k: of what the coins are it says nothing. NOT IN FRONT OF A LAW
OVER COINS. The full size and the format's second hash function alone. Nothing on any property.
-/
import AtFullSide.K2.OwnHandsAtTheBook
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.K1.Law.PinsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (Block Chain)
open Johnson.G (proofSendsFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K2 (SwitchPlace switchPlaces handed)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)} {W₀ Rc Tr X₀ X : Type}
  {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **A.B is what bookWhole returns at F0T at the written sendings.** -/
theorem pure_book_written (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok A.B := by
  have e := ProofFile.Honest.K14.atPure_book_at_head h hA
  rw [VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub
    (VerifiableInference.Desc.K1.pin1_atAll h)] at e
  exact e

/-- **THE PREMISE hlend, AT THE BOOK OF `onlineProverFromPublicFiles`.** -/
theorem lend_at_pure (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ p' ∈ switchPlaces Zp Bs.G₀, ∀ k : Coins A.B,
      ∃ c₀, lendPart A.B (A.B.rowsOf 0) (k.look 0) ⟨p'.place, 0⟩
        (ProofFile.Honest.K2.switchPart (ProofFile.Honest.K2.coreSender ProofFile.Honest.K2.freshTable) p'.sizes
          p'.others p'.foldVars p'.carries) = .ok c₀ := by
  intro p' hp' k
  obtain ⟨g, pt, -, h2, -⟩ := own_hands_at_book h O (pure_book_written h hA) hp'
  obtain ⟨c, hc, -⟩ := h2 k
  unfold handed at hc
  cases e : lendPart A.B (A.B.rowsOf 0) (k.look 0) ⟨p'.place, 0⟩
    (ProofFile.Honest.K2.switchPart (ProofFile.Honest.K2.coreSender ProofFile.Honest.K2.freshTable) p'.sizes
      p'.others p'.foldVars p'.carries) with
  | error _ =>
    rw [e] at hc
    cases hc
  | ok v => exact ⟨v, rfl⟩

end AtFullSide.K2

#print axioms AtFullSide.K2.pure_book_written
#print axioms AtFullSide.K2.lend_at_pure
