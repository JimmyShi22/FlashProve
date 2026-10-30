-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/CutsAtHead.lean

Under the head, at whatever book the maker returns: a sentence on all entries of the book, a public
test with code on them, both at the shared chain's own plan, and the field coin of `LeftAt`
(Johnson/Desc/ProofFile/Honest/K12/OnFreeTAtHeadULeft.lean). Three theorems. In the side library,
because CutsAtLaid.lean is.

  `he_head`: the premise he of `coin_at_lendings`
      (Johnson/Desc/ProofFile/Honest/K12/CoinAtLendings.lean).
  `bookCutsU_head`: `bookCutsU` (…/K12/CutOfBookAt.lean) at the plan and the seated place.
  `coin_head`: the field coin.

By what. `he_at_laid`, `bookCutsU_at_laid` (CutsAtLaid.lean in this folder), which stand at eight
written numbers; `sendNumbers_head`, `sendNumbers_of` (…/K12/SendNumbersAtHead.lean), which have
these numbers at the plan under the head; the shared rounds' authors' `places4`
(…/Honest/K14/PaidAt.lean); `p12At_place` (…/K12/AtProof/Places.lean); `planFacts_head`
(…/K12/DoorReturnsAt.lean).

Limits. Those of CutsAtLaid.lean and SendNumbersAtHead.lean: the full size alone; the library's
written sendings and the merges that the maker reads off the first chain (hB); that the maker
returns a book is a premise (hB); under the library's stronger head the shared rounds' authors have
it as a conclusion (`bookWhole_returns_at_head_ahead`, AtFullSide/K14/WholeAheadAtHead.lean), which
is not called here. `coin_head` is of the kind that CoinAtLendings.lean's head names. It moves no
count. Nothing on completeness, on soundness or on what a view shows.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.CutsAtLaid
import Johnson.Desc.ProofFile.Honest.K12.SendNumbersAtHead
import Johnson.Desc.ProofFile.Honest.K12.CoinAtLendings
import Johnson.Desc.ProofFile.Honest.K14.PaidAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open OnBytes (E zeroE TableKey)
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc (K1.qAt)
open Desc.K14 (St blocks)
open Desc.K14.Honest (kappaOf)
open Johnson.G (proofSendsFull)
open ProofFile.Honest (ProverCoinCounts Addr Due Cs Common Part RowCoins lendRow coinsE Weights bookWhole
mergesByName)
open ProofFile.Honest.K14 (Ask jobOmega offsetOf sendPlace liftSend sendingPart Data liftK14 splitPart
  places4)
open ProofFile.Honest.K12.Light (bookCutsU heldAt sendNumbers_of sendNumbers_head coin_at_lendings
  planFacts_head)
open ProofFile.Honest.K12.AtProof (fourOf p12At_place)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- The premise he of `coin_at_lendings`, under the head, at whatever book the maker returns: at the
eighth sub-protocol's place, with the offset in the number's stead. -/
theorem he_head (h : P5J.AtMg o Z D r₀ Zp Np cF) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk) :
    ∀ e ∈ Bk.ahead, e.spender = ⟨b8.place, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, offsetOf (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.codes
        (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent (jobOmega ⟨K1.qAt Zp Np, 0⟩).sort 1⟩ := by
  have e3 := (sendNumbers_of _ (sendNumbers_head h)).2.2.1
  rw [(places4 _ b1 b2 b3 b4 b5 b6 b7 b8 hb).2.2.2, e3]
  exact he_at_laid h.scope h.laid hB

/-- **`bookCutsU` under the head, at whatever book the maker returns**: at the shared chain's own
plan and the seated place. -/
theorem bookCutsU_head (h : P5J.AtMg o Z D r₀ Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk) :
    bookCutsU Bk ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U = true := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := sendNumbers_of _ (sendNumbers_head h)
  exact bookCutsU_at_laid h.scope h.laid hB _ _ (p12At_place _ _) a1 a2 a3 a4 a5 a6 a7 a8

/-- **`LeftAt`'s field coin under the head, at whatever book the maker returns.** -/
theorem coin_head {W₀ Rc X₀ : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (A : Data) (wts : W₀ → Weights) (wit : Common W₀ Rc TableKey → Ask)
    {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {cS : RowCoins [(liftK14 A wts (splitPart A) : Part Empty (Common W₀ Rc TableKey) X₀)]}
    (lS : lendRow Bk rows look b8.place
      [(liftK14 A wts (splitPart A) : Part Empty (Common W₀ Rc TableKey) X₀)] 0 = .ok cS)
    {cO : RowCoins [(liftSend wit (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
      Part Empty (Common W₀ Rc TableKey) X₀)]}
    (lO : lendRow Bk rows look (sendPlace 5)
      [(liftSend wit (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)] 0 = .ok cO)
    (ask : Ask) (csU : Array E) :
    kappaOf (heldAt (K1.qAt Zp Np) ask csU (coinsE cO.1.1).toArray).cSp
        (K1.qAt Zp Np).par.S.sharedSplit.maskRows 0 =
      rdE.val ((coinsE cS.1.2.1.1).headD zeroE) := by
  obtain ⟨-, -, a3, -, -, -, -, a8⟩ := sendNumbers_of _ (sendNumbers_head h)
  obtain ⟨layO, hP⟩ := planFacts_head h
  have hsh := (VerifiableInference.Desc.Own.linFits_iff (K1.qAt Zp Np).codes
    (K1.qAt Zp Np).par.S).1 hP.lin
  have hSp : VerifiableInference.Desc.Own.SplitMessageFits (K1.qAt Zp Np).par.S.sharedSplit
      (K1.qAt Zp Np).par.S.sharedMaskCode := by
    rcases hsh.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with e | e
    · rw [hP.two] at e
      cases e
    · exact e
  exact coin_at_lendings (K1.qAt Zp Np) hSp.1 hSp.2.1 A wts wit lS lO
    (he_head h b1 b2 b3 b4 b5 b6 b7 b8 hb hB) (by rw [a3]; omega) ask csU

end AtFullSide.K12

#print axioms AtFullSide.K12.he_head
#print axioms AtFullSide.K12.bookCutsU_head
#print axioms AtFullSide.K12.coin_head
