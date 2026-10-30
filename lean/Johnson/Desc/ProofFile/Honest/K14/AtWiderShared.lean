-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/AtWiderShared.lean: kind K14: THE FRAME's MAKER OF THE SHARED
CHAIN's HALVES AT A READER OF THE INDEX (nowSharedBy, Honest/AtPureWiderAt.lean), HELD AGAINST THE
TERM THAT THIS KIND's FILES WRITE OUT IN ITS PLACE; what it returns under the library's head; and
that none of its halves stands at a place that the shared chain does not have. Statements with their
proofs: an unfolding and two calls. No definition.

Why. Honest/K14/SendingsAtFilling.lean (sixBody_at_head) and Honest/K14/NoStrayMade.lean
(six_no_strays_made) speak of the two readers and sixOf in one written-out term, since the frame's
file, which stands over all kinds' halves, is not among their imports. Here it is.

  nowSharedBy_body   **nowSharedBy weights Z is that term**: by unfolding
  nowSharedBy_at_head   **under the library's head, at every reader of the index: nowSharedBy
                  returns the kind's own proverSidesOfSharedRounds with proverSidesOfSharedSendings at the plan qAt Zp Np and the number
                  0 of the round "LIN point"**: by sixBody_at_head
  wider_k14       **at the public part Z and the IOP F that pubPlain and onlineDescription return at three
                  files: no half of nowSharedBy's list stands at a place that F's shared chain does
                  not have** (strays, Honest/Frame.lean), at every reader: by six_no_strays_made.
                  Where nowSharedBy returns an error the list is empty and the statement says
                  nothing

What is not claimed. That a filling's field for the shared chain is nowSharedBy's list: that is the
fillings' own text (widerFillOwn, widerFillAt, AtPureWiderAt.lean): read, not stated here. The full
size alone in nowSharedBy_at_head. Nothing of a run. Nothing on any property.

Kin. wider_k14_light (Honest/K14/NoStrayLight.lean) has wider_k14's statement to the letter, over
few files: for a caller whose imports do not hold what stands beneath Honest/K14/NoStrayMade.lean.
-/
import Johnson.Desc.ProofFile.Honest.AtPureWiderAt
import Johnson.Desc.ProofFile.Honest.K14.SendingsAtFilling
import Johnson.Desc.ProofFile.Honest.K14.NoStrayMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain FileDescription)

variable {W₀ : Type}

/-- **The frame's maker of the shared chain's halves at a reader of the index is the two readers and
sixOf**, in the letters in which this kind's files write that term out. -/
theorem nowSharedBy_body (weights : W₀ → Weights) (Z : Pub) :
    nowSharedBy weights Z =
      (due? "the shared chain's own parameters" (p14At Z)).bind fun P =>
        (due? "the shared chain's place in the description" (onlineSharedChain Z)).bind fun s =>
          sixOf P s.chain.blocksInOrder weights fun rc : IndexCommitterCoins => ⟨(rc P.item).pad, (rc P.item).tail⟩ :=
  rfl

/-- **Under the library's head: what nowSharedBy returns**, at every reader of the index. -/
theorem nowSharedBy_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place} {o : ProofFile.SecondHashFunctionArgument}
    (h : P5J.AtMgA o Z D r Zp Np cF x₀) (weights : W₀ → Weights) :
    nowSharedBy weights Zp =
      .ok (proverSidesOfSharedRounds { S := (qAt Zp Np).S, atPoint := 0, atZeta := 6 } weights ++
        proverSidesOfSharedSendings { P := qAt Zp Np, atPoint := 0 } weights (randNow (qAt Zp Np))) :=
  (nowSharedBy_body weights Zp).trans (sixBody_at_head h weights)

/-- **No half of nowSharedBy's list stands at a place that the shared chain does not have**, at what
pubPlain and onlineDescription return at three files, at every reader of the index. -/
theorem wider_k14 {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub} {F : FileDescription Inst}
    (hZ : pubPlain o pol lay KL = .ok Z) (hF : onlineDescription o pol lay KL = .ok F)
    (weights : W₀ → Weights) :
    strays F.shared.blocksInOrder ((nowSharedBy weights Z).toOption.getD []) = [] :=
  six_no_strays_made hZ hF weights

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.nowSharedBy_body
#print axioms ProofFile.Honest.K14.nowSharedBy_at_head
#print axioms ProofFile.Honest.K14.wider_k14
