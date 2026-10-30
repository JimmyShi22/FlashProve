-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
AtFullSide/K4/OwnersAtHead.lean: CONDITIONAL on the library's head h.

What is here. What the book's maker `ownerOf` returns at the head's own lists (cF.blocksInOrder, the public
part's first list of sendings, the seated description's second chain's rounds) is what it returns at
the written description WP and the written sendings; so, for the index masks' message and for each
link's mask row, it is the written value of AtFullSide/K14/RawFactsWritten.lean.
Called: `written_of_head` (Johnson/Road/K4/K4HeadWritten.lean), `planAlike_at_head`
(Honest/K14/WrittenAtHead.lean), `ownerOf_alike` (Honest/BookAlike.lean), `alike₂_rounds`
(Johnson/AtFull/ProofPlan/PlanAlike.lean), `rawIdx_written`, `rawRows_written`.
Not shown here. That h holds anywhere. Nothing on any sender's own start; nothing on coins.
Public data alone. No property is claimed.
-/
import AtFullSide.K14.RawFactsWritten
import Johnson.Desc.ProofFile.Honest.BookAlike
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.Road.K4.K4HeadWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K4
open ProofFile.Honest
open AtFullSide.K14 (rawIdxW rawIdx_written rawRowsW rawRows_written rawLater)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open VerifiableInference.Desc (Chain alike₂_rounds)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- The seated description's first chain is the chain that it was handed. No hypothesis. -/
theorem f0T_first_flat (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) : (P5J.F0T o Zp Np cF).first.blocksInOrder = cF.blocksInOrder := rfl

/-- CONDITIONAL on h. **THE MAKER's `ownerOf` AT THE HEAD's OWN LISTS IS `ownerOf` AT THE WRITTEN
ONES**, at every name, label and test. -/
theorem ownerOf_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) (name label : String)
    (pick : OnBytes.OracleNotice → Bool) :
    ownerOf name cF.blocksInOrder Zp.made.proof.1
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) label pick =
      ownerOf name WP.first.blocksInOrder proofSendsFull.1 rawLater label pick := by
  have A := ProofFile.Honest.K14.planAlike_at_head h
  have W := OnBytes.Road.K4.written_of_head h.toAtMg
  rw [W.proof, ← alike₂_rounds _ _ A.second, ← f0T_first_flat OnBytes.secondHashFunction Zp Np cF]
  exact (ownerOf_alike A.first name proofSendsFull.1 _ label pick).symm

/-- CONDITIONAL on h. **The index masks' message as an owner, at the head's own lists, is the
written value.** -/
theorem indexOwner_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    ownerOf indexMaskRun cF.blocksInOrder Zp.made.proof.1
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds))
        "link 0, moment 0" isIndexMaskMsg = some rawIdxW :=
  (ownerOf_at_head h _ _ _).trans rawIdx_written

/-- CONDITIONAL on h. **Each link's mask row as an owner, at the head's own lists, is the written
value.** -/
theorem rowOwner_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    ∀ x ∈ rawRowsW, ownerOf maskRowRun cF.blocksInOrder Zp.made.proof.1
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds))
        s!"link {x.1}, moment 0" isMaskRowMsg = some x.2 :=
  fun x hx => (ownerOf_at_head h _ _ _).trans (rawRows_written x hx)

end AtFullSide.K4

#print axioms AtFullSide.K4.f0T_first_flat
#print axioms AtFullSide.K4.ownerOf_at_head
#print axioms AtFullSide.K4.indexOwner_at_head
#print axioms AtFullSide.K4.rowOwner_at_head
