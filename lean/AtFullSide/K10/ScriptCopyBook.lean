-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/ScriptCopyBook.lean: the book of whatever the maker returns, in the spelling in which the law on the joined script's messages at
the switches asks it (the premise hB of `msgs_at_lot_data`, AtFullSide/K2/MsgsAtLotData.lean): `bookWhole` at the hypothesis's own description, at the
WRITTEN three lists of sendings (`proofSendsFull`) and at the merges named off that description's own first chain. One statement.

  **`book_at_lot`**   under the library's hypothesis at Zp and where `onlineProverFromPublicFiles` returns A at the hypothesis's files:
                    `bookWhole (F0T secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2 (mergesByName (F0T secondHashFunction Zp Np cF).first.blocksInOrder) = .ok A.B`

By: `atPure_book_at_head` (Johnson/Desc/ProofFile/Honest/K14/AtPureBookAtHead.lean), which has it at the public part's own three lists and at the merges
named off cF's flat list; `sends_in_scope` (Johnson/Goal/Numbers/MadeInScope.lean): in the goals' scope these three lists are the written ones; the
description's first chain is cF by its make.

Limits. The hypothesis and the maker's return are premises: that `onlineProverFromPublicFiles` returns at any filling is not said. What the book holds is not said.
The full size and the older hash alone. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open Johnson.G (proofSendsFull)
open P5J (AtMgA TS)
open ProofFile.Honest

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place} {W₀ Rc Tr X₀ X : Type}

/-- **The maker's book, at the written lists of sendings and the description's own first chain.** -/
theorem book_at_lot (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok A.B := by
  have e := ProofFile.Honest.K14.atPure_book_at_head h hA
  rw [VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub
    (P5J.pins_of_laid h.scope h.laid).1] at e
  exact e

end AtFullSide.K10

#print axioms AtFullSide.K10.book_at_lot
