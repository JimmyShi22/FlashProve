-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/BookBridge.lean: the kind "the code switch" (K2): FROM THE WRITTEN BOOK's ENTRIES AND
THE WRITTEN ORDER TO THE BOOK AND THE ORDER UNDER THE LIBRARY's HEAD: the kind's test on the book
(`bookFits`, Johnson/Desc/ProofFile/Honest/K2/Fresh.lean) AT ONE OWNER, FOR EVERY ADDRESS, AT
WHATEVER BOOK bookWhole RETURNS AT F0T AND AT THAT DESCRIPTION's OWN ORDER OF PLACES, FROM THREE
PUBLIC FACTS ON WRITTEN VALUES: what the owner's entries are, as tuples, in the written list
`rawAheadW` · each spender's place stands where the written positions name it · the one test
`ownerOk` at these tuples and positions. NO LIST OF TUPLES IS NAMED HERE AND NOTHING IS EVALUATED.
It lies in the side library because it imports files of it. No definition; statements with their
proofs: calls.

  `ahead_at_head`   under the head: the book's entries are `rawAheadW`
  `order_at_head`   under the head: the description's order of places is the written description's
  `book_at_owner`   THE END: the field book of `FreshAsks`, in its own text, at an owner

By, sealed, of another group of authors: `rawAheadW`, `bookWhole_returns_written_ahead`,
`rawBook_same`, `posW`, `orderW_nodup` (AtFullSide/K14/RawAheadWritten.lean, BookWholeWritten.lean,
RawAtTheBookAtHead.lean, RawTwinKit.lean) · `planAlike_at_laid` (Honest/K14/WrittenAtHead.lean) ·
of the frame's authors: `orderOf_alike` (Honest/BookWholeAlike.lean) · `beforeG`, `placedAt`,
`before_of_placed` (Honest/BookLinear/Positions.lean). Ours: `book_of_ownerOk`
(Honest/K2/Law/BookByRuns.lean).

Limits. THE THREE FACTS ARE PREMISES: hL · hpl · hok: shown of no owner here. THE MERGES ARE
mergesByName's, which the frame's own text calls a guess. That a thread's book is what bookWhole
returns at F0T is not said. The full size and the format's second hash function alone. THE HEAD IS A
HYPOTHESIS: THIS FILE SHOWS IT MET BY NOTHING: WHERE NOTHING MEETS IT THESE LAWS HOLD EMPTILY. The
book's return, hB, is a premise here; under the head it is had (`bookWhole_returns_at_head_ahead`,
AtFullSide/K14/WholeAheadAtHead.lean: not imported). No coin occurs.
All limits of the files named stand. Nothing on any property.
-/
import AtFullSide.K14.RawTwinKit
import AtFullSide.K14.BookWholeWritten
import AtFullSide.K14.RawAtTheBookAtHead
import Johnson.Desc.ProofFile.Honest.BookWholeAlike
import Johnson.Desc.ProofFile.Honest.K2.Law.BookByRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (Chain)
open Johnson.G (proofSendsFull)
open P2Law.ProofPlan (WP)
open P5J (AtMgA F0T TS)
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K2 (bookFits)
open ProofFile.Honest.K2.Law (entryTuple ownerOk spendersIn book_of_ownerOk)
open AtFullSide.K14 (rawAheadW posW orderW_nodup bookWhole_returns_written_ahead rawBook_same)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {B : ProverCoinCounts}

/-- Under the head the book's entries are the written ones. -/
theorem ahead_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B) :
    B.ahead = rawAheadW := by
  obtain ⟨W, hW, e⟩ := bookWhole_returns_written_ahead
  rw [rawBook_same h.scope h.laid hW hB]
  exact e

/-- Under the head the description's order of places is the written description's. -/
theorem order_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    orderOf (F0T OnBytes.secondHashFunction Zp Np cF) = orderOf WP :=
  (orderOf_alike (planAlike_at_laid h.scope h.laid).first (planAlike_at_laid h.scope h.laid).shared
    (planAlike_at_laid h.scope h.laid).second).symm

/-- **THE FIELD book's OWN TEXT AT AN OWNER, UNDER THE HEAD, AT THE BOOK**, from three public facts
on written values. -/
theorem book_at_owner (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)}
    {o : Addr} {L : List (Addr × Due × Due × Bool)}
    (hL : (rawAheadW.filter fun e => e.owner == o).map entryTuple = L)
    (hpl : (L.all fun t => placedAt posW (orderOf WP) t.1.place) = true)
    (hok : ownerOk codes sent fresh (beforeG posW) L = true) :
    ∀ q : Addr, bookFits codes sent fresh (B.spentBy o q)
      (B.knownBy (orderOf (F0T OnBytes.secondHashFunction Zp Np cF)) o q) = true := by
  rw [order_at_head h]
  refine book_of_ownerOk (by rw [ahead_at_head h hB]; exact hL) ?_ hok
  intro t ht q hq
  have hq' : ∃ u ∈ L, u.1 = q := by
    unfold spendersIn at hq
    rw [List.mem_eraseDups] at hq
    obtain ⟨u, hu, e⟩ := List.mem_map.1 hq
    exact ⟨u, (List.mem_filter.1 hu).1, e⟩
  obtain ⟨u, hu, rfl⟩ := hq'
  exact before_of_placed orderW_nodup (List.all_eq_true.1 hpl t ht) (List.all_eq_true.1 hpl u hu)

end AtFullSide.K2

#print axioms AtFullSide.K2.ahead_at_head
#print axioms AtFullSide.K2.order_at_head
#print axioms AtFullSide.K2.book_at_owner
