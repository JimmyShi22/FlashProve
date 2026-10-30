-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/LaysBookFacts.lean: the written book as a term, and that the maker's book is it.

  bookW            the written book: rows, entries and cuts, as terms
  book_is_written  the book that bookWhole returns at the written description is that book
  jobWB            W's job's public fields, as a job
  sendPart_two     W's sender's part has the cut's two moves

Limits. The full size alone. Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.HeldAtHeadW
import Johnson.Desc.ProofFile.Honest.K12.StepsReturnLast
import Johnson.Desc.ProofFile.Honest.BookWritten.Cuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Place)
open H2K.Member (piWFull)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open AtFullSide.K14 (rawAheadW rawSegW rawRowsFirstW rawRowsSharedW rawRowsSecondW
  rawBookRows_written rawWhole_is_raw bookWhole_returns_written_ahead)

/-- **The written book.** -/
def bookW : ProverCoinCounts :=
  ⟨rawRowsFirstW, rawRowsSharedW, rawRowsSecondW, rawAheadW,
    cutsFirstW ++ cutsSharedW ++ cutsSecondW⟩

set_option maxRecDepth 1000000 in
/-- **The maker's book is the written one.** -/
theorem book_is_written {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) : B = bookW := by
  obtain ⟨r1, r2, r3⟩ := rawBookRows_written _ B (rawWhole_is_raw hB)
  obtain ⟨B₀, h₀, he⟩ := bookWhole_returns_written_ahead
  obtain rfl : B = B₀ := Except.ok.inj (hB.symm.trans h₀)
  have hc : B.cuts = cutsOf WP := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc⟩ :=
      bookRaw_rows (rawWhole_is_raw hB)
    exact hc
  rw [cutsOf_written] at hc
  have e : B = ⟨B.first, B.shared, B.second, B.ahead, B.cuts⟩ := rfl
  rw [e, r1, r2, r3, he, hc]
  rfl

/-- **W's job's public fields.** -/
def jobWB : TestJob Unit Unit :=
  bareJob { piWFull with place := placeW } membersWF (some (senderW, 1))

/-- W's sender's part has the cut's two moves. -/
theorem sendPart_two {V W X : Type} (J : K1.SendJob W X) :
    (K1.sendPart J : Part V W X).moves.length = 2 := rfl

end AtFullSide.K12

#print axioms AtFullSide.K12.bookW
#print axioms AtFullSide.K12.book_is_written
#print axioms AtFullSide.K12.jobWB
#print axioms AtFullSide.K12.sendPart_two
