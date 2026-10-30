-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawAtTheBookAtHead.lean: IN SCOPE AND UNDER LaidAt, WHATEVER BOOK bookWhole
(Honest/BookWhole.lean) RETURNS AT THE PROOF FILE's IOP AS WRITTEN IN LEAN (F0T), AT THE LIBRARY's
WRITTEN SENDINGS AND THE MERGES THAT mergesByName GUESSES THERE, IS THE BOOK THAT IT RETURNS AT THE
WRITTEN DESCRIPTION WP: SO IT HAS THE FORM RawBookFacts (AtFullSide/K14/RawAtTheBook.lean): what the
parts at K11's, K13's and K6's places and the rows at K5's twelve places and K6's spend in it is
what is written. Statements with their proofs: calls alone.

  rawBook_same    in scope, under LaidAt: whatever bookWhole returns at F0T is what it returns at
                  WP: bookWhole_carried_guess (Honest/BookWholeAlike.lean) at planAlike_at_laid
                  (Honest/K14/WrittenAtHead.lean), and bookWhole is a function
  rawBook_at_laid, rawBook_at_head   **so whatever book bookWhole returns at F0T has the form**: in
                  scope under LaidAt; and under the hypothesis of the head's member (P5J.AtMgA)

Kin. bookWhole_returns_at_laid_of_written, bookWhole_returns_at_head_of_written
(Honest/K14/BookWholeAtHead.lean) have that a book is returned at F0T; that it is WP's is in their
proofs, not in their statements.
No option is raised. The file stands in this side library because its first import does.
What is assumed. Nothing.
What is not claimed. All that AtFullSide/K14/RawAtTheBook.lean does not claim. At F0T the sendings
are the written ones: that the public part's own lists are these is made_sends_at_files'
(Honest/K14/SharedSendsWritten.lean). Numbers and addresses: nothing on soundness, completeness or
hiding.
-/
import AtFullSide.K14.RawAtTheBook
import Johnson.Desc.ProofFile.Honest.K14.BookWholeAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open VerifiableInference.Desc (Chain)
open VerifierAndGoals (InScope)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open P5J (LaidAt F0T TS)
open ProofFile.Honest ProofFile.Honest.K14

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **In scope, under LaidAt: what bookWhole returns at F0T is what it returns at WP.** -/
theorem rawBook_same (scope : InScope Z = true) (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF)
    {B B' : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
                  (mergesByName WP.first.blocksInOrder) = .ok B)
    (hB' : bookWhole (F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (F0T o Zp Np cF).first.blocksInOrder) = .ok B') : B' = B :=
  Except.ok.inj (hB'.symm.trans (bookWhole_carried_guess (planAlike_at_laid scope L) hB))

/-- **IN SCOPE, UNDER LaidAt: WHATEVER BOOK bookWhole RETURNS AT F0T HAS THE FORM.** -/
theorem rawBook_at_laid (scope : InScope Z = true) (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF)
    {B' : ProverCoinCounts}
    (hB' : bookWhole (F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (F0T o Zp Np cF).first.blocksInOrder) = .ok B') : RawBookFacts B' := by
  obtain ⟨B, hB⟩ := bookWhole_returns_written
  rw [rawBook_same scope L hB hB']
  exact rawBook_facts hB

/-- **THE SAME UNDER THE HYPOTHESIS OF THE HEAD's MEMBER.** -/
theorem rawBook_at_head {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA o Z D r Zp Np cF x₀) {B' : ProverCoinCounts}
    (hB' : bookWhole (F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (F0T o Zp Np cF).first.blocksInOrder) = .ok B') : RawBookFacts B' :=
  rawBook_at_laid h.scope h.laid hB'

end AtFullSide.K14

#print axioms AtFullSide.K14.rawBook_same
#print axioms AtFullSide.K14.rawBook_at_laid
#print axioms AtFullSide.K14.rawBook_at_head
