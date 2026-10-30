-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BookWholeAtHead.lean: kind K14: the label of the linear claim's
sub-protocols: **WHATEVER BOOK THE FRAME's MAKER bookWhole (Honest/BookWhole.lean) RETURNS AT THE
LIBRARY's WRITTEN DESCRIPTION WP, THAT VERY BOOK IT RETURNS AT THE PROOF FILE's IOP AS WRITTEN IN
LEAN**, at the written lists of sendings and the guessed merges: for all public files Z that pass
the library's test InScope and every public part of which the library's LaidAt holds; and under the
library's one hypothesis at the full size. UNDER ONE PREMISE, hB (bookWhole RETURNS B AT WP): A
PREMISE: NOT SHOWN IN THIS FILE. Four statements with their proofs; no definition. Calls alone.

  bookWhole_same_at_laid   by bookWhole_carried_guess (Honest/BookWholeAlike.lean) at
                  planAlike_at_laid (Honest/K14/WrittenAtHead.lean): B is one letter in the premise
                  and in the conclusion
  bookWhole_same_at_head   the same under the library's head
  bookWhole_returns_at_laid_of_written, bookWhole_returns_at_head_of_written   the weaker forms:
                  "if there is a book at WP, there is one at the description"

What is assumed. hB. That some B meets it is shown by its authors (
bookWhole_returns_written, AtFullSide/K14/BookWholeWritten.lean): OVER THE FRAME's segmentCarries
ALONE; AT mergesByName, THE FRAME's GUESS; no Lake,
no ride of record, no independent checker yet. Neither file imports the other.
What is not claimed. That bookWhole returns at any description: four implications. BOTH SIDES STAND
AT THE WRITTEN LISTS OF SENDINGS: THAT THE PUBLIC PART's OWN LISTS (Zp.made.proof), OR THE LAST
THREE OF WHAT THE LIBRARY's LIST OF SENDINGS RETURNS, ARE THESE IS ANOTHER FACT, not had here: the
sealed sends_in_scope (Johnson/Goal/Numbers/MadeInScope.lean) with pins_of_laid
(Johnson/Goal/Skeleton/PinsOfLaid.lean); spent in Honest/K14/BookForAtPure.lean. That bookWhole
returns says that the book's eleven own tests accept, and no more: nothing on the frame's test over
a list of owners (ownersClearBy), on carriesWhole, on a budget of positions; the book is made
without a look at any filling. It holds of the makers' texts as they lie beneath this file. The full
size alone. Nothing on what is or is not hidden; no property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.BookWholeAlike
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)
open VerifierAndGoals (InScope)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open P5J (LaidAt F0T TS)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The book that bookWhole returns at the written description is the book that it returns at the
description**, in scope, under LaidAt. UNDER ONE PREMISE, hB, which this file does not show. -/
theorem bookWhole_same_at_laid {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B)
    (scope : InScope Z = true) (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    bookWhole (F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (F0T o Zp Np cF).first.blocksInOrder) = .ok B :=
  bookWhole_carried_guess (planAlike_at_laid scope L) hB

/-- The same under the library's head. UNDER ONE PREMISE, hB, which this file does not show. -/
theorem bookWhole_same_at_head {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B)
    {x₀ : VerifiableInference.Desc.First.Look.Place} (h : P5J.AtMgA o Z D r Zp Np cF x₀) :
    bookWhole (F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (F0T o Zp Np cF).first.blocksInOrder) = .ok B :=
  bookWhole_same_at_laid hB h.scope h.laid

/-- The weaker form: if bookWhole returns a book at the written description, it returns one at the
description. UNDER ONE PREMISE, hB, which this file does not show. -/
theorem bookWhole_returns_at_laid_of_written
    (hB : ∃ B, bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B)
    (scope : InScope Z = true) (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    ∃ B, bookWhole (F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (F0T o Zp Np cF).first.blocksInOrder) = .ok B :=
  hB.elim fun B h => ⟨B, bookWhole_same_at_laid h scope L⟩

/-- The weaker form under the library's head. UNDER ONE PREMISE, hB, which this file does not
show. -/
theorem bookWhole_returns_at_head_of_written
    (hB : ∃ B, bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B)
    {x₀ : VerifiableInference.Desc.First.Look.Place} (h : P5J.AtMgA o Z D r Zp Np cF x₀) :
    ∃ B, bookWhole (F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (F0T o Zp Np cF).first.blocksInOrder) = .ok B :=
  bookWhole_returns_at_laid_of_written hB h.scope h.laid

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.bookWhole_same_at_laid
#print axioms ProofFile.Honest.K14.bookWhole_same_at_head
#print axioms ProofFile.Honest.K14.bookWhole_returns_at_laid_of_written
#print axioms ProofFile.Honest.K14.bookWhole_returns_at_head_of_written
