-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/WholeAheadAtHead.lean: kind K14: the label of the linear claim's sub-protocols: under
the library's one hypothesis at the full size (P5J.AtMgA), at any earlier hash, WITH NO OTHER
PREMISE: **THE FRAME's MAKER bookWhole (Honest/BookWhole.lean) RETURNS A BOOK AT THE PROOF FILE's
IOP AS WRITTEN IN LEAN, AT THE LIBRARY's WRITTEN LISTS OF SENDINGS AND THE GUESSED MERGES, AND THAT
BOOK's ENTRIES ARE THE WRITTEN LIST rawAheadW** (AtFullSide/K14/RawAheadWritten.lean). One theorem;
no definition. Two calls.

What it is not. THAT bookWhole RETURNS SAYS THAT THE BOOK's ELEVEN OWN TESTS ACCEPT, AND NO MORE:
nothing on the frame's test over a list of owners (ownersClearBy), on carriesWhole, on a budget of
positions. The eleven read entries, rows, cuts and the description, not the parts' texts; the book
is made without a look at any filling. rawAheadW IS NOT SPELLED THROUGHOUT: two of its ten pieces
are their makers' terms (the head of AtFullSide/K14/BookWholeWritten.lean). THE ENTRIES ALONE ARE
NAMED: of the book's rows and cuts nothing is said here (the rows: rawBookRows_written,
AtFullSide/K14/RawBookRowsWritten.lean, at the raw book). BOTH SIDES STAND AT THE WRITTEN LISTS OF
SENDINGS: that the public part's own lists are these is another fact (bookWhole_same_at_made,
Honest/K14/BookForAtPure.lean). THAT THE FRAME's MAKER onlineProverFromPublicFiles RETURNS IS NOT SHOWN HERE; THAT B IS
THE BOOK BY WHICH ANY PLAY OF THE FRAME's PROVER GOES, OR THE BOOK A.B OF WHAT onlineProverFromPublicFiles YIELDS, IS NOT
SAID HERE. That the hypothesis has a member is not shown here. Which masked sumchecks are merges is
the frame's guess (mergesByName); switches, four tests and three sendings are found by their labels.
The return at the written description rests on evaluations in Lean's kernel at the library's written
values and at written lists of its authors'; it is carried to the description by the library's
relation PlanAlike. It holds of the makers' texts as they lie beneath this file: over the frame's
turned segmentCarries alone (Honest/BookCarry.lean as it lies beneath). In the side library. The
full size alone. All limits of the files named hold here. No property is claimed. Nothing on
soundness, completeness or hiding.
How. bookWhole_returns_written_ahead (AtFullSide/K14/BookWholeWritten.lean) and
bookWhole_same_at_head (Honest/K14/BookWholeAtHead.lean).
-/
import AtFullSide.K14.BookWholeWritten
import Johnson.Desc.ProofFile.Honest.K14.BookWholeAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open VerifiableInference.Desc (Chain)
open Johnson.G (proofSendsFull)
open P5J (F0T TS)
open ProofFile.Honest ProofFile.Honest.K14

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **Under the head: bookWhole returns a book at the description, at the written lists of
sendings, and its entries are the written list.** -/
theorem bookWhole_returns_at_head_ahead {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA o Z D r Zp Np cF x₀) :
    ∃ B, bookWhole (F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (F0T o Zp Np cF).first.blocksInOrder) = .ok B ∧ B.ahead = rawAheadW :=
  bookWhole_returns_written_ahead.elim fun B hB => ⟨B, bookWhole_same_at_head hB.1 h, hB.2⟩

end AtFullSide.K14

#print axioms AtFullSide.K14.bookWhole_returns_at_head_ahead
