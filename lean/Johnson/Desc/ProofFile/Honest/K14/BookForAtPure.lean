-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BookForAtPure.lean: kind K14: the label of the linear claim's
sub-protocols: under the library's one hypothesis at the full size, at the earlier hash: **WHATEVER
BOOK B THE FRAME's MAKER bookWhole (Honest/BookWhole.lean) RETURNS AT THE LIBRARY's WRITTEN
DESCRIPTION WP, THAT VERY BOOK IT RETURNS AT THE PROOF FILE's IOP AS WRITTEN IN LEAN: WHEREVER THE
LIBRARY's LIST OF SENDINGS RETURNS SEVEN LISTS WHOSE FIFTH IS THE PUBLIC PART's FIRST, AT THE LAST
THREE OF THESE** (the call that the frame's maker onlineProverFromPublicFiles makes); **AND AT THE PUBLIC PART's OWN
THREE LISTS.** UNDER ONE PREMISE, hB (bookWhole RETURNS B AT WP, at the written lists of sendings
and the guessed merges): A PREMISE: NOT SHOWN IN THIS FILE. Three theorems; no definition. Calls
alone. A file of its own, so that whoever calls it need not stand on the side library: nothing of
AtFullSide/ lies beneath it.

  book_same_for_atPure   B is one letter in the premise and in the conclusion
  bookWhole_same_at_made   the same at Zp.made.proof's three lists
  book_for_atPure_of_written   the weaker form, "if there is a book at WP, there is one there": the
                  form in which a law on onlineProverFromPublicFiles can ask for the book

How. What the library's list of sendings returns at such files is the written lists (the step of
sends_written_at_files, Honest/K14/BookAtPure.lean, written out here at the four sealed laws that it
calls: sendsWhole_all, sends_tie, made_in_scope, pins_of_laid: so that file, and all that it stands
on, need not lie beneath); that the public part's own lists are the written ones: the sealed
sends_in_scope (Johnson/Goal/Numbers/MadeInScope.lean) at pins_of_laid
(Johnson/Goal/Skeleton/PinsOfLaid.lean); bookWhole_same_at_head (Honest/K14/BookWholeAtHead.lean).
What it is not. Three implications. That some B meets hB is shown in bookWhole_returns_written
(AtFullSide/K14/BookWholeWritten.lean): OVER THE FRAME's segmentCarries ALONE;
AT mergesByName, THE FRAME's GUESS; no Lake,
no ride of record, no independent checker yet. THAT onlineProverFromPublicFiles RETURNS IS NOT SHOWN, NOT EVEN UNDER hB:
it can refuse at other places too. That bookWhole returns says that the book's eleven own tests
accept, and no more: nothing on the frame's test over a list of owners (ownersClearBy), on
carriesWhole, on a budget of positions; the book is made without a look at any filling. Which masked
sumchecks are merges is the frame's guess (mergesByName). It holds of the makers' texts as they lie
beneath this file. The full size alone; at the earlier hash. No property is claimed. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.BookWholeAtHead
import Johnson.LPFE1R.RadiiAt
import Johnson.AtFull.Sends.SendsWhole
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open P5J (F0T TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **THE VERY BOOK, AT onlineProverFromPublicFiles's OWN CALL**: whatever book bookWhole returns at the written
description, that book it returns at the description and the last three of the seven lists that the
library's list of sendings returns: under the head, at the earlier hash. UNDER ONE PREMISE, hB,
which this file does not show. -/
theorem book_same_for_atPure {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B)
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    ∀ k0 k1 k2 e p1 p2, Johnson.G.sendsOf Z.pol Z.lay Z.KL =
        .ok [k0, k1, k2, e, Zp.made.proof.1, p1, p2] →
      bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 p1 p2
        (mergesByName cF.blocksInOrder) = .ok B := by
  intro k0 k1 k2 e p1 p2 hs
  obtain ⟨En, hEn⟩ := Johnson.AtFull.Sends.sendsWhole_all
  have h1 := VerifiableInference.Desc.LinkJoin.sends_tie h.laid.pub hs
  have h2 := hEn _ (VerifiableInference.PlanWritten.Joined.made_in_scope h.scope h.laid.pub
    (P5J.pins_of_laid h.scope h.laid).1)
  have hl := Except.ok.inj (h1.symm.trans h2)
  simp only [List.cons.injEq, and_true] at hl
  obtain ⟨-, -, -, -, e0, rfl, rfl⟩ := hl
  rw [e0]
  exact bookWhole_same_at_head hB h

/-- **The very book, at the public part's own three lists of sendings**: these are the written ones
(the sealed sends_in_scope at pins_of_laid). UNDER ONE PREMISE, hB, which this file does not
show. -/
theorem bookWhole_same_at_made {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B)
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
      Zp.made.proof.2.2 (mergesByName cF.blocksInOrder) = .ok B := by
  rw [VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub
    (P5J.pins_of_laid h.scope h.laid).1]
  exact bookWhole_same_at_head hB h

/-- **The book, in the form in which a law on onlineProverFromPublicFiles can ask for it**: the weaker form: "there is a
book": under the head, at the earlier hash. UNDER ONE PREMISE, hB, which this file does not show. -/
theorem book_for_atPure_of_written
    (hB : ∃ B, bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B)
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    ∀ k0 k1 k2 e p1 p2, Johnson.G.sendsOf Z.pol Z.lay Z.KL =
        .ok [k0, k1, k2, e, Zp.made.proof.1, p1, p2] →
      ∃ B, bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 p1 p2
        (mergesByName cF.blocksInOrder) = .ok B :=
  fun k0 k1 k2 e p1 p2 hs => hB.elim fun B hb => ⟨B, book_same_for_atPure hb h k0 k1 k2 e p1 p2 hs⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.book_same_for_atPure
#print axioms ProofFile.Honest.K14.bookWhole_same_at_made
#print axioms ProofFile.Honest.K14.book_for_atPure_of_written
