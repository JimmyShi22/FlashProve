-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookWholeAlikeGuess.lean: **AT TWO DESCRIPTIONS THAT ARE ALIKE (the
library's relation PlanAlike, Johnson/AtFull/ProofPlan/PlanAlike.lean) THE FRAME's MAKER bookWhole
(Honest/BookWhole.lean) GIVES ONE ANSWER, EACH AT THE MERGES THAT mergesByName READS OFF ITS OWN
FIRST CHAIN**: at all three lists of sendings; an equation of the two answers, errors too. ONE
PREMISE: PlanAlike W F. One theorem; no definition. Two calls.

What it is not. THAT bookWhole RETURNS A BOOK AT ANY DESCRIPTION IS NOT SAID: where it refuses at
one it refuses at the other, with the same word. That any two descriptions are alike is not said (at
the written description and the proof file's IOP as written in Lean: planAlike_at_laid,
planAlike_at_head, Honest/K14/WrittenAtHead.lean). What a returned book is worth is not said:
bookWhole's return gives the book's eleven own tests and no more. Which masked sumchecks are merges
is the frame's guess (mergesByName): that the guess is right is not said; that it is one at both
descriptions is mergesByName_alike. It holds of the makers' texts as they lie beneath this file. No
property is claimed. Nothing on soundness, completeness or hiding.
How. bookWhole_planAlike (Honest/BookWholeAlike.lean: the same at any merges, one letter on both
sides) and mergesByName_alike (Honest/BookAlikeRows.lean). bookWhole_carried_guess
(Honest/BookWholeAlike.lean) is the weaker form: "a book returned at the one is returned at the
other".
-/
import Johnson.Desc.ProofFile.Honest.BookWholeAlike
import Johnson.Desc.ProofFile.Honest.BookAlikeRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription PlanAlike)

/-- **At two descriptions that are alike bookWhole gives one answer, each at its own guessed
merges.** -/
theorem bookWhole_planAlike_guess {Xi Xi' : Type} {W : FileDescription Xi} {F : FileDescription Xi'}
    (h : PlanAlike W F) (p0 p1 p2 : Johnson.G.ChainSends) :
    bookWhole W p0 p1 p2 (mergesByName W.first.blocksInOrder) =
      bookWhole F p0 p1 p2 (mergesByName F.first.blocksInOrder) := by
  rw [mergesByName_alike h.first]
  exact bookWhole_planAlike h p0 p1 p2 _

end ProofFile.Honest

#print axioms ProofFile.Honest.bookWhole_planAlike_guess
