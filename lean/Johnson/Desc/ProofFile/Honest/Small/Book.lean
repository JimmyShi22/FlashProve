-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/Book.lean proves, conditional on either of the two tests on the
book of Honest/Small/Field.lean at the part at o, that the list of the runs that p spends of the
part at o is empty, at every p. That is the one premise of the frame's own `fresh_of_nil`
(Honest/Law/ToyLaw.lean). It is not a theorem on a part or on a distribution.

  `spentBy_of_noneSpent`: from `noneSpent B o`: no entry that spends names the part at o as its
     owner
  `spentBy_of_lendsNone`: from `lendsNone B o`: no entry at all names it

So a caller that has evaluated such a test to true has the field `fresh` at its member by one call
of the frame's lemma: `fresh_of_nil _ (spentBy_of_noneSpent h p) _ _`. No theorem on `fresh` is
stated here: a caller calls the frame's own `fresh_of_nil`. The proof here is one call of the
frame's `spentBy_nil`.

The frame's terms that are used here (part, side, row, member, face, coin, run, book, fold and the
like): the head of Honest/Small/Field.lean. All names stand in the namespace ProofFile.Honest.Small: a
caller opens it.

Limits. Neither Bool follows from `ProverCoinCounts.clauses`: each is evaluated at the book. Nothing is claimed
on any property of the protocol: not soundness, completeness, binding, hiding or any other.
-/
import Johnson.Desc.ProofFile.Honest.Law.ToyLaw
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small

/-- Conditional on `noneSpent B o`: where no entry that spends names the part at o as its owner,
none spends of it. -/
theorem spentBy_of_noneSpent {B : ProverCoinCounts} {o : Addr} (h : noneSpent B o = true) (p : Addr) :
    B.spentBy o p = [] := by
  refine spentBy_nil B o p fun e he h1 ho _ => ?_
  have h2 := List.all_eq_true.1 h e he
  rw [h1, ho, beq_self_eq_true] at h2
  cases h2

/-- Conditional on `lendsNone B o`: the like where no entry at all names it. -/
theorem spentBy_of_lendsNone {B : ProverCoinCounts} {o : Addr} (h : lendsNone B o = true) (p : Addr) :
    B.spentBy o p = [] := spentBy_of_noneSpent (noneSpent_of_lendsNone h) p

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.spentBy_of_noneSpent
#print axioms ProofFile.Honest.Small.spentBy_of_lendsNone
