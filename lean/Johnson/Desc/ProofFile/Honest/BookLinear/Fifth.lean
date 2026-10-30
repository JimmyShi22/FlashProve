-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookLinear/Fifth.lean: WHERE AN ORDER OF PLACES HAS NO PLACE TWICE AND
THE TEST clause5P ACCEPTS A LIST OF ENTRIES AT IT, THE FIFTH TEST OF ProverCoinCounts.clauses
(Honest/Frame.lean: "an entry's spender does not stand behind its owner") ACCEPTS THAT LIST AT THAT
ORDER (clause5P_of). ONE DIRECTION ALONE: where clause5P rejects, nothing follows. GENERAL IN g, the
function that names a place's position: nothing is asked of it. One definition with code; one
statement with its proof; one closed fact on small lists. Written by the authors of the honest side
of the linear claim's shared rounds (K14), in the frame's folder, not by the frame's authors; Ahead,
Addr and the test are the frame's (Honest/Frame.lean); Place is the library's
(Johnson/Desc/Block.lean).

  clause5P g all l   the twin: at every entry: g names the position of the owner's place and of the
    spender's in the order (placedAt, Honest/BookLinear/Positions.lean), and the owner stands before
    the spender by g's numbers (beforeG, the same file)
  clause5P_of     **all.Nodup → clause5P g all l = true → the fifth test's Bool at all and l is
                  true**: THE CONCLUSION IS THE TEST's Bool AS IT STANDS IN ProverCoinCounts.clauses, with the
                  order and the list as letters: at all := orderOf F and l := B.ahead it is the
                  fifth premise of clauses_all_of_each (Honest/BookWordOf.lean), to the letter. By
                  findIdx_of_placed (for "contains") and before_of_placed

What it is for. The test as it stands walks the order four times at every entry and compares places
at each step; the twin walks to a position twice at every entry, without a comparison on the way,
and compares numbers. Nothing here says what either costs.

That the order of a description has no place twice: the frame's orderOf_nodup
(Honest/Law/Rule/Tests.lean), under its test placesOk: not called here: a premise.

Kin. The frame's ProverCoinCounts.behind (Honest/Law/Rule/Tests.lean): THE OTHER WAY ROUND: from "no test is
named as failing" to the fifth test's last clause at every entry. The fifth test's Bool stands,
beside Honest/Frame.lean, in Honest/BookWordOf.lean alone (as a premise); no law that concludes it
was found in the frame's files or this kind's.

Limits. WHERE g IS WRONG THE TWIN REJECTS A LIST THAT THE TEST ACCEPTS (the closed fact's last
clause). What g is to be at a description's order is not said. No book is named: that a book's
entries pass clause5P is shown nowhere here. The closed fact is an evaluation in Lean's kernel
(decide +kernel) at an order of three places. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookLinear.Positions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place)

/-- The fifth test's twin: at every entry g names the positions of the owner's place and of the
  spender's, and the owner stands before the spender by g's numbers. -/
def clause5P (g : Place → Nat) (all : List Place) (l : List Ahead) : Bool :=
  l.all fun a => placedAt g all a.owner.place && placedAt g all a.spender.place && beforeG g a.owner
    a.spender

/-- **TWIN → FIFTH**, general in g: where the order has no place twice and the twin accepts, the
  fifth test of `ProverCoinCounts.clauses` accepts. -/
theorem clause5P_of {g : Place → Nat} {all : List Place} {l : List Ahead} (hn : all.Nodup)
    (h : clause5P g all l = true) :
    (l.all fun a => all.contains a.owner.place && all.contains a.spender.place &&
      a.owner.before all a.spender) = true := by
  rw [List.all_eq_true]
  intro a ha
  have h' := List.all_eq_true.1 h a ha
  simp only [Bool.and_eq_true] at h' ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h'
  exact ⟨⟨(findIdx_of_placed hn h1).2, (findIdx_of_placed hn h2).2⟩,
    by rw [before_of_placed hn h1 h2]; exact h3⟩

/-! ## Small lists: what the twin must accept, and what it must reject -/

/-- At an order of three places, g the piece's number. Accepted: the spender's place behind the
  owner's; one place, the spender's part behind the owner's. Rejected: the spender's place in front;
  a spender's place that the order does not hold. And with g one off the twin rejects a list that
  the test accepts. -/
theorem clause5P_small :
    clause5P (fun p => p.piece) [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩]
      [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨⟨1, none, 0, .K1⟩, 1⟩, true⟩] = true ∧
    clause5P (fun p => p.piece) [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩]
      [⟨"x", ⟨⟨1, none, 1, .K2⟩, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨⟨1, none, 0, .K1⟩, 0⟩, true⟩] = false ∧
    clause5P (fun p => p.piece) [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩]
      [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨⟨1, none, 1, .K9⟩, 0⟩, true⟩] = false ∧
    clause5P (fun p => p.piece + 1) [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩]
      [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩] = false ∧
    ([⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩].all fun (a :
      Ahead) =>
      ([⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩] : List Place).contains
        a.owner.place &&
      ([⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩] : List Place).contains
        a.spender.place &&
      a.owner.before [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩] a.spender) = true :=
        by
  decide +kernel

end ProofFile.Honest

#print axioms ProofFile.Honest.clause5P_of
#print axioms ProofFile.Honest.clause5P_small
