-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLBookClosingLetters.lean

It states no goal. No property of the protocol is claimed.

The body of the public test
`closingBookTest` (LOpensBook.lean) as a test on two lists of entries. At letters: no written value.

  `closingCarriedTest`      the body, of what is carried to the test's part (mine) and to the finish's (his)
  `closingBookTest_is`      `closingBookTest` is that body at the book's carrying entries (`carryE`)

A sister: `closingEntriesTest`, `closingBookTest_eq` (not beneath this file), the
same text: their file holds a closed line over the book's whole written list, so it is not imported here.

Limits. A definition and an unfolding. Nothing at any book. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LOpensBook
import Johnson.Desc.ProofFile.Honest.Law.Rule.Cell

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open ProofFile.Honest (carryE)

/-- **The body of `closingBookTest`**, of what is carried to the test's part (mine) and to the
finish's (his). -/
def closingCarriedTest (mine his : List Ahead) (p : K2.SwitchPlace) : Bool :=
  ((List.range p.front.length).all fun n =>
    match mine[n]?, his[n]? with
    | some x, some y => x.owner == y.owner && x.start == y.start && x.count == y.count
    | _, _ => false) &&
  (match mine[p.front.length]? with
    | some x => x.owner == ⟨p.place, 0⟩ && x.start == ⟨0, 0⟩ &&
        x.count == K2.messageDue p.sizes.codes (shapeL p) none
    | none => false) &&
  (match mine[p.front.length + 1]? with
    | some x => x.owner == ⟨p.place, 0⟩ &&
        x.start == K2.dueBefore p.sizes.codes (sentL p)
          (K2.switchFresh p.sizes p.others p.foldVars) 1 &&
        x.count == K2.messageDue p.sizes.codes (freshShapeL p) (some p.foldVars) &&
        decide (x.start.e + x.count.e ≤ (K2.sendingDue p.sizes.codes (sentL p)
          (K2.switchFresh p.sizes p.others p.foldVars)).e)
    | none => false)

/-- `closingBookTest` is that body at the book's carrying entries. -/
theorem closingBookTest_is (Bk : ProverCoinCounts) (p : K2.SwitchPlace) (a : Addr) :
    closingBookTest Bk p a = closingCarriedTest (carryE Bk a) (carryE Bk ⟨p.place, 0⟩) p := rfl

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.closingBookTest_is
