-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/ReadsTestTie.lean: the number treesOf of ReadsTest.lean is the number treesTo
of BudProof.lean. So where the test readsWithinB accepts at treesOf of every split of the first
chain's list at the place a, the rule's clause on queried positions holds for the sender's row
(sendRow, "our row") at a (BudClause).
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file proves.
  treesTo_eq          treesTo F pre = treesOf F.first.blocksInOrder pre, by rfl.
  budClause_of_light  If readsWithinB F J.P (treesOf F.first.blocksInOrder pre) accepts for every way to
                      split F.first.blocksInOrder into pre, a sub-protocol at the place a, and a rest, then
                      BudClause F a J holds.

Limits. The test is evaluated at no description in this file. The lemmas are on numbers only: no
distribution and no coin is named.

How it fits. ReadsTest.lean defines the test and treesOf with few imports, so that a test program
can load them; the statements on the test (ReadsCountProof.lean) use treesTo. budClause_of_light is
budClause_of_test in the words of ReadsTest.lean. budAtLots (AtDescLots.lean) applies it to any list
of jobs; LotsTestTie.lean uses that at the jobs of the two lots.
-/
import Johnson.SendSim.Seat.ReadsCountProof

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc OnBytes.SendSim.At

/-- The number treesTo of BudProof.lean is treesOf of ReadsTest.lean at the first chain's list. -/
theorem treesTo_eq {Xi : Type} (F : FileDescription Xi) (pre : List (Block F.S₁ F.Cl)) :
    treesTo F pre = treesOf F.first.blocksInOrder pre := rfl

/-- If readsWithinB F J.P (treesOf F.first.blocksInOrder pre) accepts for every way to split the first
chain's list into pre, a sub-protocol at the place a and a rest, then BudClause F a J holds. -/
theorem budClause_of_light {Xi V W X Pb : Type} (F : FileDescription Xi) (a : Place) (J : SendJob W X)
    (h : ∀ pre b t, F.first.blocksInOrder = pre ++ b :: t → b.place = a →
      readsWithinB F J.P (treesOf F.first.blocksInOrder pre) = true) :
    BudClause (V := V) (Pb := Pb) F a J :=
  budClause_of_test F a J fun pre b t h1 h2 => by rw [treesTo_eq]; exact h pre b t h1 h2

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.treesTo_eq
#print axioms OnBytes.SendSim.Seat.budClause_of_light
