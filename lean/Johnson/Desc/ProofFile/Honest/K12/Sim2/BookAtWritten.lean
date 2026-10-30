-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the public test on the sendings, evaluated, and what it gives at the maker's book.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/BookAtWritten.lean: sendsOffTests (BookAtTest.lean) at the
library's written description and written sendings, by Lean's kernel; carried to the description at
the head; so at every book that the frame's maker returns under the head, nothing is spent of a part
at a proximity test's place.

  sendsOffTests_alike, namesSought_alike   two alike lists give one test
  test_first_written, test_shared_written, test_last_written   the three tests, by Lean's kernel
  test_first_can_say_no   a tooth: the test refuses a proximity test's own sending
  noneSpent_at_maker   the test on the book at what onlineProverFromPublicFiles returns

The labels of the written sendings rest on one print (Johnson/G/SendsWritten.lean's head). No
property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.BookAtTest
import Johnson.Desc.ProofFile.Honest.BookAlike
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.K14.SharedSendsWritten
import AtFullSide.K14.RawSpentWritten
import Johnson.Unfolds.SplitOn
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain)
open ProofFile.Honest ProofFile.Honest.BookShared ProofFile.Honest.BookRow
open ProofFile.Honest.Small (noneSpent)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

theorem sendsOffTests_alike {S Cl S' Cl' : Type} {l : List (Block S Cl)} {l' : List (Block S' Cl')}
    (h : List.Forall₂ VerifiableInference.Desc.Alike₂ l l') (c : Johnson.G.ChainSends)
    (names : List String) : sendsOffTests l c names = sendsOffTests l' c names := by
  unfold sendsOffTests
  rw [seedRounds_alike h]
  simp only [addrOfRound_alike h]

theorem namesSought_alike {S Cl S' Cl' : Type} {l : List (Block S Cl)} {l' : List (Block S' Cl')}
    (h : List.Forall₂ VerifiableInference.Desc.Alike₂ l l') : namesSought l = namesSought l' := by
  have e : l.filterMap (·.place.link) = l'.filterMap (·.place.link) := by
    induction h with
    | nil => rfl
    | @cons b b' l l' hb _ ih =>
      simp only [List.filterMap_cons, hb.1, ih]
  unfold namesSought
  rw [e]

set_option maxRecDepth 1000000 in
/-- The first chain's, by Lean's kernel. -/
theorem test_first_written :
    sendsOffTests WP.first.blocksInOrder proofSendsFull.1 (namesSought WP.first.blocksInOrder) = true := by
  simp only [sendsOffTests, isSwitch, Johnson.Unfolds.splitOn_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The shared chain's, by Lean's kernel. -/
theorem test_shared_written : sendsOffTests WP.shared.blocksInOrder proofSendsFull.2.1 ["Omega"] = true := by
  simp only [sendsOffTests, isSwitch, Johnson.Unfolds.splitOn_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The last chain's, by Lean's kernel. -/
theorem test_last_written : sendsOffTests WP.second.blocksInOrder proofSendsFull.2.2 [] = true := by
  simp only [sendsOffTests, isSwitch, Johnson.Unfolds.splitOn_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can say no: with a proximity test's own sending among the labels that are looked up. -/
theorem test_first_can_say_no :
    sendsOffTests WP.first.blocksInOrder proofSendsFull.1
      ["the last group's test, the code switch of stage 1"] = false := by
  simp only [sendsOffTests, isSwitch, Johnson.Unfolds.splitOn_eq]
  decide +kernel

/-- **At every book that the frame's maker returns under the head, nothing is spent of a part at a
proximity test's place.** -/
theorem noneSpent_at_maker {W₀ Rc Tr X₀ X : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (o : Addr)
    (ho : o.place.kind = .K12) : noneSpent A.B o = true := by
  have hb := ProofFile.Honest.K14.atPure_book_at_head h hA
  have hs := ProofFile.Honest.K14.made_sends_at_files h.scope h.laid
  have al := ProofFile.Honest.K14.planAlike_at_laid h.scope h.laid
  rw [hs] at hb
  refine bookWhole_noneSpent hb ?_ ?_ ?_ o ho
  · rw [← sendsOffTests_alike al.first, ← namesSought_alike al.first]
    exact test_first_written
  · rw [← sendsOffTests_alike al.shared]
    exact test_shared_written
  · rw [← sendsOffTests_alike al.second]
    exact test_last_written

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.test_first_written
#print axioms ProofFile.Honest.K12.Sim2.test_shared_written
#print axioms ProofFile.Honest.K12.Sim2.test_last_written
#print axioms ProofFile.Honest.K12.Sim2.test_first_can_say_no
#print axioms ProofFile.Honest.K12.Sim2.noneSpent_at_maker
