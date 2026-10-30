-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/CBook.lean: conjunct 12 of the tests on the plan at WK: treeSharingOk: the eleven
clauses of BookPlan.allClausesHold (Johnson/Desc/BookPlan.lean), each alone, at the written declared rounds and
at what WK's blocks say of the roots. By evaluations in Lean's kernel; the clause inTime through its
eager twin (BeforeE.lean). Negative tests: with a second group told at the sampled tenant of the
first chain's second tree the clause oneGroup says no (so at that tree's sending the groups as told
reach the block's oracle messages and are read; the sendings of trees 0 and 5 go the same road and
are not bent); with the first four rounds struck (a gross bend), and with one opening's tree moved
to one that is sent later, the clause inTime says no. The other nine clauses' negative tests:
Johnson/HB/LLHARD/KB9/BookBent.lean (four) and Johnson/HB/LLHARD/KB9/BookBentD.lean (five).
Limits. At the closed description WK (WK.lean) and the written declared rounds alone. That a key
file's description passes the test at any public files is another file's, under named equations.
Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.WK
import Johnson.HB.LLHARD.KB4.BeforeE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.KB8 (declKeyFull)

set_option maxRecDepth 1000000 in
theorem book_sum : BookPlan.sum WK.roots = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem book_rows : BookPlan.rows WK.roots = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem book_told : BookPlan.everyOpenedTreeIsListed declKeyFull WK.roots = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem book_range : BookPlan.range declKeyFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem book_alike : BookPlan.alike declKeyFull WK.roots = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem book_oneGroup : BookPlan.oneGroup declKeyFull WK.roots = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem book_once : BookPlan.once declKeyFull WK.roots = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem book_answered : BookPlan.answered declKeyFull WK.roots = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem book_allTold : BookPlan.sentOraclesMatchEntries declKeyFull WK.roots = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem book_inOrder : BookPlan.inOrder declKeyFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem book_inTimeE : inTimeE declKeyFull WK.roots = true := by decide +kernel

theorem book_inTime : BookPlan.inTime declKeyFull WK.roots = true := by
  rw [inTime_eq]
  exact book_inTimeE

set_option maxRecDepth 1000000 in
theorem book_inTime_bent :
    inTimeE (declKeyFull.1.drop 4, declKeyFull.2.1, declKeyFull.2.2) WK.roots = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- One number moved: the first chain's round 18,812 opens its tree 5, which is sent in round
18,848, for its tree 1. -/
theorem book_inTime_own_bent : inTimeE
    (declKeyFull.1.zipIdx.map fun x =>
        if x.2 == 18812 then { x.1 with opens := [(⟨22, 12, false, 5⟩, .own 5)] } else x.1,
      declKeyFull.2.1, declKeyFull.2.2) WK.roots = false := by
  decide +kernel

/-- The tenants as told of the first chain, with a second group at the second tree's sampled
tenant. -/
def toldBent : List ProofFile.Root :=
  toldKeyFull.1.set 1 ⟨22, 77, [⟨2, 27, 1, true, [100, 101]⟩, ⟨0, 48, 1, false, []⟩]⟩

/-- The first chain at these. -/
def firstBent : Chain FirstState Claim :=
  firstChainL (lookLinks lookE oneFull Lk6.AtPlan.keyFull.set) oneFull declKeyFull.1 toldBent
    Johnson.KB8.rangesNumsFull

set_option maxRecDepth 1000000 in
theorem book_oneGroup_bent : BookPlan.oneGroup declKeyFull
    [oraclesOf firstBent.blocksInOrder, oraclesOf WK.shared.blocksInOrder, oraclesOf WK.second.blocksInOrder] = false := by
  decide +kernel

theorem WK_book : WK.treeSharingOk = true := by
  show BookPlan.allClausesHold WK.roundsDeclaredByBlocks WK.roots = true
  rw [WK_decl]
  unfold BookPlan.allClausesHold BookPlan.clauses
  simp only [List.all_cons, List.all_nil, book_sum, book_rows, book_told, book_range, book_alike,
    book_oneGroup, book_once, book_answered, book_allTold, book_inTime, book_inOrder,
    Bool.and_self]

end Johnson.KB4

#print axioms Johnson.KB4.book_sum
#print axioms Johnson.KB4.book_rows
#print axioms Johnson.KB4.book_told
#print axioms Johnson.KB4.book_range
#print axioms Johnson.KB4.book_alike
#print axioms Johnson.KB4.book_oneGroup
#print axioms Johnson.KB4.book_once
#print axioms Johnson.KB4.book_answered
#print axioms Johnson.KB4.book_allTold
#print axioms Johnson.KB4.book_inOrder
#print axioms Johnson.KB4.book_inTimeE
#print axioms Johnson.KB4.book_inTime
#print axioms Johnson.KB4.book_inTime_bent
#print axioms Johnson.KB4.book_inTime_own_bent
#print axioms Johnson.KB4.book_oneGroup_bent
#print axioms Johnson.KB4.WK_book
